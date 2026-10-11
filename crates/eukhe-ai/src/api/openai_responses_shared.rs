//! Request conversion and stream processing shared by the `OpenAI` Responses
//! APIs (`openai-responses`, `azure-openai-responses`,
//! `openai-codex-responses`). Port of `api/openai-responses-shared.ts`.
//!
//! Input items and tools are the exact wire objects as [`JsonValue`]s.

mod stream;

use eukhe_types::pi_ai::TextSignaturePhase;
use serde_json::json;

use super::cache_breakpoints::has_cache_breakpoint;
use super::constrained_sampling::{
    get_grammar_tool_input, get_json_schema_tool_parameters, resolve_grammar_constrained_sampling,
    resolve_json_schema_strict_sampling, StrictToolParameters,
};
use super::transform_messages::transform_messages;
use crate::types::{
    AssistantContentBlock, AssistantMessage, IndexMap, JsonObject, JsonValue, Message, Modality,
    Model, ModelCompat, SystemMessage, Tool, TranscriptContext, UserContent, UserContentBlock,
};
use crate::utils::diagnostics::{ErrorObject, Thrown};
use crate::utils::hash::short_hash;
use crate::utils::js::{json_stringify, utf16_len};
use crate::utils::json_parse::json_parse;
use crate::utils::sanitize_unicode::sanitize_surrogates;
use crate::utils::text::{get_system_message_text, render_system_message_update};
use crate::utils::transcript::{resolve_transcript, resolve_transcript_tools};

pub use stream::{
    process_responses_stream, ApplyServiceTierPricingFn, OpenAIResponsesStreamOptions,
    ResolveServiceTierFn,
};

/// Tool name → the argument property that carries a grammar tool's raw input.
pub type GrammarToolInputProperties = IndexMap<String, String>;

struct ParsedTextSignature {
    id: String,
    phase: Option<TextSignaturePhase>,
}

fn parse_text_signature(signature: Option<&str>) -> Option<ParsedTextSignature> {
    let signature = signature.filter(|signature| !signature.is_empty())?;
    if signature.starts_with('{') {
        if let Ok(JsonValue::Object(parsed)) = json_parse(signature) {
            if parsed.get("v").and_then(JsonValue::as_f64) == Some(1.0) {
                if let Some(JsonValue::String(id)) = parsed.get("id") {
                    let phase = match parsed.get("phase").and_then(JsonValue::as_str) {
                        Some("commentary") => Some(TextSignaturePhase::Commentary),
                        Some("final_answer") => Some(TextSignaturePhase::FinalAnswer),
                        _ => None,
                    };
                    return Some(ParsedTextSignature {
                        id: id.clone(),
                        phase,
                    });
                }
            }
        }
        // Fall through to legacy plain-string handling.
    }
    Some(ParsedTextSignature {
        id: signature.to_owned(),
        phase: None,
    })
}

fn convert_tool_result_output(model: &Model, content: &[UserContentBlock]) -> JsonValue {
    let text_result = content
        .iter()
        .filter_map(|block| match block {
            UserContentBlock::Text(text) => Some(text.text.as_str()),
            UserContentBlock::Image(_) => None,
        })
        .collect::<Vec<_>>()
        .join("\n");
    let images: Vec<_> = content
        .iter()
        .filter_map(|block| match block {
            UserContentBlock::Image(image) => Some(image),
            UserContentBlock::Text(_) => None,
        })
        .collect();
    let has_text = !text_result.is_empty();

    if images.is_empty() || !model.input.contains(&Modality::Image) {
        let text = if has_text {
            text_result.as_str()
        } else if images.is_empty() {
            "(no tool output)"
        } else {
            "(see attached image)"
        };
        return JsonValue::String(sanitize_surrogates(text).into_owned());
    }

    let mut output = Vec::new();
    if has_text {
        output.push(json!({ "type": "input_text", "text": sanitize_surrogates(&text_result) }));
    }
    for image in images {
        output.push(json!({
            "type": "input_image",
            "detail": "auto",
            "image_url": format!("data:{};base64,{}", image.mime_type, image.data),
        }));
    }
    JsonValue::Array(output)
}

/// TS `ConvertResponsesMessagesOptions`.
#[derive(Debug, Clone, Default)]
pub struct ConvertResponsesMessagesOptions {
    /// Default: true.
    pub include_system_prompt: Option<bool>,
    pub grammar_tool_input_properties: Option<GrammarToolInputProperties>,
    /// Whether later system messages are sent in place; otherwise they are
    /// folded into the leading prompt.
    pub supports_mid_convo_system_messages: Option<bool>,
    pub supports_additional_tools: Option<bool>,
    pub supports_tool_search: Option<bool>,
    pub tool_options: Option<ConvertResponsesToolsOptions>,
    /// eukhe addition: whether marked user text blocks
    /// ([`TextContent::cache_breakpoint`](eukhe_types::pi_ai::TextContent))
    /// carry `prompt_cache_breakpoint: {"mode": "explicit"}` on the models
    /// with explicit prompt-cache controls
    /// ([`supports_explicit_cache_breakpoints`]). The API decides: not every
    /// Responses backend is known to accept the field.
    pub explicit_cache_breakpoints: bool,
}

/// TS `ConvertResponsesToolsOptions`.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ConvertResponsesToolsOptions {
    /// TS `strict?: boolean | null`: `None` is undefined, `Some(None)` null.
    pub strict: Option<Option<bool>>,
    /// Default: true.
    pub supports_strict_mode: Option<bool>,
    /// Default: false.
    pub supports_openai_grammar_tools: Option<bool>,
    pub tool_search_result: Option<bool>,
}

/// eukhe addition: whether an `OpenAI` Responses model id has the explicit
/// prompt-cache controls: GPT-5.6 and every later GPT-5 minor version
/// (`gpt-5.6`, `gpt-5.6-sol`, ...) and every GPT-6 model (`gpt-6-astra`,
/// `gpt-6.1-sol`, ...). These models accept `prompt_cache_breakpoint:
/// {"mode": "explicit"}` on `input_text` items and `reasoning.context:
/// "all_turns"`; the requests of every other model carry neither field.
#[must_use]
pub fn supports_explicit_cache_breakpoints(model_id: &str) -> bool {
    if let Some(rest) = model_id.strip_prefix("gpt-6") {
        return rest.is_empty() || rest.starts_with(['-', '.']);
    }
    let Some(rest) = model_id.strip_prefix("gpt-5.") else {
        return false;
    };
    let minor_end = rest
        .find(|c: char| !c.is_ascii_digit())
        .unwrap_or(rest.len());
    let (minor, suffix) = rest.split_at(minor_end);
    (suffix.is_empty() || suffix.starts_with('-'))
        && minor.parse::<u32>().is_ok_and(|minor| minor >= 6)
}

/// eukhe addition: pin `reasoning.context: "all_turns"` in the request's
/// reasoning object, when it sends one, on the models with explicit
/// prompt-cache controls: the reasoning of earlier turns stays in the
/// prompt, so a user message sent mid-run keeps the cached prefix (with
/// `current_turn` it drops the earlier reasoning and the cache misses).
/// Other models' requests stay unchanged.
pub fn apply_reasoning_context(model: &Model, params: &mut JsonObject) {
    if !supports_explicit_cache_breakpoints(&model.id) {
        return;
    }
    if let Some(JsonValue::Object(reasoning)) = params.get_mut("reasoning") {
        reasoning.insert("context".to_owned(), json!("all_turns"));
    }
}

/// `part.replace(/[^a-zA-Z0-9_-]/g, "_")`, cut to 64 UTF-16 units, trailing
/// underscores removed.
fn normalize_id_part(part: &str) -> String {
    let mut sanitized = String::new();
    for c in part.chars() {
        if c.is_ascii_alphanumeric() || c == '_' || c == '-' {
            sanitized.push(c);
        } else {
            // Each UTF-16 code unit of a non-matching char becomes one `_`.
            for _ in 0..c.len_utf16() {
                sanitized.push('_');
            }
        }
    }
    // Every char is ASCII now: byte length equals UTF-16 length.
    sanitized.truncate(64);
    sanitized.trim_end_matches('_').to_owned()
}

fn build_foreign_responses_item_id(item_id: &str) -> String {
    // `fc_` plus a short hash is ASCII and well under 64 characters.
    format!("fc_{}", short_hash(item_id))
}

fn compat_supports_developer_role(model: &Model) -> Option<bool> {
    match model.compat.as_ref()? {
        ModelCompat::OpenAIResponses(compat) => compat.supports_developer_role,
        ModelCompat::OpenAICompletions(compat) => compat.supports_developer_role,
        ModelCompat::Other(value) => value
            .get("supportsDeveloperRole")
            .and_then(JsonValue::as_bool),
        ModelCompat::AnthropicMessages(_)
        | ModelCompat::Bedrock(_)
        | ModelCompat::MistralConversations(_) => None,
    }
}

/// Split `id` at the first two `|` pieces like JS `id.split("|")`
/// destructured into `[callId, itemId]`.
fn split_tool_call_id(id: &str) -> (&str, Option<&str>) {
    let mut pieces = id.split('|');
    let call_id = pieces.next().unwrap_or_default();
    (call_id, pieces.next())
}

/// TS `convertResponsesMessages`.
///
/// # Errors
///
/// What TS throws: a corrupt reasoning signature (`JSON.parse`), invalid
/// constrained-sampling tool definitions.
#[allow(clippy::too_many_lines)] // One TS function; split would scatter its shared state.
pub fn convert_responses_messages(
    model: &Model,
    context: &TranscriptContext,
    allowed_tool_call_providers: &[&str],
    options: &ConvertResponsesMessagesOptions,
) -> Result<Vec<JsonValue>, Thrown> {
    let normalized_context =
        resolve_transcript(context.clone(), options.supports_mid_convo_system_messages);
    let mut messages: Vec<JsonValue> = Vec::new();

    let provider_allowed = allowed_tool_call_providers.contains(&model.provider.as_str());
    let normalize_tool_call_id = |id: &str, _target: &Model, source: &AssistantMessage| -> String {
        if !provider_allowed || !id.contains('|') {
            return normalize_id_part(id);
        }
        let (call_id, item_id) = split_tool_call_id(id);
        let item_id = item_id.unwrap_or_default();
        let normalized_call_id = normalize_id_part(call_id);
        let is_foreign_tool_call = source.provider != model.provider || source.api != model.api;
        let mut normalized_item_id = if is_foreign_tool_call {
            build_foreign_responses_item_id(item_id)
        } else {
            normalize_id_part(item_id)
        };
        // OpenAI Responses API requires item id to start with "fc"
        if !normalized_item_id.starts_with("fc_") {
            normalized_item_id = normalize_id_part(&format!("fc_{normalized_item_id}"));
        }
        format!("{normalized_call_id}|{normalized_item_id}")
    };

    let transformed_messages = transform_messages(
        normalized_context.messages(),
        model,
        Some(&normalize_tool_call_id),
    );
    let supports_additional_tools = options.supports_additional_tools.unwrap_or(false);
    let supports_tool_search = options.supports_tool_search.unwrap_or(false);
    let transcript_tools = resolve_transcript_tools(
        normalized_context.messages(),
        supports_additional_tools || supports_tool_search,
    );
    let tool_options = options.tool_options.unwrap_or_default();
    let append_system_tool_additions = |messages: &mut Vec<JsonValue>,
                                        message: &SystemMessage,
                                        seed: &str|
     -> Result<(), Thrown> {
        let tools: &[Tool] = if transcript_tools.anchors_additions {
            message.tools_added.as_deref().unwrap_or_default()
        } else {
            &[]
        };
        if tools.is_empty() {
            return Ok(());
        }
        if supports_additional_tools {
            messages.push(json!({
                "type": "additional_tools",
                "role": "developer",
                "tools": convert_responses_tools(tools, &tool_options)?,
            }));
            return Ok(());
        }
        if !supports_tool_search {
            return Ok(());
        }
        let names: Vec<&str> = tools.iter().map(|tool| tool.name.as_str()).collect();
        let call_id = format!(
            "pi_tool_load_{}",
            short_hash(&format!("{seed}:{}", names.join(",")))
        );
        messages.push(json!({
            "type": "tool_search_call",
            "call_id": call_id,
            "execution": "client",
            "status": "completed",
            "arguments": { "query": names.join(" "), "limit": names.len() },
        }));
        messages.push(json!({
            "type": "tool_search_output",
            "call_id": call_id,
            "execution": "client",
            "status": "completed",
            "tools": convert_responses_tools(
                tools,
                &ConvertResponsesToolsOptions {
                    tool_search_result: Some(true),
                    ..tool_options
                },
            )?,
        }));
        Ok(())
    };
    let include_initial_system_message = options.include_system_prompt.unwrap_or(true);
    let instruction_role =
        if model.reasoning && compat_supports_developer_role(model) != Some(false) {
            "developer"
        } else {
            "system"
        };
    let explicit_breakpoints =
        options.explicit_cache_breakpoints && supports_explicit_cache_breakpoints(&model.id);
    let grammar = options.grammar_tool_input_properties.as_ref();

    let mut msg_index: usize = 0;
    for (source_index, msg) in transformed_messages.iter().enumerate() {
        let is_leading_system_message = source_index == 0 && matches!(msg, Message::System(_));
        match msg {
            Message::System(system) => {
                if !is_leading_system_message {
                    append_system_tool_additions(
                        &mut messages,
                        system,
                        &format!("system:{msg_index}"),
                    )?;
                }
                if !is_leading_system_message || include_initial_system_message {
                    let text = if is_leading_system_message {
                        get_system_message_text(system)
                    } else {
                        render_system_message_update(system)
                    };
                    if !text.is_empty() {
                        messages.push(json!({
                            "role": instruction_role,
                            "content": sanitize_surrogates(&text),
                        }));
                    }
                }
            }
            Message::User(user) => match &user.content {
                UserContent::Text(text) => messages.push(json!({
                    "role": "user",
                    "content": [{ "type": "input_text", "text": sanitize_surrogates(text) }],
                })),
                UserContent::Blocks(blocks) => {
                    let input_items: Vec<JsonValue> = blocks
                        .iter()
                        .map(|item| {
                            let mut content_item = match item {
                                UserContentBlock::Text(text) => json!({
                                    "type": "input_text",
                                    "text": sanitize_surrogates(&text.text),
                                }),
                                UserContentBlock::Image(image) => json!({
                                    "type": "input_image",
                                    "detail": "auto",
                                    "image_url": format!("data:{};base64,{}", image.mime_type, image.data),
                                }),
                            };
                            // eukhe addition: a marked block ends a cacheable prefix.
                            if explicit_breakpoints && has_cache_breakpoint(item) {
                                if let JsonValue::Object(object) = &mut content_item {
                                    object.insert(
                                        "prompt_cache_breakpoint".to_owned(),
                                        json!({ "mode": "explicit" }),
                                    );
                                }
                            }
                            content_item
                        })
                        .collect();
                    if input_items.is_empty() {
                        continue;
                    }
                    messages.push(json!({ "role": "user", "content": input_items }));
                }
            },
            Message::Assistant(assistant) => {
                let output = convert_assistant_message(model, assistant, msg_index, grammar)?;
                if output.is_empty() {
                    continue;
                }
                messages.extend(output);
            }
            Message::ToolResult(result) => {
                let (call_id, _) = split_tool_call_id(&result.tool_call_id);
                let output = convert_tool_result_output(model, &result.content);
                let kind = if grammar.is_some_and(|grammar| grammar.contains_key(&result.tool_name))
                {
                    "custom_tool_call_output"
                } else {
                    "function_call_output"
                };
                messages.push(json!({ "type": kind, "call_id": call_id, "output": output }));
            }
        }
        if !is_leading_system_message {
            msg_index += 1;
        }
    }

    Ok(messages)
}

fn convert_assistant_message(
    model: &Model,
    assistant: &AssistantMessage,
    msg_index: usize,
    grammar: Option<&GrammarToolInputProperties>,
) -> Result<Vec<JsonValue>, Thrown> {
    let mut output: Vec<JsonValue> = Vec::new();
    let is_same_provider_and_api =
        assistant.provider == model.provider && assistant.api == model.api;
    let is_same_model = is_same_provider_and_api && assistant.model == model.id;
    let is_different_model = is_same_provider_and_api && assistant.model != model.id;
    let mut text_block_index: usize = 0;

    for block in &assistant.content {
        match block {
            AssistantContentBlock::Thinking(thinking) => {
                if let Some(signature) = thinking
                    .thinking_signature
                    .as_deref()
                    .filter(|signature| !signature.is_empty())
                {
                    let item = json_parse(signature).map_err(|error| {
                        ErrorObject::named("SyntaxError", error.message).thrown()
                    })?;
                    output.push(item);
                }
            }
            AssistantContentBlock::Text(text) => {
                let parsed_signature = parse_text_signature(text.text_signature.as_deref());
                let fallback_message_id = if text_block_index == 0 {
                    format!("msg_pi_{msg_index}")
                } else {
                    format!("msg_pi_{msg_index}_{text_block_index}")
                };
                text_block_index += 1;
                // OpenAI requires id to be max 64 characters
                let msg_id = match parsed_signature.as_ref().map(|parsed| parsed.id.as_str()) {
                    None | Some("") => fallback_message_id,
                    Some(id) if utf16_len(id) > 64 => format!("msg_{}", short_hash(id)),
                    Some(id) => id.to_owned(),
                };
                let mut item = json!({
                    "type": "message",
                    "role": "assistant",
                    "content": [{ "type": "output_text", "text": sanitize_surrogates(&text.text), "annotations": [] }],
                    "status": "completed",
                    "id": msg_id,
                });
                if let Some(phase) = parsed_signature.and_then(|parsed| parsed.phase) {
                    if let JsonValue::Object(object) = &mut item {
                        object.insert("phase".to_owned(), json!(phase));
                    }
                }
                output.push(item);
            }
            AssistantContentBlock::ToolCall(tool_call) => {
                let (call_id, item_id_raw) = split_tool_call_id(&tool_call.id);
                let custom_input_property =
                    grammar.and_then(|grammar| grammar.get(&tool_call.name));

                // For different-model messages, omit the id to avoid pairing
                // validation (OpenAI tracks which item ids were paired with
                // rs_xxx reasoning items). Also drop ids that do not match the
                // replayed item type: function_call ids must be fc_* and
                // custom_tool_call ids must be ctc_*.
                let item_id_prefix = if custom_input_property.is_none() {
                    "fc_"
                } else {
                    "ctc_"
                };
                let item_id = item_id_raw
                    .filter(|item_id| !is_different_model && item_id.starts_with(item_id_prefix));

                let mut item = JsonObject::new();
                if let Some(property) = custom_input_property {
                    item.insert("type".to_owned(), json!("custom_tool_call"));
                    if let Some(item_id) = item_id {
                        item.insert("id".to_owned(), json!(item_id));
                    }
                    item.insert("call_id".to_owned(), json!(call_id));
                    item.insert("name".to_owned(), json!(tool_call.name));
                    let input =
                        get_grammar_tool_input(&tool_call.name, &tool_call.arguments, property)?;
                    item.insert("input".to_owned(), json!(sanitize_surrogates(input)));
                } else {
                    item.insert("type".to_owned(), json!("function_call"));
                    if let Some(item_id) = item_id {
                        item.insert("id".to_owned(), json!(item_id));
                    }
                    item.insert("call_id".to_owned(), json!(call_id));
                    item.insert("name".to_owned(), json!(tool_call.name));
                    item.insert(
                        "arguments".to_owned(),
                        json!(json_stringify(&JsonValue::Object(
                            tool_call.arguments.clone()
                        ))),
                    );
                }
                if is_same_model {
                    if let Some(namespace) = &tool_call.namespace {
                        item.insert("namespace".to_owned(), json!(namespace));
                    }
                }
                output.push(JsonValue::Object(item));
            }
        }
    }
    Ok(output)
}

/// TS `convertResponsesTools`.
///
/// # Errors
///
/// Invalid constrained-sampling tool definitions (what TS throws).
pub fn convert_responses_tools(
    tools: &[Tool],
    options: &ConvertResponsesToolsOptions,
) -> Result<Vec<JsonValue>, Thrown> {
    let default_strict = options.strict.unwrap_or(Some(false));
    let supports_strict_mode = options.supports_strict_mode.unwrap_or(true);
    let supports_openai_grammar_tools = options.supports_openai_grammar_tools.unwrap_or(false);
    let defer_loading = options.tool_search_result.unwrap_or(false);

    tools
        .iter()
        .map(|tool| {
            if let Some(grammar) =
                resolve_grammar_constrained_sampling(tool, supports_openai_grammar_tools)?
            {
                let mut item = JsonObject::new();
                item.insert("type".to_owned(), json!("custom"));
                item.insert("name".to_owned(), json!(tool.name));
                item.insert("description".to_owned(), json!(tool.description));
                item.insert(
                    "format".to_owned(),
                    json!({
                        "type": "grammar",
                        "syntax": grammar.format,
                        "definition": grammar.definition,
                    }),
                );
                if defer_loading {
                    item.insert("defer_loading".to_owned(), json!(true));
                }
                return Ok(JsonValue::Object(item));
            }

            let constrained_strict =
                resolve_json_schema_strict_sampling(tool, supports_strict_mode, None)?;
            let strict = constrained_strict.map_or(default_strict, Some);
            let mut item = JsonObject::new();
            item.insert("type".to_owned(), json!("function"));
            item.insert("name".to_owned(), json!(tool.name));
            item.insert("description".to_owned(), json!(tool.description));
            let parameters_mode = if strict == Some(true) {
                StrictToolParameters::Strict
            } else {
                StrictToolParameters::AsDeclared
            };
            item.insert(
                "parameters".to_owned(),
                get_json_schema_tool_parameters(tool, parameters_mode)?,
            );
            if defer_loading {
                item.insert("defer_loading".to_owned(), json!(true));
            }
            if supports_strict_mode {
                item.insert("strict".to_owned(), json!(strict));
            }
            Ok(JsonValue::Object(item))
        })
        .collect()
}

#[cfg(test)]
mod tests;
