//! Transcript → Chat Completions `messages` and `tools` (TS `convertMessages`,
//! `convertTools`), plus the `reasoning_details` replay helpers.

use crate::types::IndexMap;
use serde_json::json;

use super::compat::ResolvedCompat;
use crate::api::constrained_sampling::{
    get_grammar_tool_input, get_json_schema_tool_parameters, resolve_grammar_constrained_sampling,
    resolve_json_schema_strict_sampling, StrictToolParameters,
};
use crate::api::transform_messages::transform_messages;
use crate::types::{
    AssistantContentBlock, AssistantMessage, JsonObject, JsonValue, Message, Modality, Model,
    ThinkingContent, Tool, ToolCall, TranscriptContext, UserContent, UserContentBlock,
};
use crate::utils::diagnostics::Thrown;
use crate::utils::hash::short_hash;
use crate::utils::js::{js_trim, json_stringify, utf16_len, utf16_prefix};
use crate::utils::sanitize_unicode::sanitize_surrogates;
use crate::utils::text::{get_system_message_text, render_system_message_update};
use crate::utils::transcript::{resolve_transcript, resolve_transcript_tools};

/// TS `ConvertCompletionsMessagesOptions`.
#[derive(Debug, Clone, Default)]
pub struct ConvertCompletionsMessagesOptions<'a> {
    /// Tool name → grammar input property of tools sent as `OpenAI` custom tools.
    pub grammar_tool_input_properties: Option<&'a IndexMap<String, String>>,
    /// eukhe addition: the Anthropic-format `cache_control` mark of this
    /// request. When set, user text blocks carrying a `cache_breakpoint` get
    /// it as an explicit prompt-cache breakpoint.
    pub cache_control: Option<&'a JsonValue>,
}

/// The reasoning fields an assistant replay can carry, in TS declaration order.
const OPENAI_COMPLETIONS_REASONING_FIELDS: [&str; 3] =
    ["reasoning", "reasoning_content", "reasoning_text"];

/// JS truthiness of an optional JSON property.
pub(crate) fn js_truthy(value: Option<&JsonValue>) -> bool {
    match value {
        None | Some(JsonValue::Null) => false,
        Some(JsonValue::Bool(flag)) => *flag,
        Some(JsonValue::Number(number)) => number.as_f64().is_some_and(|n| n != 0.0 && !n.is_nan()),
        Some(JsonValue::String(text)) => !text.is_empty(),
        Some(JsonValue::Array(_) | JsonValue::Object(_)) => true,
    }
}

fn has_valid_common_reasoning_detail_fields(candidate: &JsonObject) -> bool {
    matches!(
        candidate.get("id"),
        None | Some(JsonValue::Null | JsonValue::String(_))
    ) && matches!(candidate.get("format"), None | Some(JsonValue::String(_)))
        && matches!(candidate.get("index"), None | Some(JsonValue::Number(_)))
}

/// TS `isOpenAIReasoningDetail`.
pub(crate) fn is_openai_reasoning_detail(detail: &JsonValue) -> bool {
    let Some(detail) = detail.as_object() else {
        return false;
    };
    if !has_valid_common_reasoning_detail_fields(detail) {
        return false;
    }
    match detail.get("type").and_then(JsonValue::as_str) {
        Some("reasoning.summary") => detail.get("summary").is_some_and(JsonValue::is_string),
        Some("reasoning.encrypted") => detail.get("data").is_some_and(JsonValue::is_string),
        Some("reasoning.text") => {
            detail.get("text").is_some_and(JsonValue::is_string)
                && matches!(
                    detail.get("signature"),
                    None | Some(JsonValue::Null | JsonValue::String(_))
                )
        }
        _ => false,
    }
}

fn parse_openai_reasoning_details(signature: Option<&str>) -> Option<Vec<JsonValue>> {
    let signature = signature.filter(|signature| !signature.is_empty())?;
    let parsed: JsonValue = serde_json::from_str(signature).ok()?;
    match parsed {
        JsonValue::Array(details)
            if !details.is_empty() && details.iter().all(is_openai_reasoning_detail) =>
        {
            Some(details)
        }
        _ => None,
    }
}

fn parse_legacy_encrypted_reasoning_detail(signature: Option<&str>) -> Option<JsonValue> {
    let signature = signature.filter(|signature| !signature.is_empty())?;
    let parsed: JsonValue = serde_json::from_str(signature).ok()?;
    let valid = is_openai_reasoning_detail(&parsed)
        && parsed.get("type").and_then(JsonValue::as_str) == Some("reasoning.encrypted")
        && parsed
            .get("id")
            .and_then(JsonValue::as_str)
            .is_some_and(|id| !id.is_empty())
        && parsed
            .get("data")
            .and_then(JsonValue::as_str)
            .is_some_and(|data| !data.is_empty());
    valid.then_some(parsed)
}

/// Assign `key` from `source` the way TS assigns a possibly-`undefined`
/// property: an absent source value leaves the key `undefined`, which
/// `JSON.stringify` omits, so it is removed.
fn assign_from(target: &mut JsonObject, source: &JsonObject, key: &str) {
    match source.get(key) {
        Some(value) => {
            target.insert(key.to_owned(), value.clone());
        }
        None => {
            target.shift_remove(key);
        }
    }
}

fn fill_missing_common_reasoning_detail_fields(target: &mut JsonObject, source: &JsonObject) {
    if matches!(target.get("id"), None | Some(JsonValue::Null)) {
        assign_from(target, source, "id");
    }
    if !js_truthy(target.get("format")) {
        assign_from(target, source, "format");
    }
    if matches!(target.get("index"), None | Some(JsonValue::Null)) {
        assign_from(target, source, "index");
    }
}

fn append_text_field(target: &mut JsonObject, source: &JsonObject, key: &str) {
    let appended = source
        .get(key)
        .and_then(JsonValue::as_str)
        .unwrap_or_default();
    if let Some(JsonValue::String(text)) = target.get_mut(key) {
        text.push_str(appended);
    }
}

/// TS `appendOpenAIReasoningDetail`: consecutive text/summary deltas merge
/// into one logical entry; encrypted entries stay discrete. `detail` must
/// satisfy [`is_openai_reasoning_detail`].
pub(crate) fn append_openai_reasoning_detail(details: &mut Vec<JsonValue>, detail: &JsonValue) {
    let Some(source) = detail.as_object() else {
        return;
    };
    let detail_type = source.get("type").and_then(JsonValue::as_str);
    if let Some(last) = details.last_mut().and_then(JsonValue::as_object_mut) {
        let last_type = last.get("type").and_then(JsonValue::as_str);
        if detail_type == Some("reasoning.text") && last_type == Some("reasoning.text") {
            append_text_field(last, source, "text");
            if !js_truthy(last.get("signature")) {
                assign_from(last, source, "signature");
            }
            fill_missing_common_reasoning_detail_fields(last, source);
            return;
        }
        if detail_type == Some("reasoning.summary") && last_type == Some("reasoning.summary") {
            append_text_field(last, source, "summary");
            fill_missing_common_reasoning_detail_fields(last, source);
            return;
        }
    }
    details.push(detail.clone());
}

/// TS `normalizeToolCallId` inside `convertMessages`.
fn normalize_tool_call_id(model: &Model, id: &str) -> String {
    // JS `replace(/[^a-zA-Z0-9_-]/g, "_")` works on UTF-16 code units.
    fn sanitize(text: &str) -> String {
        let mut out = String::with_capacity(text.len());
        for c in text.chars() {
            if c.is_ascii_alphanumeric() || c == '_' || c == '-' {
                out.push(c);
            } else {
                for _ in 0..c.len_utf16() {
                    out.push('_');
                }
            }
        }
        out
    }
    if let Some(separator_index) = id.find('|') {
        let call_id = sanitize(&id[..separator_index]);
        let item_id = sanitize(&id[separator_index + 1..]);
        let combined_id = if item_id.is_empty() {
            call_id.clone()
        } else {
            format!("{call_id}_{item_id}")
        };
        if combined_id.len() <= 40 {
            return combined_id;
        }
        let hash: String = short_hash(id).chars().take(8).collect();
        let prefix_len = 40usize.saturating_sub(hash.len() + 1).max(1);
        let prefix: String = call_id.chars().take(prefix_len).collect();
        return format!("{prefix}_{hash}");
    }
    if model.provider == "openai" && utf16_len(id) > 40 {
        return utf16_prefix(id, 40).to_owned();
    }
    id.to_owned()
}

fn image_url(mime_type: &str, data: &str) -> JsonValue {
    json!({
        "type": "image_url",
        "image_url": { "url": format!("data:{mime_type};base64,{data}") },
    })
}

/// TS `convertMessages`.
///
/// # Errors
///
/// Fails when a grammar tool call cannot be replayed (non-string input) or
/// a tool added mid-conversation has an invalid constrained-sampling config.
// One linear loop over the transcript, kept in TS statement order.
#[allow(clippy::too_many_lines)]
pub(crate) fn convert_messages(
    model: &Model,
    context: &TranscriptContext,
    compat: &ResolvedCompat,
    options: &ConvertCompletionsMessagesOptions<'_>,
) -> Result<Vec<JsonValue>, Thrown> {
    let normalized_context =
        resolve_transcript(context.clone(), compat.supports_mid_convo_system_messages);
    let mut params: Vec<JsonValue> = Vec::new();

    let normalize = |id: &str, _: &Model, _: &AssistantMessage| normalize_tool_call_id(model, id);
    let transformed_messages =
        transform_messages(normalized_context.messages(), model, Some(&normalize));
    let transcript_tools = resolve_transcript_tools(
        normalized_context.messages(),
        compat.supports_mid_convo_system_messages == Some(true)
            && compat.supports_mid_convo_tool_additions == Some(true),
    );
    let instruction_role = if model.reasoning && compat.supports_developer_role {
        "developer"
    } else {
        "system"
    };

    let mut last_role: Option<&'static str> = None;
    let mut i = 0;
    while i < transformed_messages.len() {
        let msg = &transformed_messages[i];
        // Some providers don't allow user messages directly after tool results.
        if compat.requires_assistant_after_tool_result
            && last_role == Some("toolResult")
            && matches!(msg, Message::User(_))
        {
            params.push(json!({
                "role": "assistant",
                "content": "I have processed the tool results.",
            }));
        }

        match msg {
            Message::System(system) => {
                let added_tools: &[Tool] = if i > 0 && transcript_tools.anchors_additions {
                    system.tools_added.as_deref().unwrap_or_default()
                } else {
                    &[]
                };
                if !added_tools.is_empty() {
                    params.push(json!({
                        "role": "system",
                        "tools": convert_tools(added_tools, compat)?,
                    }));
                }
                let text = if i == 0 {
                    get_system_message_text(system)
                } else {
                    render_system_message_update(system)
                };
                if !text.is_empty() {
                    params.push(json!({
                        "role": instruction_role,
                        "content": sanitize_surrogates(&text),
                    }));
                }
            }
            Message::User(user) => match &user.content {
                UserContent::Text(text) => {
                    params.push(json!({ "role": "user", "content": sanitize_surrogates(text) }));
                }
                UserContent::Blocks(blocks) => {
                    let parts: Vec<JsonValue> = blocks
                        .iter()
                        .filter(|item| match item {
                            UserContentBlock::Text(text) => !text.text.is_empty(),
                            UserContentBlock::Image(_) => true,
                        })
                        .map(|item| match item {
                            UserContentBlock::Text(text) => {
                                let mut part = json!({
                                    "type": "text",
                                    "text": sanitize_surrogates(&text.text),
                                });
                                // eukhe addition: a marked block ends a cacheable prefix.
                                if let (Some(cache_control), Some(_)) =
                                    (options.cache_control, text.cache_breakpoint)
                                {
                                    if let Some(part) = part.as_object_mut() {
                                        part.insert("cache_control".into(), cache_control.clone());
                                    }
                                }
                                part
                            }
                            UserContentBlock::Image(image) => {
                                image_url(&image.mime_type, &image.data)
                            }
                        })
                        .collect();
                    if parts.is_empty() {
                        i += 1;
                        continue;
                    }
                    params.push(json!({ "role": "user", "content": parts }));
                }
            },
            Message::Assistant(assistant) => {
                let Some(message) = convert_assistant(model, compat, options, assistant)? else {
                    i += 1;
                    continue;
                };
                params.push(message);
            }
            Message::ToolResult(_) => {
                let mut image_blocks: Vec<JsonValue> = Vec::new();
                let mut j = i;
                while let Some(Message::ToolResult(tool_msg)) = transformed_messages.get(j) {
                    let text_result = tool_msg
                        .content
                        .iter()
                        .filter_map(|block| match block {
                            UserContentBlock::Text(text) => Some(text.text.as_str()),
                            UserContentBlock::Image(_) => None,
                        })
                        .collect::<Vec<_>>()
                        .join("\n");
                    let has_images = tool_msg
                        .content
                        .iter()
                        .any(|block| matches!(block, UserContentBlock::Image(_)));
                    let tool_result_text = if !text_result.is_empty() {
                        text_result.as_str()
                    } else if has_images {
                        "(see attached image)"
                    } else {
                        "(no tool output)"
                    };
                    let mut tool_result_msg = json!({
                        "role": "tool",
                        "content": sanitize_surrogates(tool_result_text),
                        "tool_call_id": tool_msg.tool_call_id,
                    });
                    if compat.requires_tool_result_name && !tool_msg.tool_name.is_empty() {
                        if let Some(object) = tool_result_msg.as_object_mut() {
                            object.insert("name".into(), json!(tool_msg.tool_name));
                        }
                    }
                    params.push(tool_result_msg);

                    if has_images && model.input.contains(&Modality::Image) {
                        for block in &tool_msg.content {
                            if let UserContentBlock::Image(image) = block {
                                image_blocks.push(image_url(&image.mime_type, &image.data));
                            }
                        }
                    }
                    j += 1;
                }
                i = j;

                if image_blocks.is_empty() {
                    last_role = Some("toolResult");
                } else {
                    if compat.requires_assistant_after_tool_result {
                        params.push(json!({
                            "role": "assistant",
                            "content": "I have processed the tool results.",
                        }));
                    }
                    let mut parts = vec![json!({
                        "type": "text",
                        "text": "Attached image(s) from tool result:",
                    })];
                    parts.extend(image_blocks);
                    params.push(json!({ "role": "user", "content": parts }));
                    last_role = Some("user");
                }
                continue;
            }
        }

        last_role = Some(msg.role());
        i += 1;
    }

    Ok(params)
}

/// The assistant branch of `convertMessages`; `None` when the message has no
/// content and no tool calls and is skipped.
// One branch of the TS loop, kept in TS statement order.
#[allow(clippy::too_many_lines)]
fn convert_assistant(
    model: &Model,
    compat: &ResolvedCompat,
    options: &ConvertCompletionsMessagesOptions<'_>,
    msg: &AssistantMessage,
) -> Result<Option<JsonValue>, Thrown> {
    let mut assistant_msg = JsonObject::new();
    assistant_msg.insert("role".into(), json!("assistant"));
    // Some providers don't accept null content, use empty string instead.
    assistant_msg.insert(
        "content".into(),
        if compat.requires_assistant_after_tool_result {
            json!("")
        } else {
            JsonValue::Null
        },
    );

    let assistant_text_parts: Vec<String> = msg
        .content
        .iter()
        .filter_map(|block| match block {
            AssistantContentBlock::Text(text) if !js_trim(&text.text).is_empty() => {
                Some(sanitize_surrogates(&text.text).into_owned())
            }
            AssistantContentBlock::Text(_)
            | AssistantContentBlock::Thinking(_)
            | AssistantContentBlock::ToolCall(_) => None,
        })
        .collect();
    let assistant_text = assistant_text_parts.concat();

    let thinking_blocks: Vec<&ThinkingContent> = msg
        .content
        .iter()
        .filter_map(|block| match block {
            AssistantContentBlock::Thinking(thinking) => Some(thinking),
            AssistantContentBlock::Text(_) | AssistantContentBlock::ToolCall(_) => None,
        })
        .collect();
    let tool_calls: Vec<&ToolCall> = msg
        .content
        .iter()
        .filter_map(|block| match block {
            AssistantContentBlock::ToolCall(tool_call) => Some(tool_call),
            AssistantContentBlock::Text(_) | AssistantContentBlock::Thinking(_) => None,
        })
        .collect();
    let signed_reasoning_details = thinking_blocks
        .iter()
        .find_map(|block| parse_openai_reasoning_details(block.thinking_signature.as_deref()));
    let legacy_reasoning_details: Vec<JsonValue> = tool_calls
        .iter()
        .filter_map(|tool_call| {
            parse_legacy_encrypted_reasoning_detail(tool_call.thought_signature.as_deref())
        })
        .collect();
    let preserved_reasoning_details = signed_reasoning_details
        .or_else(|| (!legacy_reasoning_details.is_empty()).then_some(legacy_reasoning_details));

    let non_empty_thinking_blocks: Vec<&ThinkingContent> = thinking_blocks
        .iter()
        .copied()
        .filter(|block| !js_trim(&block.thinking).is_empty())
        .collect();
    if let Some(first_thinking) = non_empty_thinking_blocks.first() {
        if compat.requires_thinking_as_text {
            // Convert thinking blocks to plain text (no tags to avoid model mimicking them).
            let thinking_text = non_empty_thinking_blocks
                .iter()
                .map(|block| sanitize_surrogates(&block.thinking).into_owned())
                .collect::<Vec<_>>()
                .join("\n\n");
            let mut content = vec![json!({ "type": "text", "text": thinking_text })];
            content.extend(
                assistant_text_parts
                    .iter()
                    .map(|text| json!({ "type": "text", "text": text })),
            );
            assistant_msg.insert("content".into(), JsonValue::Array(content));
        } else {
            // Always send assistant content as a plain string (the Chat
            // Completions standard); arrays make some models mirror the block
            // structure literally.
            if !assistant_text.is_empty() {
                assistant_msg.insert("content".into(), json!(assistant_text));
            }
            // reasoning_details is the structured alternative to a raw reasoning field.
            if preserved_reasoning_details.is_none() {
                let mut signature = first_thinking.thinking_signature.as_deref();
                if model.provider == "opencode-go" && signature == Some("reasoning") {
                    signature = Some("reasoning_content");
                }
                if let Some(field) =
                    signature.filter(|field| OPENAI_COMPLETIONS_REASONING_FIELDS.contains(field))
                {
                    let joined = non_empty_thinking_blocks
                        .iter()
                        .map(|block| block.thinking.as_str())
                        .collect::<Vec<_>>()
                        .join("\n");
                    assistant_msg.insert(field.to_owned(), json!(joined));
                }
            }
        }
    } else if !assistant_text.is_empty() {
        assistant_msg.insert("content".into(), json!(assistant_text));
    }

    if !tool_calls.is_empty() {
        let mut converted = Vec::with_capacity(tool_calls.len());
        for tool_call in &tool_calls {
            let custom_input_property = options
                .grammar_tool_input_properties
                .and_then(|properties| properties.get(&tool_call.name));
            converted.push(match custom_input_property {
                Some(property) => {
                    let input =
                        get_grammar_tool_input(&tool_call.name, &tool_call.arguments, property)?;
                    json!({
                        "id": tool_call.id,
                        "type": "custom",
                        "custom": {
                            "name": tool_call.name,
                            "input": sanitize_surrogates(input),
                        },
                    })
                }
                None => json!({
                    "id": tool_call.id,
                    "type": "function",
                    "function": {
                        "name": tool_call.name,
                        "arguments": json_stringify(&JsonValue::Object(tool_call.arguments.clone())),
                    },
                }),
            });
        }
        assistant_msg.insert("tool_calls".into(), JsonValue::Array(converted));
    }
    if let Some(details) = preserved_reasoning_details {
        assistant_msg.insert("reasoning_details".into(), JsonValue::Array(details));
    }
    if compat.requires_reasoning_content_on_assistant_messages
        && model.reasoning
        && !assistant_msg.contains_key("reasoning_content")
    {
        assistant_msg.insert("reasoning_content".into(), json!(""));
    }
    // Skip assistant messages that have no content and no tool calls.
    let has_content = match assistant_msg.get("content") {
        Some(JsonValue::String(text)) => !text.is_empty(),
        Some(JsonValue::Array(parts)) => !parts.is_empty(),
        _ => false,
    };
    if !has_content && !assistant_msg.contains_key("tool_calls") {
        return Ok(None);
    }
    Ok(Some(JsonValue::Object(assistant_msg)))
}

/// TS `convertTools`.
///
/// # Errors
///
/// Fails on invalid grammar or strict-mode constrained-sampling configs.
pub(crate) fn convert_tools(
    tools: &[Tool],
    compat: &ResolvedCompat,
) -> Result<Vec<JsonValue>, Thrown> {
    tools
        .iter()
        .map(|tool| {
            if let Some(grammar) =
                resolve_grammar_constrained_sampling(tool, compat.supports_openai_grammar_tools)?
            {
                return Ok(json!({
                    "type": "custom",
                    "custom": {
                        "name": tool.name,
                        "description": tool.description,
                        "format": {
                            "type": "grammar",
                            "grammar": {
                                "syntax": grammar.format,
                                "definition": grammar.definition,
                            },
                        },
                    },
                }));
            }
            let strict =
                resolve_json_schema_strict_sampling(tool, compat.supports_strict_mode, None)?;
            let mut function = json!({
                "name": tool.name,
                "description": tool.description,
                "parameters": get_json_schema_tool_parameters(
                    tool,
                    if strict == Some(true) {
                        StrictToolParameters::Strict
                    } else {
                        StrictToolParameters::AsDeclared
                    },
                )?,
            });
            // Only include strict if provider supports it. Some reject unknown fields.
            if compat.supports_strict_mode {
                if let Some(function) = function.as_object_mut() {
                    function.insert("strict".into(), json!(strict.unwrap_or(false)));
                }
            }
            Ok(json!({ "type": "function", "function": function }))
        })
        .collect()
}
