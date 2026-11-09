//! Converse request building: messages, system prompt, tool configuration,
//! additional model request fields, and the model-capability checks behind
//! them. Section of the port of `api/bedrock-converse-stream.ts`.

use base64::engine::general_purpose::{GeneralPurpose, GeneralPurposeConfig, STANDARD};
use base64::engine::DecodePaddingMode;
use base64::Engine as _;
use eukhe_bend::rules::model_facts::{
    self, Effort, GptEffort, Level, MapEntry, ReasoningFields, Shape,
};
use eukhe_types::pi_ai::{
    AssistantContentBlock, CacheRetention, JsonObject, JsonValue, Message, Model,
    ModelThinkingLevel, ProviderEnv, StopReason, ThinkingLevel, Tool, UserContent,
    UserContentBlock,
};
use serde_json::json;

use super::client_config::get_configured_bedrock_region;
use super::{BedrockOptions, BedrockThinkingDisplay, BedrockToolChoice};
use crate::api::cache_breakpoints::{has_assistant_cache_breakpoint, has_cache_breakpoint};
use crate::api::constrained_sampling::{
    get_json_schema_tool_parameters, ConstrainedSamplingError, StrictPlan, StrictSupport,
    StrictToolParameters,
};
use crate::api::simple_options::thinking_budget_for_level;
use crate::api::tool_result_content::sent_blocks;
use crate::api::transform_messages::transform_messages;
use crate::models::{adaptive_thinking, thinking_level_map};
use crate::quirks::Quirks;
use crate::utils::diagnostics::{ErrorObject, Thrown};
use crate::utils::js::js_trim;
use crate::utils::provider_env::get_provider_env_value;
use crate::utils::sanitize_unicode::sanitize_surrogates;
use crate::utils::transcript::without_initial_system_message;

#[cfg(test)]
mod facts_tests;

const EMPTY_TEXT_PLACEHOLDER: &str = "<empty>";

const THINKING_BINDING_CONTROLS_BETA: &str = "thinking-binding-controls-2026-08-01";

/// The thinking-level map's entry of `level` for `model`, as the compiled
/// core reads it.
fn map_entry(model: &Model, level: ModelThinkingLevel) -> MapEntry {
    match thinking_level_map(model).and_then(|map| map.get(&level)) {
        None => MapEntry::Missing,
        Some(None) => MapEntry::Null,
        Some(Some(_)) => MapEntry::Wire,
    }
}

const fn level_of(level: ThinkingLevel) -> Level {
    match level {
        ThinkingLevel::Minimal => Level::Minimal,
        ThinkingLevel::Low => Level::Low,
        ThinkingLevel::Medium => Level::Medium,
        ThinkingLevel::High => Level::High,
        ThinkingLevel::Xhigh => Level::Xhigh,
        ThinkingLevel::Max => Level::Max,
    }
}

/// The map's own wire string of `level` (the effort `Mapped` names).
fn mapped_effort(model: &Model, level: ThinkingLevel) -> String {
    thinking_level_map(model)
        .and_then(|map| map.get(&ModelThinkingLevel::from(level)))
        .and_then(Option::clone)
        .unwrap_or_default()
}

/// TS `mapThinkingLevelToEffort`: the model's thinking-level map, else the
/// Bedrock default effort of the level. A model with native `xhigh` says so
/// in its map (`xhigh: "xhigh"`).
#[must_use]
pub fn map_thinking_level_to_effort(model: &Model, level: ThinkingLevel) -> String {
    let entries = [
        ModelThinkingLevel::Minimal,
        ModelThinkingLevel::Low,
        ModelThinkingLevel::Medium,
        ModelThinkingLevel::High,
        ModelThinkingLevel::Xhigh,
        ModelThinkingLevel::Max,
    ]
    .map(|at| map_entry(model, at));
    match model_facts::effort(entries, level_of(level)) {
        Effort::Mapped => mapped_effort(model, level),
        Effort::Low => "low".to_owned(),
        Effort::Medium => "medium".to_owned(),
        Effort::High => "high".to_owned(),
    }
}

/// TS `resolveCacheRetention`: defaults to `short`; `PI_CACHE_RETENTION=long`
/// for backward compatibility.
pub(crate) fn resolve_cache_retention(
    cache_retention: Option<CacheRetention>,
    env: Option<&ProviderEnv>,
) -> CacheRetention {
    if let Some(retention) = cache_retention {
        return retention;
    }
    if get_provider_env_value("PI_CACHE_RETENTION", env).as_deref() == Some("long") {
        return CacheRetention::Long;
    }
    CacheRetention::Short
}

/// Whether the rulebook gives the model Claude's request shape on Bedrock
/// (`bedrock_reasoning: "claude"`; TS `isAnthropicClaudeModel`, which read
/// the id and the name: application inference profile ARNs do not hold
/// the model name).
pub(crate) fn is_anthropic_claude_model(model: &Model) -> bool {
    Quirks::of(model).bedrock_reasoning() == Some(Shape::Claude)
}

/// TS `supportsPromptCaching`: the quirks rulebook's `prompt_caching` for
/// the model; a model the rulebook does not name caches only with
/// `AWS_BEDROCK_FORCE_CACHE=1`.
#[must_use]
pub fn supports_prompt_caching(model: &Model, env: Option<&ProviderEnv>) -> bool {
    let forced = get_provider_env_value("AWS_BEDROCK_FORCE_CACHE", env).as_deref() == Some("1");
    model_facts::flag(Quirks::of(model).prompt_caching(), forced)
}

/// TS `supportsThinkingSignature`: only Claude accepts
/// `reasoningContent.reasoningText.signature`.
fn supports_thinking_signature(model: &Model) -> bool {
    is_anthropic_claude_model(model)
}

/// A `cachePoint` content block (TS `{ type: CachePointType.DEFAULT, ttl? }`).
fn cache_point(cache_retention: CacheRetention) -> JsonValue {
    let mut point = JsonObject::new();
    point.insert("type".to_owned(), "default".into());
    if cache_retention == CacheRetention::Long {
        point.insert("ttl".to_owned(), "1h".into());
    }
    json!({ "cachePoint": point })
}

/// eukhe addition: the cache point after a block marked with
/// `TextContent::cache_breakpoint` (the provider default, shortest TTL).
fn breakpoint_cache_point() -> JsonValue {
    json!({ "cachePoint": { "type": "default" } })
}

/// TS `buildSystemPrompt`. eukhe addition: with marked blocks the system
/// cache points are optional and take mark slots only while some are left
/// after the `placed` message marks (`eukhe_bend::rules::cache_marks`);
/// the prompt's shared `prefix` and the session's `tail` (`""` when the
/// prompt is not split) are blocks of their own, each with its cache point.
pub(crate) fn build_system_prompt(
    prefix: &str,
    tail: &str,
    model: &Model,
    cache_retention: CacheRetention,
    env: Option<&ProviderEnv>,
    placed: usize,
) -> Option<Vec<JsonValue>> {
    if prefix.is_empty() && tail.is_empty() {
        return None;
    }
    let want = cache_retention != CacheRetention::None && supports_prompt_caching(model, env);
    let marks = eukhe_bend::rules::cache_marks::grant(
        placed,
        [want && !prefix.is_empty(), want && !tail.is_empty()],
    );
    let mut blocks = Vec::new();
    for (text, marked) in [prefix, tail].into_iter().zip(marks) {
        if text.is_empty() {
            continue;
        }
        blocks.push(json!({ "text": sanitize_surrogates(text) }));
        if marked {
            blocks.push(cache_point(cache_retention));
        }
    }
    Some(blocks)
}

/// TS `normalizeToolCallId`: Bedrock tool-use ids are `[a-zA-Z0-9_-]{1,64}`.
pub(crate) fn normalize_tool_call_id(id: &str) -> String {
    let mut sanitized = String::with_capacity(id.len());
    for c in id.chars() {
        if c.is_ascii_alphanumeric() || c == '_' || c == '-' {
            sanitized.push(c);
        } else {
            // The TS regex replaces each UTF-16 code unit.
            for _ in 0..c.len_utf16() {
                sanitized.push('_');
            }
        }
    }
    sanitized.truncate(64);
    sanitized
}

/// TS `createNonBlankTextBlock`.
fn create_non_blank_text_block(text: &str) -> Option<JsonValue> {
    let sanitized = sanitize_surrogates(text);
    if js_trim(&sanitized).is_empty() {
        None
    } else {
        Some(json!({ "text": sanitized }))
    }
}

/// TS `createRequiredTextBlock`.
fn create_required_text_block(text: &str) -> JsonValue {
    create_non_blank_text_block(text).unwrap_or_else(|| json!({ "text": EMPTY_TEXT_PLACEHOLDER }))
}

/// TS `sanitizeBedrockDocument`: drops empty property names at any depth.
fn sanitize_bedrock_document(value: &JsonValue) -> JsonValue {
    match value {
        JsonValue::Array(items) => {
            JsonValue::Array(items.iter().map(sanitize_bedrock_document).collect())
        }
        JsonValue::Object(object) => JsonValue::Object(
            object
                .iter()
                .filter(|(key, _)| !key.is_empty())
                .map(|(key, nested)| (key.clone(), sanitize_bedrock_document(nested)))
                .collect(),
        ),
        other => other.clone(),
    }
}

/// JS `atob` (forgiving-base64 decode), with its `InvalidCharacterError`s.
fn atob(data: &str) -> Result<Vec<u8>, Thrown> {
    let mut text: String = data
        .chars()
        .filter(|c| !matches!(c, '\t' | '\n' | '\u{000C}' | '\r' | ' '))
        .collect();
    if text.len().is_multiple_of(4) {
        for _ in 0..2 {
            if text.ends_with('=') {
                text.pop();
            }
        }
    }
    if !text
        .chars()
        .all(|c| c.is_ascii_alphanumeric() || c == '+' || c == '/')
    {
        return Err(ErrorObject::named("InvalidCharacterError", "Invalid character").thrown());
    }
    if text.len() % 4 == 1 {
        return Err(ErrorObject::named(
            "InvalidCharacterError",
            "The string to be decoded is not correctly encoded.",
        )
        .thrown());
    }
    let lenient = GeneralPurpose::new(
        &base64::alphabet::STANDARD,
        GeneralPurposeConfig::new()
            .with_decode_padding_mode(DecodePaddingMode::RequireNone)
            .with_decode_allow_trailing_bits(true),
    );
    lenient.decode(text.as_bytes()).map_err(|_| {
        ErrorObject::named(
            "InvalidCharacterError",
            "The string to be decoded is not correctly encoded.",
        )
        .thrown()
    })
}

/// TS `base64ToBytes`, in the base64 wire form the SDK sends: the decoded
/// bytes re-encoded canonically.
fn base64_to_wire_bytes(data: &str) -> Result<String, Thrown> {
    Ok(STANDARD.encode(atob(data)?))
}

/// TS `createImageBlock`.
fn create_image_block(mime_type: &str, data: &str) -> Result<JsonValue, Thrown> {
    let format = match mime_type {
        "image/jpeg" | "image/jpg" => "jpeg",
        "image/png" => "png",
        "image/gif" => "gif",
        "image/webp" => "webp",
        _ => {
            return Err(ErrorObject::new(format!("Unknown image type: {mime_type}")).thrown());
        }
    };
    Ok(json!({ "source": { "bytes": base64_to_wire_bytes(data)? }, "format": format }))
}

/// TS `decodeRedactedContent`: a stored signature that is not base64 drops
/// the block instead of failing the request.
fn decode_redacted_content(signature: Option<&str>) -> Option<String> {
    let signature = signature.filter(|signature| !signature.is_empty())?;
    atob(signature).ok().map(|bytes| STANDARD.encode(bytes))
}

/// Whether a tool result failed: its images then go as text lines.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ResultStatus {
    Success,
    Error,
}

/// TS `convertToolResultContent`. eukhe addition: the blocks sent are the
/// compiled core's ([`sent_blocks`]): an error result's images go as text
/// lines, as Anthropic models take only text in an error tool result.
fn convert_tool_result_content(
    content: &[UserContentBlock],
    status: ResultStatus,
) -> Result<Vec<JsonValue>, Thrown> {
    let mut result = Vec::new();
    for block in sent_blocks(content, status == ResultStatus::Error) {
        match block.as_ref() {
            UserContentBlock::Image(image) => {
                result.push(json!({ "image": create_image_block(&image.mime_type, &image.data)? }));
            }
            UserContentBlock::Text(text) => {
                if let Some(text_block) = create_non_blank_text_block(&text.text) {
                    result.push(text_block);
                }
            }
        }
    }
    if result.is_empty() {
        result.push(json!({ "text": EMPTY_TEXT_PLACEHOLDER }));
    }
    Ok(result)
}

/// The assistant blocks of one message (TS `convertMessages`, `assistant`).
/// eukhe addition: when `breakpoints` is on, a cache point follows each
/// marked text block that is sent.
fn convert_assistant_content(
    content: &[AssistantContentBlock],
    model: &Model,
    breakpoints: bool,
) -> Vec<JsonValue> {
    let mut blocks = Vec::new();
    for block in content {
        match block {
            AssistantContentBlock::Text(text) => {
                if let Some(text_block) = create_non_blank_text_block(&text.text) {
                    blocks.push(text_block);
                    if breakpoints && has_assistant_cache_breakpoint(block) {
                        blocks.push(breakpoint_cache_point());
                    }
                }
            }
            AssistantContentBlock::ToolCall(call) => {
                blocks.push(json!({
                    "toolUse": {
                        "toolUseId": call.id,
                        "name": call.name,
                        "input": sanitize_bedrock_document(&JsonValue::Object(call.arguments.clone())),
                    }
                }));
            }
            AssistantContentBlock::Thinking(thinking) => {
                // Encrypted reasoning is opaque: replay the stored payload as
                // the `redactedContent` member.
                if thinking.redacted == Some(true) {
                    if let Some(redacted) =
                        decode_redacted_content(thinking.thinking_signature.as_deref())
                            .filter(|redacted| !redacted.is_empty())
                    {
                        blocks.push(json!({ "reasoningContent": { "redactedContent": redacted } }));
                    }
                    continue;
                }
                let text = sanitize_surrogates(&thinking.thinking);
                if js_trim(&text).is_empty() {
                    continue;
                }
                if supports_thinking_signature(model) {
                    // A partial or externally persisted message without a
                    // signature replays as plain text, matching Anthropic.
                    match thinking
                        .thinking_signature
                        .as_deref()
                        .filter(|signature| !js_trim(signature).is_empty())
                    {
                        None => blocks.push(json!({ "text": text })),
                        Some(signature) => blocks.push(json!({
                            "reasoningContent": {
                                "reasoningText": { "text": text, "signature": signature },
                            }
                        })),
                    }
                } else {
                    blocks
                        .push(json!({ "reasoningContent": { "reasoningText": { "text": text } } }));
                }
            }
        }
    }
    blocks
}

/// The user blocks of one message (TS `convertMessages`, `user`). eukhe
/// addition: when `breakpoints` is on, a cache point follows each marked
/// text block that is sent.
fn convert_user_content(
    content: &UserContent,
    breakpoints: bool,
) -> Result<Vec<JsonValue>, Thrown> {
    let blocks = match content {
        UserContent::Text(text) => return Ok(vec![create_required_text_block(text)]),
        UserContent::Blocks(blocks) => blocks,
    };
    let mut converted = Vec::new();
    for block in blocks {
        match block {
            UserContentBlock::Text(text) => {
                if let Some(text_block) = create_non_blank_text_block(&text.text) {
                    converted.push(text_block);
                    if breakpoints && has_cache_breakpoint(block) {
                        converted.push(breakpoint_cache_point());
                    }
                }
            }
            UserContentBlock::Image(image) => {
                converted
                    .push(json!({ "image": create_image_block(&image.mime_type, &image.data)? }));
            }
        }
    }
    if converted.is_empty() {
        converted.push(json!({ "text": EMPTY_TEXT_PLACEHOLDER }));
    }
    Ok(converted)
}

/// TS `convertMessages`.
pub(crate) fn convert_messages(
    messages: &[Message],
    model: &Model,
    cache_retention: CacheRetention,
    env: Option<&ProviderEnv>,
) -> Result<Vec<JsonValue>, Thrown> {
    let normalize =
        |id: &str, _: &Model, _: &eukhe_types::pi_ai::AssistantMessage| normalize_tool_call_id(id);
    let transformed = transform_messages(
        without_initial_system_message(messages),
        model,
        Some(&normalize),
    );
    let caching = cache_retention != CacheRetention::None && supports_prompt_caching(model, env);

    let mut result: Vec<JsonValue> = Vec::new();
    let mut i = 0;
    while i < transformed.len() {
        match &transformed[i] {
            Message::User(user) => {
                let content = convert_user_content(&user.content, caching)?;
                result.push(json!({ "role": "user", "content": content }));
            }
            Message::Assistant(assistant) => {
                // Bedrock rejects messages with empty content arrays.
                if !assistant.content.is_empty() {
                    let content = convert_assistant_content(&assistant.content, model, caching);
                    if !content.is_empty() {
                        result.push(json!({ "role": "assistant", "content": content }));
                    }
                }
            }
            Message::ToolResult(_) => {
                // Bedrock requires all consecutive tool results in one user message.
                let mut tool_results = Vec::new();
                let mut j = i;
                while let Some(Message::ToolResult(next)) = transformed.get(j) {
                    tool_results.push(json!({
                        "toolResult": {
                            "toolUseId": next.tool_call_id,
                            "content": convert_tool_result_content(
                                &next.content,
                                if next.is_error {
                                    ResultStatus::Error
                                } else {
                                    ResultStatus::Success
                                },
                            )?,
                            "status": if next.is_error { "error" } else { "success" },
                        }
                    }));
                    j += 1;
                }
                i = j - 1;
                result.push(json!({ "role": "user", "content": tool_results }));
            }
            Message::System(_) => {}
        }
        i += 1;
    }

    // Add a cache point to the last user message. eukhe addition: a marked
    // last block already ends with one.
    if caching {
        if let Some(JsonValue::Object(last)) = result.last_mut() {
            if last.get("role").and_then(JsonValue::as_str) == Some("user") {
                if let Some(JsonValue::Array(content)) = last.get_mut("content") {
                    if content
                        .last()
                        .is_none_or(|block| block.get("cachePoint").is_none())
                    {
                        content.push(cache_point(cache_retention));
                    }
                }
            }
        }
    }
    Ok(result)
}

/// TS `convertToolConfig`.
pub(crate) fn convert_tool_config(
    tools: &[Tool],
    tool_choice: Option<&BedrockToolChoice>,
    strict_support: StrictSupport,
) -> Result<Option<JsonValue>, ConstrainedSamplingError> {
    if tools.is_empty() || tool_choice == Some(&BedrockToolChoice::None) {
        return Ok(None);
    }
    let strict_plan = StrictPlan::new(tools, strict_support, None)?;
    let mut bedrock_tools = Vec::with_capacity(tools.len());
    for tool in tools {
        let strict = strict_plan.resolve(tool, None)?;
        let parameters = get_json_schema_tool_parameters(
            tool,
            if strict == Some(true) {
                StrictToolParameters::Strict
            } else {
                StrictToolParameters::AsDeclared
            },
        )?;
        let mut spec = JsonObject::new();
        spec.insert("name".to_owned(), tool.name.clone().into());
        spec.insert("description".to_owned(), tool.description.clone().into());
        spec.insert("inputSchema".to_owned(), json!({ "json": parameters }));
        if strict == Some(true) {
            spec.insert("strict".to_owned(), true.into());
        }
        bedrock_tools.push(json!({ "toolSpec": spec }));
    }
    let bedrock_tool_choice = match tool_choice {
        Some(BedrockToolChoice::Auto) => Some(json!({ "auto": {} })),
        Some(BedrockToolChoice::Any) => Some(json!({ "any": {} })),
        Some(BedrockToolChoice::Tool { name }) => Some(json!({ "tool": { "name": name } })),
        Some(BedrockToolChoice::None) | None => None,
    };
    let mut config = JsonObject::new();
    config.insert("tools".to_owned(), JsonValue::Array(bedrock_tools));
    if let Some(choice) = bedrock_tool_choice {
        config.insert("toolChoice".to_owned(), choice);
    }
    Ok(Some(JsonValue::Object(config)))
}

/// TS `mapStopReason`: the stop reason and, for unknown reasons, the error.
pub(crate) fn map_stop_reason(reason: Option<&str>) -> (StopReason, Option<String>) {
    match reason {
        Some("end_turn" | "stop_sequence") => (StopReason::Stop, None),
        Some("max_tokens" | "model_context_window_exceeded") => (StopReason::Length, None),
        Some("tool_use") => (StopReason::ToolUse, None),
        Some(reason) if !reason.is_empty() => (
            StopReason::Error,
            Some(format!("Provider stopped with: {reason}")),
        ),
        Some(_) | None => (StopReason::Error, None),
    }
}

/// TS `isGovCloudBedrockTarget`.
fn is_gov_cloud_bedrock_target(model: &Model, options: &BedrockOptions) -> bool {
    if get_configured_bedrock_region(options)
        .is_some_and(|region| region.to_lowercase().starts_with("us-gov-"))
    {
        return true;
    }
    let model_id = model.id.to_lowercase();
    model_id.starts_with("us-gov.") || model_id.starts_with("arn:aws-us-gov:")
}

/// TS `buildAdditionalModelRequestFields`.
pub(crate) fn build_additional_model_request_fields(
    model: &Model,
    options: &BedrockOptions,
) -> Option<JsonValue> {
    let reasoning = options.reasoning?;
    if !model.reasoning {
        return None;
    }
    let fields = model_facts::reasoning(
        Quirks::of(model).bedrock_reasoning(),
        map_entry(model, ModelThinkingLevel::from(reasoning)),
        level_of(reasoning),
    );
    let gpt_effort = |effort: GptEffort| match effort {
        GptEffort::Mapped => mapped_effort(model, reasoning),
        GptEffort::Low => "low".to_owned(),
        GptEffort::Medium => "medium".to_owned(),
        GptEffort::High => "high".to_owned(),
        GptEffort::Xhigh => "xhigh".to_owned(),
        GptEffort::Max => "max".to_owned(),
    };
    match fields {
        ReasoningFields::None => return None,
        ReasoningFields::Nested(effort) => {
            return Some(json!({ "reasoning": { "effort": gpt_effort(effort) } }));
        }
        ReasoningFields::Flat(effort) => {
            return Some(json!({ "reasoning_effort": gpt_effort(effort) }));
        }
        ReasoningFields::Claude => {}
    }
    // GovCloud Bedrock rejects the Claude thinking.display field and block
    // binding.
    let is_gov_cloud = is_gov_cloud_bedrock_target(model, options);
    let display = if is_gov_cloud {
        None
    } else {
        Some(
            options
                .thinking_display
                .unwrap_or(BedrockThinkingDisplay::Summarized),
        )
    };
    let adaptive = adaptive_thinking(model);
    let mut result = JsonObject::new();
    if adaptive {
        let use_block_binding =
            !is_gov_cloud && model_facts::flag(Quirks::of(model).thinking_block_binding(), false);
        let mut thinking = JsonObject::new();
        thinking.insert("type".to_owned(), "adaptive".into());
        if let Some(display) = display {
            thinking.insert("display".to_owned(), display.as_str().into());
        }
        if use_block_binding {
            thinking.insert(
                "block_binding".to_owned(),
                json!({ "prefix_mismatch_behavior": "drop_block" }),
            );
        }
        result.insert("thinking".to_owned(), JsonValue::Object(thinking));
        result.insert(
            "output_config".to_owned(),
            json!({ "effort": map_thinking_level_to_effort(model, reasoning) }),
        );
        if use_block_binding {
            result.insert(
                "anthropic_beta".to_owned(),
                json!([THINKING_BINDING_CONTROLS_BETA]),
            );
        }
    } else {
        // Budget-based Claude clamps extended levels to high; custom budgets
        // only cover token-based levels through high.
        let mut thinking = JsonObject::new();
        thinking.insert("type".to_owned(), "enabled".into());
        thinking.insert(
            "budget_tokens".to_owned(),
            thinking_budget_for_level(reasoning, options.thinking_budgets.as_ref()).into(),
        );
        if let Some(display) = display {
            thinking.insert("display".to_owned(), display.as_str().into());
        }
        result.insert("thinking".to_owned(), JsonValue::Object(thinking));
        // Only a caller's explicit `interleavedThinking` adds the beta (omp
        // `amazon-bedrock.ts` `buildAdditionalModelRequestFields`).
        if options.interleaved_thinking == Some(true) {
            result.insert(
                "anthropic_beta".to_owned(),
                json!(["interleaved-thinking-2025-05-14"]),
            );
        }
    }
    Some(JsonValue::Object(result))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Regression: an error tool result's image went to Bedrock as an image
    /// block, which Anthropic models refuse in an error result. It now goes
    /// as a text line; a successful result keeps its image.
    #[test]
    fn an_error_tool_result_sends_text_only() {
        let content = vec![
            UserContentBlock::Text(eukhe_types::pi_ai::TextContent::new("failed")),
            UserContentBlock::Image(eukhe_types::pi_ai::ImageContent {
                data: "AA==".to_string(),
                mime_type: "image/png".to_string(),
            }),
        ];
        assert_eq!(
            (
                convert_tool_result_content(&content, ResultStatus::Error).unwrap(),
                convert_tool_result_content(&content, ResultStatus::Success)
                    .unwrap()
                    .len(),
            ),
            (
                vec![
                    json!({ "text": "failed" }),
                    json!({ "text": "[image omitted: error result]" })
                ],
                2,
            )
        );
    }

    /// eukhe addition: with breakpoints on, a marked assistant text block is
    /// followed by a cache point; without them the blocks go unmarked.
    #[test]
    fn a_marked_assistant_text_block_is_followed_by_a_cache_point() {
        let model = crate::providers::all::get_builtin_model(
            "amazon-bedrock",
            "global.anthropic.claude-opus-4-6-v1",
        )
        .expect("catalog model");
        let content = vec![
            AssistantContentBlock::Text(eukhe_types::pi_ai::TextContent::new("draft")),
            AssistantContentBlock::Text(eukhe_types::pi_ai::TextContent {
                cache_breakpoint: Some(eukhe_types::pi_ai::CacheBreakpoint::Ephemeral),
                ..eukhe_types::pi_ai::TextContent::new("answer")
            }),
        ];
        assert_eq!(
            (
                convert_assistant_content(&content, &model, true),
                convert_assistant_content(&content, &model, false),
            ),
            (
                vec![
                    json!({ "text": "draft" }),
                    json!({ "text": "answer" }),
                    json!({ "cachePoint": { "type": "default" } }),
                ],
                vec![json!({ "text": "draft" }), json!({ "text": "answer" })],
            )
        );
    }

    #[test]
    fn normalizes_tool_call_ids_like_the_ts_regex() {
        assert_eq!(normalize_tool_call_id("call|a.b"), "call_a_b");
        assert_eq!(normalize_tool_call_id("x😀"), "x__");
        assert_eq!(normalize_tool_call_id(&"a".repeat(70)).len(), 64);
    }

    #[test]
    fn decodes_base64_like_atob() {
        assert_eq!(
            base64_to_wire_bytes("A A E =").ok().as_deref(),
            Some("AAE=")
        );
        assert_eq!(base64_to_wire_bytes("AAE").ok().as_deref(), Some("AAE="));
        assert_eq!(
            base64_to_wire_bytes("!!").map_err(|error| error.to_string()),
            Err("Invalid character".to_owned())
        );
        assert_eq!(
            base64_to_wire_bytes("AAAAA").map_err(|error| error.to_string()),
            Err("The string to be decoded is not correctly encoded.".to_owned())
        );
    }

    #[test]
    fn maps_stop_reasons() {
        assert_eq!(map_stop_reason(Some("end_turn")), (StopReason::Stop, None));
        assert_eq!(
            map_stop_reason(Some("model_context_window_exceeded")),
            (StopReason::Length, None)
        );
        assert_eq!(
            map_stop_reason(Some("guardrail_intervened")),
            (
                StopReason::Error,
                Some("Provider stopped with: guardrail_intervened".to_owned())
            )
        );
        assert_eq!(map_stop_reason(None), (StopReason::Error, None));
    }
}
