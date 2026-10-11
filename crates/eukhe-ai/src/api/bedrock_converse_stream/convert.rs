//! Converse request building: messages, system prompt, tool configuration,
//! additional model request fields, and the model-capability checks behind
//! them. Section of the port of `api/bedrock-converse-stream.ts`.

use std::sync::LazyLock;

use base64::engine::general_purpose::{GeneralPurpose, GeneralPurposeConfig, STANDARD};
use base64::engine::DecodePaddingMode;
use base64::Engine as _;
use eukhe_types::pi_ai::{
    AssistantContentBlock, CacheRetention, JsonObject, JsonValue, Message, Model,
    ModelThinkingLevel, ProviderEnv, StopReason, ThinkingLevel, Tool, UserContent,
    UserContentBlock,
};
use regex::Regex;
use serde_json::json;

use super::client_config::get_configured_bedrock_region;
use super::{BedrockOptions, BedrockThinkingDisplay, BedrockToolChoice};
use crate::api::cache_breakpoints::{has_cache_breakpoint, CacheMarkBudget};
use crate::api::constrained_sampling::{
    get_json_schema_tool_parameters, resolve_json_schema_strict_sampling, ConstrainedSamplingError,
    StrictToolParameters,
};
use crate::api::simple_options::clamp_reasoning;
use crate::api::transform_messages::transform_messages;
use crate::utils::diagnostics::{ErrorObject, Thrown};
use crate::utils::js::js_trim;
use crate::utils::provider_env::get_provider_env_value;
use crate::utils::sanitize_unicode::sanitize_surrogates;
use crate::utils::transcript::without_initial_system_message;

const EMPTY_TEXT_PLACEHOLDER: &str = "<empty>";

const THINKING_BINDING_CONTROLS_BETA: &str = "thinking-binding-controls-2026-08-01";

/// `/[\s_.:]+/g`.
static SEPARATORS: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"[\s_.:]+").unwrap_or_else(|_| unreachable!("static regex")));

/// TS `getModelMatchCandidates`: the lowercased id (and name), each also
/// with separator runs replaced by `-`.
fn get_model_match_candidates(model_id: &str, model_name: &str) -> Vec<String> {
    let values: &[&str] = if model_name.is_empty() {
        &[model_id]
    } else {
        &[model_id, model_name]
    };
    values
        .iter()
        .flat_map(|value| {
            let lower = value.to_lowercase();
            let dashed = SEPARATORS.replace_all(&lower, "-").into_owned();
            [lower, dashed]
        })
        .collect()
}

fn any_candidate(model_id: &str, model_name: &str, needles: &[&str]) -> bool {
    get_model_match_candidates(model_id, model_name)
        .iter()
        .any(|candidate| needles.iter().any(|needle| candidate.contains(needle)))
}

/// TS `supportsAdaptiveThinking` (Opus 4.6+, Sonnet 4.6+, Fable 5).
pub(crate) fn supports_adaptive_thinking(model_id: &str, model_name: &str) -> bool {
    any_candidate(
        model_id,
        model_name,
        &[
            "opus-4-6",
            "opus-4-7",
            "opus-4-8",
            "opus-5",
            "sonnet-4-6",
            "sonnet-5",
            "haiku-5",
            "fable-5",
        ],
    )
}

/// TS `supportsNativeXhighEffort`.
fn supports_native_xhigh_effort(model: &Model) -> bool {
    any_candidate(
        &model.id,
        &model.name,
        &[
            "opus-4-7", "opus-4-8", "opus-5", "sonnet-5", "haiku-5", "fable-5",
        ],
    )
}

/// TS `supportsThinkingBlockBinding`: Opus 4.6 and Sonnet 4.6 reject
/// `thinking.block_binding`.
fn supports_thinking_block_binding(model: &Model) -> bool {
    any_candidate(
        &model.id,
        &model.name,
        &[
            "opus-4-7", "opus-4-8", "opus-5", "sonnet-5", "haiku-5", "fable-5",
        ],
    )
}

/// TS `mapThinkingLevelToEffort`.
fn map_thinking_level_to_effort(model: &Model, level: ThinkingLevel) -> String {
    if level == ThinkingLevel::Xhigh && supports_native_xhigh_effort(model) {
        return "xhigh".to_owned();
    }
    let mapped = model
        .thinking_level_map
        .as_ref()
        .and_then(|map| map.get(&ModelThinkingLevel::from(level)))
        .and_then(Option::as_ref);
    if let Some(mapped) = mapped {
        return mapped.clone();
    }
    match level {
        ThinkingLevel::Minimal | ThinkingLevel::Low => "low",
        ThinkingLevel::Medium => "medium",
        ThinkingLevel::High | ThinkingLevel::Xhigh | ThinkingLevel::Max => "high",
    }
    .to_owned()
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

/// TS `isAnthropicClaudeModel`: checks the id and the name (application
/// inference profile ARNs don't contain the model name).
pub(crate) fn is_anthropic_claude_model(model: &Model) -> bool {
    let id = model.id.to_lowercase();
    let name = model.name.to_lowercase();
    id.contains("anthropic.claude")
        || id.contains("anthropic/claude")
        || name.contains("anthropic.claude")
        || name.contains("anthropic/claude")
        || name.contains("claude")
}

/// TS `supportsPromptCaching`: Claude 3.5 Haiku, 3.7 Sonnet, 4.x, 5; any
/// model with `AWS_BEDROCK_FORCE_CACHE=1` when the id/name names no Claude.
pub(crate) fn supports_prompt_caching(model: &Model, env: Option<&ProviderEnv>) -> bool {
    let candidates = get_model_match_candidates(&model.id, &model.name);
    let any = |needle: &str| {
        candidates
            .iter()
            .any(|candidate| candidate.contains(needle))
    };
    if !any("claude") {
        return get_provider_env_value("AWS_BEDROCK_FORCE_CACHE", env).as_deref() == Some("1");
    }
    any("fable-5")
        || any("opus-5")
        || any("sonnet-5")
        || any("haiku-5")
        || any("-4-")
        || any("claude-3-7-sonnet")
        || any("claude-3-5-haiku")
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
/// cache point is optional and takes a mark slot only while `budget` has one
/// left after the message marks.
pub(crate) fn build_system_prompt(
    system_prompt: Option<&str>,
    model: &Model,
    cache_retention: CacheRetention,
    env: Option<&ProviderEnv>,
    budget: &mut CacheMarkBudget,
) -> Option<Vec<JsonValue>> {
    let system_prompt = system_prompt.filter(|prompt| !prompt.is_empty())?;
    let mut blocks = vec![json!({ "text": sanitize_surrogates(system_prompt) })];
    if cache_retention != CacheRetention::None
        && supports_prompt_caching(model, env)
        && budget.take()
    {
        blocks.push(cache_point(cache_retention));
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

/// TS `convertToolResultContent`.
fn convert_tool_result_content(content: &[UserContentBlock]) -> Result<Vec<JsonValue>, Thrown> {
    let mut result = Vec::new();
    for block in content {
        match block {
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
fn convert_assistant_content(content: &[AssistantContentBlock], model: &Model) -> Vec<JsonValue> {
    let mut blocks = Vec::new();
    for block in content {
        match block {
            AssistantContentBlock::Text(text) => {
                if let Some(text_block) = create_non_blank_text_block(&text.text) {
                    blocks.push(text_block);
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
                    let content = convert_assistant_content(&assistant.content, model);
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
                            "content": convert_tool_result_content(&next.content)?,
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
    supports_strict_mode: bool,
) -> Result<Option<JsonValue>, ConstrainedSamplingError> {
    if tools.is_empty() || tool_choice == Some(&BedrockToolChoice::None) {
        return Ok(None);
    }
    let mut bedrock_tools = Vec::with_capacity(tools.len());
    for tool in tools {
        let strict = resolve_json_schema_strict_sampling(tool, supports_strict_mode, None)?;
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
    if !is_anthropic_claude_model(model) {
        return build_openai_reasoning_fields(model, reasoning);
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
    let adaptive = supports_adaptive_thinking(&model.id, &model.name);
    let mut result = JsonObject::new();
    if adaptive {
        let use_block_binding = !is_gov_cloud && supports_thinking_block_binding(model);
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
        let default_budget: u64 = match reasoning {
            ThinkingLevel::Minimal => 1024,
            ThinkingLevel::Low => 2048,
            ThinkingLevel::Medium => 8192,
            // Budget-based Claude clamps extended levels to high.
            ThinkingLevel::High | ThinkingLevel::Xhigh | ThinkingLevel::Max => 16384,
        };
        // Custom budgets only cover token-based levels through high.
        let custom = options.thinking_budgets.as_ref().and_then(|budgets| {
            match clamp_reasoning(Some(reasoning)) {
                Some(ThinkingLevel::Minimal) => budgets.minimal,
                Some(ThinkingLevel::Low) => budgets.low,
                Some(ThinkingLevel::Medium) => budgets.medium,
                Some(ThinkingLevel::High | ThinkingLevel::Xhigh | ThinkingLevel::Max) | None => {
                    budgets.high
                }
            }
        });
        let mut thinking = JsonObject::new();
        thinking.insert("type".to_owned(), "enabled".into());
        thinking.insert(
            "budget_tokens".to_owned(),
            custom.unwrap_or(default_budget).into(),
        );
        if let Some(display) = display {
            thinking.insert("display".to_owned(), display.as_str().into());
        }
        result.insert("thinking".to_owned(), JsonValue::Object(thinking));
        if options.interleaved_thinking.unwrap_or(true) {
            result.insert(
                "anthropic_beta".to_owned(),
                json!(["interleaved-thinking-2025-05-14"]),
            );
        }
    }
    Some(JsonValue::Object(result))
}

/// The non-Claude tail of TS `buildAdditionalModelRequestFields`: `OpenAI`
/// GPT models (GPT-5.x, GPT-6) take a nested `reasoning.effort` and reject
/// `minimal`; gpt-oss takes a flat `reasoning_effort` and only accepts low,
/// medium and high.
fn build_openai_reasoning_fields(model: &Model, reasoning: ThinkingLevel) -> Option<JsonValue> {
    let candidates = get_model_match_candidates(&model.id, &model.name);
    if candidates
        .iter()
        .any(|candidate| candidate.contains("gpt-oss"))
    {
        // TS `OPENAI_GPT_OSS_EFFORT`.
        let effort = match reasoning {
            ThinkingLevel::Minimal | ThinkingLevel::Low => "low",
            ThinkingLevel::Medium => "medium",
            ThinkingLevel::High | ThinkingLevel::Xhigh | ThinkingLevel::Max => "high",
        };
        return Some(json!({ "reasoning_effort": effort }));
    }
    if candidates
        .iter()
        .any(|candidate| candidate.contains("gpt-"))
    {
        let mapped = model
            .thinking_level_map
            .as_ref()
            .and_then(|map| map.get(&ModelThinkingLevel::from(reasoning)))
            .and_then(Option::as_ref);
        // TS `OPENAI_GPT_EFFORT`.
        let effort = mapped.map_or_else(
            || {
                match reasoning {
                    ThinkingLevel::Minimal | ThinkingLevel::Low => "low",
                    ThinkingLevel::Medium => "medium",
                    ThinkingLevel::High => "high",
                    ThinkingLevel::Xhigh => "xhigh",
                    ThinkingLevel::Max => "max",
                }
                .to_owned()
            },
            Clone::clone,
        );
        return Some(json!({ "reasoning": { "effort": effort } }));
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

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
