//! Bedrock Converse request conversion: messages, system prompt, tool config,
//! and model-capability classification.
//! Port of the conversion section of
//! `packages/ai/src/providers/amazon-bedrock.ts`.

use base64::Engine as _;
use serde_json::{json, Map, Value};

use crate::models::clamp_thinking_level;
use crate::providers::cache_breakpoints::{has_cache_breakpoint, CacheMarkBudget};
use crate::providers::transform_messages::transform_messages_with_normalizer;
use crate::types::{
    AssistantContent, CacheRetention, Context, Message, Model, ModelThinkingLevel, Tool,
    UserMessageContent,
};
use crate::utils_inner::sanitize_unicode::sanitize_surrogates;

/// Port of `getModelMatchCandidates`.
fn get_model_match_candidates(model_id: &str, model_name: Option<&str>) -> Vec<String> {
    let mut values = vec![model_id.to_string()];
    if let Some(name) = model_name {
        values.push(name.to_string());
    }
    values
        .iter()
        .flat_map(|value| {
            let lower = value.to_lowercase();
            let dashed = lower.replace(
                |c: char| c.is_whitespace() || c == '_' || c == '.' || c == ':',
                "-",
            );
            [lower, dashed]
        })
        .collect()
}

/// Port of `supportsAdaptiveThinking` (Opus 4.6+, Sonnet 4.6).
pub fn supports_adaptive_thinking(model_id: &str, model_name: Option<&str>) -> bool {
    get_model_match_candidates(model_id, model_name)
        .iter()
        .any(|s| {
            s.contains("opus-4-6")
                || s.contains("opus-4-7")
                || s.contains("opus-4-8")
                || s.contains("opus-5")
                || s.contains("sonnet-4-6")
                || s.contains("sonnet-5")
                || s.contains("fable-5")
                || s.contains("mythos-5")
                || s.contains("mythos-preview")
        })
}

/// Port of `supportsAlwaysOnAdaptiveThinking`: Fable/Mythos models — and
/// Claude Opus 5.5 — think every turn and reject sampling params with a 400.
pub fn supports_always_on_adaptive_thinking(model_id: &str, model_name: Option<&str>) -> bool {
    get_model_match_candidates(model_id, model_name)
        .iter()
        .any(|s| {
            s.contains("fable-5")
                || s.contains("mythos-5")
                || s.contains("mythos-preview")
                || s.contains("opus-5-5")
                || s.contains("opus-5.5")
        })
}

/// Port of `isAnthropicClaudeModel`.
pub fn is_anthropic_claude_model(model: &Model) -> bool {
    let id = model.id.to_lowercase();
    let name = model.name.to_lowercase();
    id.contains("anthropic.claude")
        || id.contains("anthropic/claude")
        || name.contains("anthropic.claude")
        || name.contains("anthropic/claude")
        || name.contains("claude")
}

/// Port of `supportsPromptCaching`.
pub fn supports_prompt_caching(model: &Model) -> bool {
    let candidates = get_model_match_candidates(&model.id, Some(&model.name));
    let has_claude_ref = candidates.iter().any(|s| s.contains("claude"));
    if !has_claude_ref {
        // Application inference profiles don't contain the model name in the
        // ARN. Allow users to force cache points via environment variable.
        return std::env::var("AWS_BEDROCK_FORCE_CACHE").as_deref() == Ok("1");
    }
    candidates.iter().any(|s| {
        s.contains("-4-") || s.contains("claude-3-7-sonnet") || s.contains("claude-3-5-haiku")
    })
}

/// Port of `supportsThinkingSignature`.
pub fn supports_thinking_signature(model: &Model) -> bool {
    is_anthropic_claude_model(model)
}

/// Port of `normalizeToolCallId`: Bedrock tool-use IDs are `[a-zA-Z0-9_-]{1,64}`.
pub fn normalize_tool_call_id(id: &str) -> String {
    let sanitized: String = id
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '_' || c == '-' {
                c
            } else {
                '_'
            }
        })
        .collect();
    if sanitized.len() > 64 {
        sanitized[..64].to_string()
    } else {
        sanitized
    }
}

/// Port of `createImageBlock`: validates the mime type and passes the base64
/// bytes straight through (the AWS JSON protocol transmits blobs as base64).
fn create_image_block(mime_type: &str, data: &str) -> Value {
    let format = match mime_type {
        "image/jpeg" | "image/jpg" => "jpeg",
        "image/png" => "png",
        "image/gif" => "gif",
        "image/webp" => "webp",
        other => panic!("Unknown image type: {other}"),
    };
    // Fail fast on invalid base64 so the request never leaves with bad bytes.
    if base64::engine::general_purpose::STANDARD
        .decode(data)
        .is_err()
    {
        panic!("Invalid base64 image data for Bedrock image block");
    }
    json!({
        "format": format,
        "source": { "bytes": data },
    })
}

/// The request's cache point block: the default TTL, or one hour for long
/// retention.
fn cache_point(cache_retention: CacheRetention) -> Value {
    let mut point = Map::new();
    point.insert("type".into(), json!("default"));
    if cache_retention == CacheRetention::Long {
        point.insert("ttl".into(), json!("1h"));
    }
    json!({ "cachePoint": Value::Object(point) })
}

/// Port of `buildSystemPrompt`. The system cache point is the request's one
/// optional mark: it is kept only while `budget` has a slot left after the
/// message marks (the marked blocks and the end mark).
pub fn build_system_prompt(
    system_prompt: Option<&str>,
    model: &Model,
    cache_retention: CacheRetention,
    budget: &mut CacheMarkBudget,
) -> Option<Vec<Value>> {
    let system_prompt = system_prompt?;
    let mut blocks = vec![json!({ "text": sanitize_surrogates(system_prompt) })];

    if cache_retention != CacheRetention::None && supports_prompt_caching(model) && budget.take() {
        blocks.push(cache_point(cache_retention));
    }

    Some(blocks)
}

/// Port of `convertMessages`. When prompt caching is on, a cache point
/// follows each marked user text block.
// Long by design (a 1:1 port of the upstream provider shape); refactoring is out of scope for the zero-behavior pedantic sweep.
#[allow(clippy::too_many_lines)]
pub fn convert_messages(
    context: &Context,
    model: &Model,
    cache_retention: CacheRetention,
) -> Vec<Value> {
    let mut result: Vec<Value> = Vec::new();
    let transformed = transform_messages_with_normalizer(&context.messages, model, &|id, _, _| {
        Some(normalize_tool_call_id(id))
    });
    let caching = cache_retention != CacheRetention::None && supports_prompt_caching(model);

    let mut i = 0usize;
    while i < transformed.len() {
        match &transformed[i] {
            Message::User(user) => {
                let content_blocks: Vec<Value> = match &user.content {
                    UserMessageContent::Text(text) => {
                        vec![json!({ "text": sanitize_surrogates(text) })]
                    }
                    UserMessageContent::Blocks(blocks) => {
                        let mut converted = Vec::with_capacity(blocks.len());
                        for c in blocks {
                            converted.push(match crate::types::user_block_payload(c) {
                                crate::types::UserBlockPayload::Text(text) => {
                                    json!({ "text": sanitize_surrogates(text) })
                                }
                                crate::types::UserBlockPayload::Image { data, mime_type } => {
                                    json!({ "image": create_image_block(mime_type, data) })
                                }
                                crate::types::UserBlockPayload::Opaque(json) => {
                                    json!({ "text": sanitize_surrogates(&json) })
                                }
                            });
                            // A marked block ends a cacheable prefix (the chat
                            // memory marks the pieces of its view).
                            if caching && has_cache_breakpoint(c) {
                                converted.push(cache_point(cache_retention));
                            }
                        }
                        converted
                    }
                };
                result.push(json!({ "role": "user", "content": content_blocks }));
                i += 1;
            }
            Message::Assistant(assistant) => {
                // Bedrock rejects messages with empty content arrays.
                if assistant.content.is_empty() {
                    i += 1;
                    continue;
                }
                let mut content_blocks: Vec<Value> = Vec::new();
                for c in &assistant.content {
                    match c {
                        AssistantContent::Text(text) => {
                            if !text.text.trim().is_empty() {
                                content_blocks
                                    .push(json!({ "text": sanitize_surrogates(&text.text) }));
                            }
                        }
                        AssistantContent::ToolCall(call) => {
                            content_blocks.push(json!({
                                "toolUse": {
                                    "toolUseId": call.id,
                                    "name": call.name,
                                    "input": call.arguments,
                                }
                            }));
                        }
                        AssistantContent::Thinking(thinking) => {
                            if thinking.thinking.trim().is_empty() {
                                continue;
                            }
                            // Only Anthropic models support the signature field
                            // in reasoningText. For other models we omit it to
                            // avoid: "This model doesn't support the
                            // reasoningContent.reasoningText.signature field".
                            if supports_thinking_signature(model) {
                                // Signatures arrive after thinking deltas. If a
                                // partial or externally persisted message lacks
                                // a signature, Bedrock rejects the replayed
                                // reasoning block. Fall back to plain text,
                                // matching Anthropic.
                                let signature = thinking
                                    .thinking_signature
                                    .as_deref()
                                    .filter(|signature| !signature.trim().is_empty());
                                match signature {
                                    None => {
                                        content_blocks.push(json!({
                                            "text": sanitize_surrogates(&thinking.thinking)
                                        }));
                                    }
                                    Some(signature) => {
                                        content_blocks.push(json!({
                                            "reasoningContent": {
                                                "reasoningText": {
                                                    "text": sanitize_surrogates(&thinking.thinking),
                                                    "signature": signature,
                                                }
                                            }
                                        }));
                                    }
                                }
                            } else {
                                content_blocks.push(json!({
                                    "reasoningContent": {
                                        "reasoningText": { "text": sanitize_surrogates(&thinking.thinking) }
                                    }
                                }));
                            }
                        }
                    }
                }
                if !content_blocks.is_empty() {
                    result.push(json!({ "role": "assistant", "content": content_blocks }));
                }
                i += 1;
            }
            Message::ToolResult(_) => {
                // Collect all consecutive toolResult messages into a single
                // user message: Bedrock requires all tool results in one message.
                let mut tool_results: Vec<Value> = Vec::new();
                let mut j = i;
                while j < transformed.len() {
                    let Message::ToolResult(current) = &transformed[j] else {
                        break;
                    };
                    tool_results.push(json!({
                        "toolResult": {
                            "toolUseId": current.tool_call_id,
                            "content": current.content.iter().map(|c| match crate::types::user_block_payload(c) {
                                crate::types::UserBlockPayload::Text(text) => {
                                    json!({ "text": sanitize_surrogates(text) })
                                }
                                crate::types::UserBlockPayload::Image { data, mime_type } => {
                                    json!({ "image": create_image_block(mime_type, data) })
                                }
                                crate::types::UserBlockPayload::Opaque(json) => {
                                    json!({ "text": sanitize_surrogates(&json) })
                                }
                            }).collect::<Vec<Value>>(),
                            "status": if current.is_error { "error" } else { "success" },
                        }
                    }));
                    j += 1;
                }
                i = j;
                result.push(json!({ "role": "user", "content": tool_results }));
            }
        }
    }

    // Add a cache point to the last user message for supported Claude models
    // when caching is enabled. A marked last block already ends with one.
    if caching && !result.is_empty() {
        let last = result.last_mut().expect("checked non-empty");
        if last.get("role").and_then(Value::as_str) == Some("user") {
            let last_blocks = last
                .get_mut("content")
                .and_then(Value::as_array_mut)
                .expect("user messages always carry content");
            if last_blocks
                .last()
                .and_then(|block| block.get("cachePoint"))
                .is_none()
            {
                last_blocks.push(cache_point(cache_retention));
            }
        }
    }

    result
}

/// Port of `convertToolConfig`.
pub fn convert_tool_config(
    tools: Option<&[Tool]>,
    tool_choice: Option<&BedrockToolChoice>,
) -> Option<Value> {
    let tools = tools?;
    if tools.is_empty() {
        return None;
    }
    if matches!(tool_choice, Some(BedrockToolChoice::None)) {
        return None;
    }

    let bedrock_tools: Vec<Value> = tools
        .iter()
        .map(|tool| {
            json!({
                "toolSpec": {
                    "name": tool.name,
                    "description": tool.description,
                    "inputSchema": { "json": tool.parameters },
                }
            })
        })
        .collect();

    let bedrock_tool_choice = match tool_choice {
        Some(BedrockToolChoice::Auto) => Some(json!({ "auto": {} })),
        Some(BedrockToolChoice::Any) => Some(json!({ "any": {} })),
        Some(BedrockToolChoice::Tool { name }) => Some(json!({ "tool": { "name": name } })),
        _ => None,
    };

    let mut config = Map::new();
    config.insert("tools".into(), Value::Array(bedrock_tools));
    if let Some(choice) = bedrock_tool_choice {
        config.insert("toolChoice".into(), choice);
    }
    Some(Value::Object(config))
}

/// Tool selection (`toolChoice` in the TS reference).
#[allow(dead_code)] // full TS option surface; variants set by callers
#[derive(Clone, Debug, PartialEq)]
pub enum BedrockToolChoice {
    Auto,
    Any,
    None,
    Tool { name: String },
}

/// Port of `mapThinkingLevelToEffort`.
pub fn map_thinking_level_to_effort(model: &Model, level: ModelThinkingLevel) -> &'static str {
    // Clamp to what the model actually supports so callers that bypass
    // clampThinkingLevel can't send an effort the model lacks.
    let effective = clamp_thinking_level(model, level);
    let mapped = model
        .thinking_level_map
        .as_ref()
        .and_then(|map| map.get(&effective))
        .and_then(std::clone::Clone::clone);
    match mapped.as_deref() {
        Some("low") => return "low",
        Some("medium") => return "medium",
        Some("high") => return "high",
        Some("xhigh") => return "xhigh",
        Some("max") => return "max",
        _ => {}
    }
    match effective {
        ModelThinkingLevel::Minimal | ModelThinkingLevel::Low => "low",
        ModelThinkingLevel::Medium => "medium",
        ModelThinkingLevel::High | ModelThinkingLevel::Off => "high",
        ModelThinkingLevel::Xhigh => "xhigh",
        ModelThinkingLevel::Max => "max",
    }
}

/// Port of `mapStopReason`.
pub fn map_stop_reason(reason: Option<&str>) -> crate::types::StopReason {
    use crate::types::StopReason;
    match reason {
        Some("end_turn" | "stop_sequence") => StopReason::Stop,
        Some("max_tokens" | "model_context_window_exceeded") => StopReason::Length,
        Some("tool_use") => StopReason::ToolUse,
        _ => StopReason::Error,
    }
}

#[cfg(test)]
mod supports_always_on_adaptive_thinking_tests {
    use super::supports_always_on_adaptive_thinking;

    #[test]
    fn bedrock_always_on_models_reject_sampling_params() {
        assert!(supports_always_on_adaptive_thinking(
            "us.anthropic.claude-opus-5-5-v1",
            Some("Claude Opus 5.5")
        ));
        assert!(supports_always_on_adaptive_thinking(
            "anthropic.claude-fable-5",
            None
        ));
    }

    #[test]
    fn bedrock_optional_thinking_models_keep_sampling_params() {
        assert!(!supports_always_on_adaptive_thinking(
            "us.anthropic.claude-opus-5-v1",
            Some("Claude Opus 5")
        ));
    }
}
