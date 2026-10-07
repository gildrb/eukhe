//! Port of `api/transform-messages.ts`: cross-model transcript replay
//! normalization shared by the wire APIs.

use std::collections::{HashMap, HashSet};

use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, Message, Modality, Model, StopReason, TextContent,
    ToolCall, ToolResultMessage, UserContent, UserContentBlock,
};

const NON_VISION_USER_IMAGE_PLACEHOLDER: &str = "(image omitted: model does not support images)";
const NON_VISION_TOOL_IMAGE_PLACEHOLDER: &str =
    "(tool image omitted: model does not support images)";

/// TS `normalizeToolCallId?: (id, model, source) => string`.
pub type NormalizeToolCallId<'a> = &'a dyn Fn(&str, &Model, &AssistantMessage) -> String;

fn replace_images_with_placeholder(
    content: &[UserContentBlock],
    placeholder: &str,
) -> Vec<UserContentBlock> {
    let mut result = Vec::with_capacity(content.len());
    let mut previous_was_placeholder = false;
    for block in content {
        match block {
            UserContentBlock::Image(_) => {
                if !previous_was_placeholder {
                    result.push(UserContentBlock::Text(TextContent::new(placeholder)));
                }
                previous_was_placeholder = true;
            }
            UserContentBlock::Text(text) => {
                previous_was_placeholder = text.text == placeholder;
                result.push(block.clone());
            }
        }
    }
    result
}

fn downgrade_unsupported_images(messages: &[Message], model: &Model) -> Vec<Message> {
    if model.input.contains(&Modality::Image) {
        return messages.to_vec();
    }
    messages
        .iter()
        .map(|message| match message {
            Message::User(user) => match &user.content {
                UserContent::Blocks(blocks) => {
                    let mut user = user.clone();
                    user.content = UserContent::Blocks(replace_images_with_placeholder(
                        blocks,
                        NON_VISION_USER_IMAGE_PLACEHOLDER,
                    ));
                    Message::User(user)
                }
                UserContent::Text(_) => message.clone(),
            },
            Message::ToolResult(result) => {
                let mut result = result.clone();
                result.content = replace_images_with_placeholder(
                    &result.content,
                    NON_VISION_TOOL_IMAGE_PLACEHOLDER,
                );
                Message::ToolResult(result)
            }
            Message::System(_) | Message::Assistant(_) => message.clone(),
        })
        .collect()
}

fn transform_assistant(
    assistant: &AssistantMessage,
    model: &Model,
    normalize_tool_call_id: Option<NormalizeToolCallId<'_>>,
    tool_call_id_map: &mut HashMap<String, String>,
) -> AssistantMessage {
    let is_same_model = assistant.provider == model.provider
        && assistant.api == model.api
        && assistant.model == model.id;

    let content = assistant
        .content
        .iter()
        .filter_map(|block| match block {
            AssistantContentBlock::Thinking(thinking) => {
                // Redacted thinking is opaque encrypted content, only valid for the same model.
                if thinking.redacted == Some(true) {
                    return is_same_model.then(|| block.clone());
                }
                // Same model: keep signed thinking (needed for replay) even when empty.
                if is_same_model
                    && thinking
                        .thinking_signature
                        .as_deref()
                        .is_some_and(|s| !s.is_empty())
                {
                    return Some(block.clone());
                }
                if crate::utils::js::js_trim(&thinking.thinking).is_empty() {
                    return None;
                }
                if is_same_model {
                    return Some(block.clone());
                }
                Some(AssistantContentBlock::Text(TextContent::new(
                    thinking.thinking.clone(),
                )))
            }
            AssistantContentBlock::Text(text) => {
                if is_same_model {
                    return Some(block.clone());
                }
                Some(AssistantContentBlock::Text(TextContent::new(
                    text.text.clone(),
                )))
            }
            AssistantContentBlock::ToolCall(tool_call) => {
                let mut normalized = tool_call.clone();
                if !is_same_model {
                    if normalized
                        .thought_signature
                        .as_deref()
                        .is_some_and(|s| !s.is_empty())
                    {
                        normalized.thought_signature = None;
                    }
                    if let Some(normalize) = normalize_tool_call_id {
                        let normalized_id = normalize(&tool_call.id, model, assistant);
                        if normalized_id != tool_call.id {
                            tool_call_id_map.insert(tool_call.id.clone(), normalized_id.clone());
                            normalized.id = normalized_id;
                        }
                    }
                }
                Some(AssistantContentBlock::ToolCall(normalized))
            }
        })
        .collect();

    let mut transformed = assistant.clone();
    transformed.content = content;
    transformed
}

/// Normalize a transcript for replay to `model`: downgrade images for
/// non-vision models, convert or drop cross-model thinking, normalize tool
/// call IDs, skip errored/aborted assistant turns, and synthesize
/// `"No result provided"` results for orphaned tool calls.
///
/// `OpenAI` Responses generates IDs that are 450+ chars with special
/// characters like `|`; Anthropic requires `^[a-zA-Z0-9_-]+$` (max 64
/// chars), hence `normalize_tool_call_id`.
///
/// TS also maps `null` content to `[]` here; in Rust lax deserialization of
/// the message types already does that.
#[must_use]
pub fn transform_messages(
    messages: &[Message],
    model: &Model,
    normalize_tool_call_id: Option<NormalizeToolCallId<'_>>,
) -> Vec<Message> {
    let mut tool_call_id_map: HashMap<String, String> = HashMap::new();
    let image_aware = downgrade_unsupported_images(messages, model);

    // First pass: thinking blocks and tool call ID normalization.
    let transformed: Vec<Message> = image_aware
        .into_iter()
        .map(|message| match message {
            Message::System(_) | Message::User(_) => message,
            Message::ToolResult(mut result) => {
                if let Some(normalized) = tool_call_id_map.get(&result.tool_call_id) {
                    if !normalized.is_empty() && *normalized != result.tool_call_id {
                        result.tool_call_id.clone_from(normalized);
                    }
                }
                Message::ToolResult(result)
            }
            Message::Assistant(assistant) => Message::Assistant(transform_assistant(
                &assistant,
                model,
                normalize_tool_call_id,
                &mut tool_call_id_map,
            )),
        })
        .collect();

    // Second pass: synthetic results for orphaned tool calls. System messages
    // between a tool call and its results are held back until after the
    // results so they never cause a duplicate result.
    let mut pass = SecondPass::default();
    for message in transformed {
        match message {
            Message::Assistant(assistant) => {
                pass.close_pending_tool_calls();
                // Skip errored/aborted turns: incomplete and unsafe to replay.
                if matches!(
                    assistant.stop_reason,
                    StopReason::Error | StopReason::Aborted
                ) {
                    continue;
                }
                let tool_calls: Vec<ToolCall> = assistant
                    .content
                    .iter()
                    .filter_map(|block| match block {
                        AssistantContentBlock::ToolCall(call) => Some(call.clone()),
                        AssistantContentBlock::Text(_) | AssistantContentBlock::Thinking(_) => None,
                    })
                    .collect();
                if !tool_calls.is_empty() {
                    pass.pending_tool_calls = tool_calls;
                    pass.existing_tool_result_ids = HashSet::new();
                }
                pass.result.push(Message::Assistant(assistant));
            }
            Message::ToolResult(result) => {
                pass.existing_tool_result_ids
                    .insert(result.tool_call_id.clone());
                pass.result.push(Message::ToolResult(result));
            }
            Message::System(system) => {
                if pass.pending_tool_calls.is_empty() {
                    pass.result.push(Message::System(system));
                } else {
                    pass.held_system_messages.push(Message::System(system));
                }
            }
            Message::User(user) => {
                pass.close_pending_tool_calls();
                pass.result.push(Message::User(user));
            }
        }
    }
    pass.close_pending_tool_calls();
    pass.result
}

#[derive(Default)]
struct SecondPass {
    result: Vec<Message>,
    pending_tool_calls: Vec<ToolCall>,
    existing_tool_result_ids: HashSet<String>,
    held_system_messages: Vec<Message>,
}

impl SecondPass {
    fn close_pending_tool_calls(&mut self) {
        if !self.pending_tool_calls.is_empty() {
            for call in std::mem::take(&mut self.pending_tool_calls) {
                if !self.existing_tool_result_ids.contains(&call.id) {
                    self.result.push(Message::ToolResult(ToolResultMessage {
                        tool_call_id: call.id,
                        tool_name: call.name,
                        content: vec![UserContentBlock::Text(TextContent::new(
                            "No result provided",
                        ))],
                        details: None,
                        usage: None,
                        nested_calls: None,
                        is_error: true,
                        timestamp: crate::utils::now_ms(),
                    }));
                }
            }
            self.existing_tool_result_ids = HashSet::new();
        }
        self.result.append(&mut self.held_system_messages);
    }
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    /// Text-only model so the image downgrade path runs (the primary crash
    /// site for null tool result content).
    fn make_text_only_model() -> Model {
        serde_json::from_value(json!({
            "id": "test-model",
            "name": "Test Model",
            "api": "openai-completions",
            "provider": "openai",
            "baseUrl": "https://example.invalid/v1",
            "reasoning": false,
            "input": ["text"],
            "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
            "contextWindow": 128_000,
            "maxTokens": 16000,
        }))
        .expect("model")
    }

    /// Port of `lax-message-content.test.ts` (the transform half; lax
    /// deserialization itself is tested in `eukhe_types::pi_ai`).
    #[test]
    fn normalizes_null_missing_content_to_an_empty_array_instead_of_crashing() {
        let messages: Vec<Message> = serde_json::from_value(json!([
            { "role": "user", "content": null, "timestamp": 1 },
            {
                "role": "assistant",
                "content": null,
                "api": "openai-completions",
                "provider": "openai",
                "model": "test-model",
                "usage": {
                    "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
                    "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
                },
                "stopReason": "stop",
                "timestamp": 1,
            },
            {
                "role": "toolResult",
                "toolCallId": "call_1",
                "toolName": "web_search",
                "isError": false,
                "timestamp": 1,
            },
        ]))
        .expect("messages");

        let result = transform_messages(&messages, &make_text_only_model(), None);

        assert_eq!(result.len(), 3);
        for message in &result {
            assert_eq!(
                serde_json::to_value(message).expect("message")["content"],
                json!([])
            );
        }
    }
}
