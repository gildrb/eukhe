//! Character-based context token estimation (4 chars per token).

use eukhe_types::pi_ai::{
    AssistantContentBlock, Message, StopReason, Usage, UserContent, UserContentBlock,
};

use super::js::{json_stringify, utf16_len};
use super::text::get_system_message_text;

/// Estimated context size.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ContextUsageEstimate {
    /// Estimated total context tokens.
    pub tokens: u64,
    /// Tokens reported by the most recent applicable assistant usage block.
    pub usage_tokens: u64,
    /// Estimated tokens after the most recent applicable assistant usage block.
    pub trailing_tokens: u64,
    /// Index of the applicable message that provided usage, if any.
    pub last_usage_index: Option<usize>,
}

const CHARS_PER_TOKEN: u64 = 4;
const ESTIMATED_IMAGE_CHARS: u64 = 4800;

/// Context tokens a usage block describes: `total_tokens`, or the sum of its parts when zero.
#[must_use]
pub fn calculate_context_tokens(usage: &Usage) -> u64 {
    if usage.total_tokens != 0 {
        return usage.total_tokens;
    }
    usage.input + usage.output + usage.cache_read + usage.cache_write
}

/// `Math.ceil(chars / CHARS_PER_TOKEN)`.
const fn chars_to_tokens(chars: u64) -> u64 {
    chars.div_ceil(CHARS_PER_TOKEN)
}

fn length(text: &str) -> u64 {
    utf16_len(text) as u64
}

fn estimate_blocks_chars(blocks: &[UserContentBlock]) -> u64 {
    blocks
        .iter()
        .map(|block| match block {
            UserContentBlock::Text(text) => length(&text.text),
            UserContentBlock::Image(_) => ESTIMATED_IMAGE_CHARS,
        })
        .sum()
}

/// Estimated tokens of a text.
#[must_use]
pub fn estimate_text_tokens(text: &str) -> u64 {
    chars_to_tokens(length(text))
}

/// Estimated tokens of user/tool-result content (images count 4800 chars).
#[must_use]
pub fn estimate_text_and_image_content_tokens(content: &UserContent) -> u64 {
    match content {
        UserContent::Text(text) => estimate_text_tokens(text),
        UserContent::Blocks(blocks) => chars_to_tokens(estimate_blocks_chars(blocks)),
    }
}

/// Estimated tokens of a tool-result content block list.
fn estimate_blocks_tokens(blocks: &[UserContentBlock]) -> u64 {
    chars_to_tokens(estimate_blocks_chars(blocks))
}

/// `JSON.stringify(value)` of a serializable value.
fn stringify<T: serde::Serialize>(value: &T) -> String {
    // Transcript types always serialize (string keys, finite numbers); the
    // TS fallback for unserializable values is `[unserializable]`.
    serde_json::to_value(value).map_or_else(
        |_| "[unserializable]".to_owned(),
        |value| json_stringify(&value),
    )
}

fn estimate_tools_tokens<T: serde::Serialize>(tools: Option<&Vec<T>>) -> u64 {
    match tools {
        Some(tools) if !tools.is_empty() => estimate_text_tokens(&stringify(tools)),
        Some(_) | None => 0,
    }
}

/// Estimated tokens of one message.
#[must_use]
pub fn estimate_message_tokens(message: &Message) -> u64 {
    match message {
        Message::System(system) => {
            estimate_text_tokens(&get_system_message_text(system))
                + estimate_tools_tokens(system.tools_added.as_ref())
                + estimate_tools_tokens(system.tools_removed.as_ref())
        }
        Message::User(user) => estimate_text_and_image_content_tokens(&user.content),
        Message::ToolResult(result) => estimate_blocks_tokens(&result.content),
        Message::Assistant(assistant) => {
            let chars: u64 = assistant
                .content
                .iter()
                .map(|block| match block {
                    AssistantContentBlock::Text(text) => length(&text.text),
                    AssistantContentBlock::Thinking(thinking) => length(&thinking.thinking),
                    AssistantContentBlock::ToolCall(call) => {
                        length(&call.name) + length(&stringify(&call.arguments))
                    }
                })
                .sum();
            chars_to_tokens(chars)
        }
    }
}

/// The last assistant usage that still describes the transcript prefix.
fn get_last_assistant_usage_info(messages: &[Message]) -> Option<(&Usage, usize)> {
    let mut latest_prefix_timestamp: Option<u64> = None;
    let mut usage_info = None;
    for (index, message) in messages.iter().enumerate() {
        if let Message::Assistant(assistant) = message {
            // A newer prefix message was inserted after this response (for
            // example a compaction summary), so its usage cannot describe the
            // current prefix.
            let usage_applies_to_prefix =
                latest_prefix_timestamp.is_none_or(|latest| assistant.timestamp >= latest);
            if usage_applies_to_prefix
                && assistant.stop_reason != StopReason::Aborted
                && assistant.stop_reason != StopReason::Error
                && calculate_context_tokens(&assistant.usage) > 0
            {
                usage_info = Some((&assistant.usage, index));
            }
        }
        let timestamp = message.timestamp();
        latest_prefix_timestamp =
            Some(latest_prefix_timestamp.map_or(timestamp, |latest| latest.max(timestamp)));
    }
    usage_info
}

/// Estimate the context size of a transcript (pass `TranscriptContext::messages()`
/// for a normalized context): the last applicable assistant usage plus
/// estimates of the messages after it, or estimates of every message.
#[must_use]
pub fn estimate_context_tokens(messages: &[Message]) -> ContextUsageEstimate {
    if let Some((usage, index)) = get_last_assistant_usage_info(messages) {
        let usage_tokens = calculate_context_tokens(usage);
        let trailing_tokens: u64 = messages[index + 1..]
            .iter()
            .map(estimate_message_tokens)
            .sum();
        return ContextUsageEstimate {
            tokens: usage_tokens + trailing_tokens,
            usage_tokens,
            trailing_tokens,
            last_usage_index: Some(index),
        };
    }
    let tokens: u64 = messages.iter().map(estimate_message_tokens).sum();
    ContextUsageEstimate {
        tokens,
        usage_tokens: 0,
        trailing_tokens: tokens,
        last_usage_index: None,
    }
}

#[cfg(test)]
mod tests {
    use eukhe_types::pi_ai::{AssistantMessage, Context, TextContent, UserMessage};

    use super::*;
    use crate::utils::transcript::normalize_context;

    fn create_usage(total_tokens: u64) -> Usage {
        Usage {
            input: total_tokens,
            total_tokens,
            ..Usage::default()
        }
    }

    fn create_assistant(timestamp: u64, total_tokens: u64) -> Message {
        Message::Assistant(AssistantMessage {
            content: vec![AssistantContentBlock::Text(TextContent::new("kept"))],
            api: "openai-responses".into(),
            provider: "openai".into(),
            model: "test-model".into(),
            response_model: None,
            response_id: None,
            provider_thinking_level: None,
            thinking_level: None,
            diagnostics: None,
            usage: create_usage(total_tokens),
            stop_reason: StopReason::Stop,
            deferred: None,
            error_message: None,
            raw_stop_reason: None,
            end_turn: None,
            timestamp,
        })
    }

    fn user(text: &str, timestamp: u64) -> Message {
        Message::User(UserMessage {
            content: UserContent::Text(text.into()),
            timestamp,
        })
    }

    #[test]
    fn ignores_stale_assistant_usage_after_a_newer_message_is_inserted_before_it() {
        let context = normalize_context(Context {
            system_prompt: Some("system".into()),
            messages: vec![
                user("summary", 200),
                create_assistant(100, 9_500),
                user(&"x".repeat(4_000), 300),
            ],
            tools: None,
        });
        assert_eq!(
            estimate_context_tokens(context.messages()),
            ContextUsageEstimate {
                tokens: 1_005,
                usage_tokens: 0,
                trailing_tokens: 1_005,
                last_usage_index: None,
            }
        );
        // `buildBaseOptions(model, context).maxTokens` (4_899) belongs to the
        // api/simple-options slice.
    }

    #[test]
    fn uses_assistant_usage_again_after_a_response_to_the_inserted_context() {
        let context = normalize_context(Context {
            system_prompt: None,
            messages: vec![
                user("summary", 200),
                create_assistant(100, 9_500),
                user("new prompt", 300),
                create_assistant(400, 2_000),
                user("tail", 500),
            ],
            tools: None,
        });
        assert_eq!(
            estimate_context_tokens(context.messages()),
            ContextUsageEstimate {
                tokens: 2_001,
                usage_tokens: 2_000,
                trailing_tokens: 1,
                last_usage_index: Some(3),
            }
        );
    }
}
