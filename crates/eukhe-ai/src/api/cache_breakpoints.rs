//! eukhe addition: explicit prompt-cache breakpoints on user text blocks
//! ([`TextContent::cache_breakpoint`](eukhe_types::pi_ai::TextContent)) and
//! the mark budget of the APIs that cap one request at four cache marks:
//! Anthropic Messages (`cache_control`), the Anthropic-format marks of
//! OpenAI-compatible proxies, and Bedrock Converse (`cachePoint`).
//!
//! The budget rule runs as the compiled core
//! (`eukhe_bend::rules::cache_marks`, `laws/cache_marks.bend`). A request
//! with no marked block keeps its upstream marks byte for byte. A request
//! with marked blocks keeps the end-of-request mark (on the last block of
//! the last conversation message) and one mark per marked block; a marked
//! block that also ends the request counts once. The provider's optional
//! marks (system prompt, tools, the OAuth identity block) then take the
//! slots left, in the provider's priority order. Too many marked blocks is
//! a caller bug: the request fails before it is sent, never with a
//! silently dropped mark. This module gathers the counts the core decides
//! on.
//!
//! Only the text blocks of user messages carry marks; tool-result content
//! never does.

use eukhe_bend::rules::cache_marks;
use eukhe_types::pi_ai::{
    AssistantMessage, AssistantMessageEvent, ErrorReason, JsonValue, Message, Model, StopReason,
    Usage, UserContent, UserContentBlock,
};

use crate::utils::event_stream::AssistantMessageEventStream;
use crate::utils::now_ms;

/// Whether a user content block carries an explicit cache breakpoint. Only
/// text blocks can carry one.
#[must_use]
pub fn has_cache_breakpoint(block: &UserContentBlock) -> bool {
    match block {
        UserContentBlock::Text(text) => text.cache_breakpoint.is_some(),
        UserContentBlock::Image(_) => false,
    }
}

/// Number of marked user text blocks in `messages`.
#[must_use]
pub fn count_cache_breakpoints(messages: &[Message]) -> usize {
    messages
        .iter()
        .map(|message| match message {
            Message::User(user) => match &user.content {
                UserContent::Blocks(blocks) => blocks
                    .iter()
                    .filter(|block| has_cache_breakpoint(block))
                    .count(),
                UserContent::Text(_) => 0,
            },
            Message::System(_) | Message::Assistant(_) | Message::ToolResult(_) => 0,
        })
        .sum()
}

/// The early error stream for a transcript that marks more user text blocks
/// than one request may carry; `None` when the count fits. Providers with a
/// capped mark budget call it before they build the request.
#[must_use]
pub fn excess_breakpoints_error(
    model: &Model,
    messages: &[Message],
) -> Option<AssistantMessageEventStream> {
    let error_message = cache_marks::excess(count_cache_breakpoints(messages))?;
    let message = AssistantMessage {
        content: Vec::new(),
        api: model.api.clone(),
        provider: model.provider.clone(),
        model: model.id.clone(),
        response_model: None,
        response_id: None,
        provider_thinking_level: None,
        thinking_level: None,
        diagnostics: None,
        usage: Usage::default(),
        stop_reason: StopReason::Error,
        deferred: None,
        error_message: Some(error_message),
        raw_stop_reason: None,
        end_turn: None,
        timestamp: now_ms(),
        duration_ms: None,
        timing: None,
    };
    let stream = AssistantMessageEventStream::new();
    stream.push(AssistantMessageEvent::Error {
        reason: ErrorReason::Error,
        error: message.clone(),
    });
    stream.end(Some(message));
    Some(stream)
}

/// The marks the converted messages carry: every content block with
/// `mark_key` (an Anthropic `cache_control` key, a Bedrock `cachePoint`
/// block). These are the marked blocks and the end mark, so a marked block
/// that ends the request counts once. The optional marks take the slots
/// `eukhe_bend::rules::cache_marks::grant` leaves after them.
#[must_use]
pub fn placed_marks(messages: &[JsonValue], mark_key: &str) -> usize {
    messages
        .iter()
        .filter_map(|message| message.get("content").and_then(JsonValue::as_array))
        .flatten()
        .filter(|block| block.get(mark_key).is_some())
        .count()
}

#[cfg(test)]
mod tests {
    use eukhe_types::pi_ai::{TextContent, UserMessage};
    use serde_json::json;

    use super::*;

    fn marked_user(count: usize) -> Message {
        Message::User(UserMessage {
            content: UserContent::Blocks(
                (0..count)
                    .map(|index| {
                        UserContentBlock::Text(TextContent {
                            cache_breakpoint: Some(eukhe_types::pi_ai::CacheBreakpoint::Ephemeral),
                            ..TextContent::new(format!("block {index}"))
                        })
                    })
                    .collect(),
            ),
            timestamp: 0,
        })
    }

    #[test]
    fn counts_marked_user_text_blocks() {
        assert_eq!(
            count_cache_breakpoints(&[marked_user(2), marked_user(1)]),
            3
        );
    }

    #[test]
    fn counts_placed_marks() {
        let messages = vec![json!({
            "role": "user",
            "content": [
                { "type": "text", "text": "a", "cache_control": { "type": "ephemeral" } },
                { "type": "text", "text": "b" },
            ],
        })];
        assert_eq!(placed_marks(&messages, "cache_control"), 1);
    }
}
