//! eukhe addition: explicit prompt-cache breakpoints on user text blocks
//! ([`TextContent::cache_breakpoint`](eukhe_types::pi_ai::TextContent)) and
//! the mark budget of the APIs that cap one request at four cache marks:
//! Anthropic Messages (`cache_control`), the Anthropic-format marks of
//! OpenAI-compatible proxies, and Bedrock Converse (`cachePoint`).
//!
//! The budget rule. A request with no marked block keeps its upstream marks
//! byte for byte. A request with marked blocks keeps the end-of-request mark
//! (on the last block of the last conversation message) and one mark per
//! marked block; a marked block that also ends the request counts once. The
//! provider's optional marks (system prompt, tools, the OAuth identity block)
//! then take the slots left, in the provider's priority order. More than
//! [`MAX_MARKED_BLOCKS`] marked blocks is a caller bug: the request fails
//! before it is sent, never with a silently dropped mark.
//!
//! Only the text blocks of user messages carry marks; tool-result content
//! never does.

use eukhe_types::pi_ai::{
    AssistantMessage, AssistantMessageEvent, ErrorReason, JsonValue, Message, Model, StopReason,
    Usage, UserContent, UserContentBlock,
};

use crate::utils::event_stream::AssistantMessageEventStream;
use crate::utils::now_ms;

/// Cache marks one request may carry (the Anthropic and Bedrock limit).
pub const MAX_CACHE_MARKS: usize = 4;

/// Marked blocks one request may carry: one slot stays for the end mark.
pub const MAX_MARKED_BLOCKS: usize = MAX_CACHE_MARKS - 1;

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
/// than [`MAX_MARKED_BLOCKS`]; `None` when the count fits. Providers with a
/// capped mark budget call it before they build the request.
#[must_use]
pub fn excess_breakpoints_error(
    model: &Model,
    messages: &[Message],
) -> Option<AssistantMessageEventStream> {
    let marked = count_cache_breakpoints(messages);
    if marked <= MAX_MARKED_BLOCKS {
        return None;
    }
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
        error_message: Some(format!(
            "Too many cache breakpoints: the request marks {marked} blocks, at most {MAX_MARKED_BLOCKS} are allowed"
        )),
        raw_stop_reason: None,
        end_turn: None,
        timestamp: now_ms(),
    };
    let stream = AssistantMessageEventStream::new();
    stream.push(AssistantMessageEvent::Error {
        reason: ErrorReason::Error,
        error: message.clone(),
    });
    stream.end(Some(message));
    Some(stream)
}

/// The cache-mark slots one request has left for its optional marks.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CacheMarkBudget {
    free: usize,
}

impl CacheMarkBudget {
    /// The budget left after the marks the converted messages carry: every
    /// content block with `mark_key` (an Anthropic `cache_control` key, a
    /// Bedrock `cachePoint` block). These are the marked blocks and the end
    /// mark, so a marked block that ends the request counts once.
    #[must_use]
    pub fn after_message_marks(messages: &[JsonValue], mark_key: &str) -> Self {
        let placed = messages
            .iter()
            .filter_map(|message| message.get("content").and_then(JsonValue::as_array))
            .flatten()
            .filter(|block| block.get(mark_key).is_some())
            .count();
        Self {
            free: MAX_CACHE_MARKS.saturating_sub(placed),
        }
    }

    /// Spend one slot on an optional mark: `true` when a slot was left.
    /// Callers ask in their priority order, and only for marks their request
    /// carries.
    pub fn take(&mut self) -> bool {
        match self.free.checked_sub(1) {
            Some(free) => {
                self.free = free;
                true
            }
            None => false,
        }
    }
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
    fn budget_subtracts_placed_marks() {
        let messages = vec![json!({
            "role": "user",
            "content": [
                { "type": "text", "text": "a", "cache_control": { "type": "ephemeral" } },
                { "type": "text", "text": "b" },
            ],
        })];
        let mut budget = CacheMarkBudget::after_message_marks(&messages, "cache_control");
        assert!(budget.take());
        assert!(budget.take());
        assert!(budget.take());
        assert!(!budget.take());
    }
}
