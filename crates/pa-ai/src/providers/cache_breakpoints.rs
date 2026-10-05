//! Explicit prompt-cache breakpoints on user text blocks
//! ([`crate::types::TextContent::cache_breakpoint`]) and the mark budget of
//! the APIs that cap one request at four cache marks: Anthropic Messages
//! (`cache_control`), the Anthropic-format marks of `OpenAI`-compatible
//! proxies, and Bedrock Converse (`cachePoint`).
//!
//! The budget rule. A request with no marked block keeps its historical
//! marks byte for byte. A request with marked blocks keeps the end-of-request
//! mark (on the last block of the last user message) and one mark per marked
//! block; a marked block that also ends the request counts once. The
//! provider's optional marks (system prompt, tools, the OAuth identity block)
//! then take the slots left, in the provider's priority order. More than
//! [`MAX_MARKED_BLOCKS`] marked blocks is a caller bug: the request fails
//! before it is sent, never with a silently dropped mark.
//!
//! Only the text blocks of user messages carry marks; tool-result content
//! never does.

use serde_json::{Map, Value};

use crate::event_stream::{
    create_assistant_message_event_stream, AssistantMessageEvent, AssistantMessageEventStream,
};
use crate::types::{
    AssistantMessage, Context, ErrorStopReason, Message, Model, StopReason, Usage,
    UserMessageContent, UserOrToolContent,
};
use crate::utils_inner::diagnostics::now_ms;

/// Cache marks one request may carry (the Anthropic and Bedrock limit).
const MAX_CACHE_MARKS: usize = 4;

/// Marked blocks one request may carry: one slot stays for the end mark.
const MAX_MARKED_BLOCKS: usize = MAX_CACHE_MARKS - 1;

/// Whether a user content block carries an explicit cache breakpoint. Only
/// modeled text blocks can carry one.
pub(crate) fn has_cache_breakpoint(block: &UserOrToolContent) -> bool {
    match block {
        UserOrToolContent::Text(text) => text.cache_breakpoint.is_some(),
        UserOrToolContent::Image(_) | UserOrToolContent::Raw(_) => false,
    }
}

/// The early error stream for a context that marks more user text blocks
/// than [`MAX_MARKED_BLOCKS`], in the shape of the providers' missing-API-key
/// error; `None` when the count fits. Providers with a capped mark budget call
/// it before they build the request.
pub(crate) fn excess_breakpoints_error(
    model: &Model,
    context: &Context,
) -> Option<AssistantMessageEventStream> {
    let marked: usize = context
        .messages
        .iter()
        .map(|message| match message {
            Message::User(user) => match &user.content {
                UserMessageContent::Blocks(blocks) => blocks
                    .iter()
                    .filter(|block| has_cache_breakpoint(block))
                    .count(),
                UserMessageContent::Text(_) => 0,
            },
            Message::Assistant(_) | Message::ToolResult(_) => 0,
        })
        .sum();
    if marked <= MAX_MARKED_BLOCKS {
        return None;
    }
    let (writer, reader) = create_assistant_message_event_stream();
    let message = AssistantMessage {
        content: Vec::new(),
        api: model.api.clone(),
        provider: model.provider.clone(),
        model: model.id.clone(),
        response_model: None,
        response_id: None,
        diagnostics: None,
        usage: Usage::default(),
        stop_reason: StopReason::Error,
        stop_reason_raw: None,
        error_message: Some(format!(
            "Too many cache breakpoints: the request marks {marked} blocks, at most {MAX_MARKED_BLOCKS} are allowed"
        )),
        timestamp: now_ms(),
        rest: Map::default(),
    };
    writer.push(AssistantMessageEvent::Error {
        reason: ErrorStopReason::Error,
        error: message.clone(),
    });
    writer.end(Some(message));
    Some(reader)
}

/// The cache-mark slots one request has left for its optional marks.
pub(crate) struct CacheMarkBudget {
    free: usize,
}

impl CacheMarkBudget {
    /// The budget left after the marks the converted messages carry: every
    /// content block with `mark_key` (an Anthropic `cache_control` key, a
    /// Bedrock `cachePoint` block). These are the marked blocks and the end
    /// mark, so a marked block that ends the request counts once.
    pub(crate) fn after_message_marks(messages: &[Value], mark_key: &str) -> Self {
        let placed = messages
            .iter()
            .filter_map(|message| message.get("content").and_then(Value::as_array))
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
    pub(crate) fn take(&mut self) -> bool {
        match self.free.checked_sub(1) {
            Some(free) => {
                self.free = free;
                true
            }
            None => false,
        }
    }
}
