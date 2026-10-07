//! Model context derivation (`harness/context.ts`, spec §2.1): the active
//! transcript range of one conversation, its edits, and the messages the next
//! provider request sends.

use std::collections::HashMap;
use std::sync::Arc;

use eukhe_chord::context::Context;
use eukhe_types::pi_ai::{
    AssistantContentBlock, Message, StopReason, TextContent, ToolCall, ToolResultMessage,
    UserContentBlock,
};
use futures::future::BoxFuture;
use futures::FutureExt;

use crate::harness::types::ContextView;
use crate::session::{Session, SessionError, SessionResult};
use crate::types::{
    ContextEdit, ContextEditAction, ConversationId, Cursor, EntryId, EntryQuery, EntryRecord,
    Storage,
};

const SCAN_PAGE_SIZE: usize = 256;
const MISSING_RESULT_TEXT: &str =
    "Tool result unavailable: history ends before this call completed.";

/// Whether an assistant message is left out of model context: `aborted`,
/// `error`, and `deferred` answers stay in the transcript only.
fn is_excluded(message: &Message) -> bool {
    match message {
        Message::Assistant(assistant) => matches!(
            assistant.stop_reason,
            StopReason::Aborted | StopReason::Error | StopReason::Deferred
        ),
        Message::System(_) | Message::User(_) | Message::ToolResult(_) => false,
    }
}

/// Head marker and newest visible entry that fix one committed context range.
#[derive(Clone, Debug)]
pub(crate) struct ContextBounds {
    /// The newest visible head marker at or before the tail; its `head` is set.
    pub(crate) head: Option<EntryRecord>,
    pub(crate) tail: EntryId,
}

/// Capture the bounds of the current context, or of the context cut off at
/// the visible entry `at`, with two O(1) reads. Run this on the Session line;
/// entries at or below the tail are immutable, so [`derive_context`] can then
/// scan them off the line.
pub(crate) async fn capture_context_bounds(
    storage: &dyn Storage,
    conversation_id: ConversationId,
    cx: &Context,
    at: Option<EntryId>,
) -> SessionResult<Option<ContextBounds>> {
    let tail = match at {
        None => {
            let page = storage
                .scan_entries(&EntryQuery::new(conversation_id), 1, None, cx)
                .await?;
            let Some(tail) = page.items.first().map(|entry| entry.id) else {
                return Ok(None);
            };
            tail
        }
        Some(at) => {
            if storage.entry_in(conversation_id, at, cx).await?.is_none() {
                return Err(SessionError::error(format!(
                    "Entry {at} is not visible from conversation {conversation_id}"
                )));
            }
            at
        }
    };
    let head = storage
        .find_latest_head_marker(conversation_id, Some(tail), cx)
        .await?;
    Ok(Some(ContextBounds { head, tail }))
}

/// Committed context of one conversation: bounds captured on the Session
/// line, entries derived off it. The line read is enqueued at the call, as
/// the TS promise starts eagerly.
pub(crate) fn read_context(
    session: &Session,
    conversation_id: ConversationId,
    cx: &Context,
    at: Option<EntryId>,
) -> BoxFuture<'static, SessionResult<ContextView>> {
    let storage = Arc::clone(session.storage());
    let line_cx = cx.clone();
    let bounds = session.read_on_line(async move {
        capture_context_bounds(storage.as_ref(), conversation_id, &line_cx, at).await
    });
    let storage = Arc::clone(session.storage());
    let cx = cx.clone();
    async move {
        let bounds = bounds.await?;
        derive_context(storage.as_ref(), conversation_id, bounds.as_ref(), &cx).await
    }
    .boxed()
}

/// Derive the active transcript and model context of one conversation within
/// captured bounds.
///
/// H = newest visible head marker; the range runs from `H.head` (or transcript
/// start) through the tail. Per target, the newest edit in the range wins.
/// Context entries are H followed by the range's non-head entries.
pub(crate) async fn derive_context(
    storage: &dyn Storage,
    conversation_id: ConversationId,
    bounds: Option<&ContextBounds>,
    cx: &Context,
) -> SessionResult<ContextView> {
    let Some(bounds) = bounds else {
        return Ok(ContextView {
            head: None,
            entries: Vec::new(),
            contributions: Vec::new(),
            messages: Vec::new(),
        });
    };
    let range = scan_range(storage, conversation_id, bounds, cx).await?;
    let mut edits: HashMap<EntryId, &ContextEdit> = HashMap::new();
    // Edits of every entry in the range count, including older head markers
    // that `select_active()` drops.
    for entry in &range {
        for edit in entry.edits.iter().flatten() {
            edits.insert(edit.target, edit);
        }
    }
    let contributions: Vec<Vec<Message>> = select_active_refs(bounds.head.as_ref(), &range)
        .map(|entry| {
            let contributed: &[Message] = match edits.get(&entry.id).map(|edit| &edit.action) {
                Some(ContextEditAction::Omit) => return Vec::new(),
                Some(ContextEditAction::Replace { messages }) => messages,
                None => entry.model.as_deref().unwrap_or_default(),
            };
            contributed
                .iter()
                .filter(|message| !is_excluded(message))
                .cloned()
                .collect()
        })
        .collect();
    let messages = order_tool_results(&contributions.concat());
    let entries = select_active(bounds.head.as_ref(), range);
    Ok(ContextView {
        head: bounds.head.clone(),
        entries,
        contributions,
        messages,
    })
}

/// The raw active entries within captured bounds, without deriving model
/// context.
pub(crate) async fn active_entries(
    storage: &dyn Storage,
    conversation_id: ConversationId,
    bounds: Option<&ContextBounds>,
    cx: &Context,
) -> SessionResult<Vec<EntryRecord>> {
    let Some(bounds) = bounds else {
        return Ok(Vec::new());
    };
    let range = scan_range(storage, conversation_id, bounds, cx).await?;
    Ok(select_active(bounds.head.as_ref(), range))
}

/// Visible entries from the head marker's head, or transcript start, through
/// the tail, oldest first.
async fn scan_range(
    storage: &dyn Storage,
    conversation_id: ConversationId,
    bounds: &ContextBounds,
    cx: &Context,
) -> SessionResult<Vec<EntryRecord>> {
    let query = EntryQuery {
        conversation_id,
        min_entry_id: bounds.head.as_ref().and_then(|head| head.head),
        max_entry_id: Some(bounds.tail),
    };
    let mut range = Vec::new();
    let mut cursor: Option<Cursor> = None;
    loop {
        let page = storage
            .scan_entries(&query, SCAN_PAGE_SIZE, cursor.as_ref(), cx)
            .await?;
        range.extend(page.items);
        cursor = page.next;
        if cursor.is_none() {
            break;
        }
    }
    range.reverse();
    Ok(range)
}

/// The head marker followed by the range's non-head entries, or the whole
/// range without a marker.
fn select_active(head: Option<&EntryRecord>, range: Vec<EntryRecord>) -> Vec<EntryRecord> {
    match head {
        None => range,
        Some(head) => std::iter::once(head.clone())
            .chain(range.into_iter().filter(|entry| entry.head.is_none()))
            .collect(),
    }
}

/// [`select_active`] by reference.
fn select_active_refs<'a>(
    head: Option<&'a EntryRecord>,
    range: &'a [EntryRecord],
) -> impl Iterator<Item = &'a EntryRecord> {
    let marker = head.is_some();
    head.into_iter().chain(
        range
            .iter()
            .filter(move |entry| !marker || entry.head.is_none()),
    )
}

/// Place each assistant's tool results directly after it in call order.
/// Results are taken from the messages before the next assistant; a missing
/// result is synthesized and unmatched results are dropped.
#[must_use]
pub fn order_tool_results(messages: &[Message]) -> Vec<Message> {
    let mut ordered = Vec::with_capacity(messages.len());
    for (index, message) in messages.iter().enumerate() {
        if matches!(message, Message::ToolResult(_)) {
            continue;
        }
        ordered.push(message.clone());
        let Message::Assistant(assistant) = message else {
            continue;
        };
        let calls: Vec<&ToolCall> = assistant
            .content
            .iter()
            .filter_map(|content| match content {
                AssistantContentBlock::ToolCall(call) => Some(call),
                AssistantContentBlock::Text(_) | AssistantContentBlock::Thinking(_) => None,
            })
            .collect();
        if calls.is_empty() {
            continue;
        }
        let mut results: HashMap<&str, usize> = HashMap::new();
        for (next, candidate) in messages.iter().enumerate().skip(index + 1) {
            match candidate {
                Message::Assistant(_) => break,
                Message::ToolResult(result) => {
                    results.entry(result.tool_call_id.as_str()).or_insert(next);
                }
                Message::System(_) | Message::User(_) => {}
            }
        }
        for call in calls {
            ordered.push(match results.get(call.id.as_str()) {
                Some(&result) => messages[result].clone(),
                None => missing_result(call, assistant.timestamp),
            });
        }
    }
    ordered
}

fn missing_result(call: &ToolCall, timestamp: u64) -> Message {
    let mut details = eukhe_types::pi_ai::JsonObject::new();
    details.insert("reason".to_owned(), "missing_result".into());
    Message::ToolResult(ToolResultMessage {
        tool_call_id: call.id.clone(),
        tool_name: call.name.clone(),
        content: vec![UserContentBlock::Text(TextContent {
            text: MISSING_RESULT_TEXT.to_owned(),
            ..TextContent::default()
        })],
        details: Some(details.into()),
        usage: None,
        nested_calls: None,
        is_error: true,
        timestamp,
    })
}
