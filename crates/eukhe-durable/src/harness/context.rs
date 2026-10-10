//! Model context derivation (`harness/context.ts`, spec §2.1): the active
//! transcript range of one conversation, its edits, and the messages the next
//! provider request sends.

use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
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

/// One context read: the visible entries it scanned, from the head marker's
/// head, or transcript start, through `bounds.tail`, oldest first, and the
/// view derived from them. Entries at or below the tail never change, so a
/// later read with the same head marker extends both.
#[derive(Debug)]
pub(crate) struct ContextRange {
    pub(crate) bounds: ContextBounds,
    entries: Vec<EntryRecord>,
    view: ContextView,
    /// Targets of the edits in `entries`.
    edited: HashSet<EntryId>,
    /// `view.messages` from the contributed messages before the last
    /// assistant message. Tool results are ordered within the messages up to
    /// the next assistant message, so later entries cannot change these.
    settled: Vec<Message>,
    /// Contributed messages from the last assistant message on, before tool
    /// result ordering.
    open: Vec<Message>,
}

/// [`read_context`] that reuses `previous`, an earlier range of the same
/// conversation: with the same head marker, only entries after its tail are
/// scanned. Returns the view and the range to pass to the next read. A range
/// outlives the read; the returned view is the caller's own copy.
pub(crate) async fn read_context_from(
    session: &Session,
    conversation_id: ConversationId,
    cx: &Context,
    at: Option<EntryId>,
    previous: Option<Arc<ContextRange>>,
) -> SessionResult<(ContextView, Option<Arc<ContextRange>>)> {
    let storage = Arc::clone(session.storage());
    let line_cx = cx.clone();
    let bounds = session
        .read_on_line(async move {
            capture_context_bounds(storage.as_ref(), conversation_id, &line_cx, at).await
        })
        .await?;
    let Some(bounds) = bounds else {
        return Ok((empty_view(), None));
    };
    let storage = session.storage().as_ref();
    let head_id = |bounds: &ContextBounds| bounds.head.as_ref().map(|head| head.id);
    let range = match previous {
        Some(previous) if head_id(&previous.bounds) == head_id(&bounds) => {
            match bounds.tail.cmp(&previous.bounds.tail) {
                Ordering::Equal => previous,
                Ordering::Less => {
                    let entries = previous
                        .entries
                        .iter()
                        .filter(|entry| entry.id <= bounds.tail)
                        .cloned()
                        .collect();
                    Arc::new(derive_range(bounds, entries))
                }
                Ordering::Greater => {
                    let min_entry_id = EntryId::from_number(previous.bounds.tail.get() + 1);
                    let added = scan_range(
                        storage,
                        conversation_id,
                        Some(min_entry_id),
                        bounds.tail,
                        cx,
                    )
                    .await?;
                    Arc::new(extend_range(&previous, bounds, added))
                }
            }
        }
        Some(_) | None => {
            let (min_entry_id, max_entry_id) = range_bounds(&bounds);
            let entries =
                scan_range(storage, conversation_id, min_entry_id, max_entry_id, cx).await?;
            Arc::new(derive_range(bounds, entries))
        }
    };
    Ok((range.view.clone(), Some(range)))
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
        derive_context(storage.as_ref(), conversation_id, bounds, &cx).await
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
    bounds: Option<ContextBounds>,
    cx: &Context,
) -> SessionResult<ContextView> {
    let Some(bounds) = bounds else {
        return Ok(empty_view());
    };
    let (min_entry_id, max_entry_id) = range_bounds(&bounds);
    let entries = scan_range(storage, conversation_id, min_entry_id, max_entry_id, cx).await?;
    Ok(derive_range(bounds, entries).view)
}

fn empty_view() -> ContextView {
    ContextView {
        head: None,
        entries: Vec::new(),
        contributions: Vec::new(),
        messages: Vec::new(),
    }
}

/// Derive the context view from the entries scanned within `bounds`.
fn derive_range(bounds: ContextBounds, entries: Vec<EntryRecord>) -> ContextRange {
    let mut edits: HashMap<EntryId, &ContextEdit> = HashMap::new();
    // Edits of every entry in the range count, including older head markers
    // that `select_active()` drops.
    for entry in &entries {
        for edit in entry.edits.iter().flatten() {
            edits.insert(edit.target, edit);
        }
    }
    let active: Vec<EntryRecord> = select_active_refs(bounds.head.as_ref(), &entries)
        .cloned()
        .collect();
    let contributions: Vec<Vec<Message>> = active
        .iter()
        .map(|entry| contribute(entry, edits.get(&entry.id).copied()))
        .collect();
    let edited = edits.into_keys().collect();
    let (settled, open) = settle(Vec::new(), contributions.concat());
    let messages = lead_with_system(
        settled
            .iter()
            .cloned()
            .chain(order_tool_results(&open))
            .collect(),
    );
    let view = ContextView {
        head: bounds.head.clone(),
        entries: active,
        contributions,
        messages,
    };
    ContextRange {
        bounds,
        entries,
        view,
        edited,
        settled,
        open,
    }
}

/// `previous` extended by the entries `added` after its tail under the same
/// head marker: only their contributions and the open messages are derived.
/// An added edit can change an earlier entry, so it derives the whole range
/// again.
fn extend_range(
    previous: &ContextRange,
    bounds: ContextBounds,
    added: Vec<EntryRecord>,
) -> ContextRange {
    let rederive = added.iter().any(|entry| {
        entry.edits.is_some() || entry.head.is_some() || previous.edited.contains(&entry.id)
    });
    let mut entries = previous.entries.clone();
    if rederive {
        entries.extend(added);
        return derive_range(bounds, entries);
    }
    let contributions: Vec<Vec<Message>> =
        added.iter().map(|entry| contribute(entry, None)).collect();
    let mut open = previous.open.clone();
    open.extend(contributions.iter().flatten().cloned());
    let (settled, open) = settle(previous.settled.clone(), open);
    let messages = lead_with_system(
        settled
            .iter()
            .cloned()
            .chain(order_tool_results(&open))
            .collect(),
    );
    let mut view_entries = previous.view.entries.clone();
    view_entries.extend(added.iter().cloned());
    let mut view_contributions = previous.view.contributions.clone();
    view_contributions.extend(contributions);
    entries.extend(added);
    ContextRange {
        view: ContextView {
            head: bounds.head.clone(),
            entries: view_entries,
            contributions: view_contributions,
            messages,
        },
        bounds,
        entries,
        edited: previous.edited.clone(),
        settled,
        open,
    }
}

/// Move a system message that only user messages precede to the front. A
/// run's input is committed before generation renders the system prompt, so
/// a transcript, or the range after a compaction or reset, starts with user
/// messages followed by the baseline system message. Providers treat only a
/// leading system message as the initial prompt and tool set; without it, a
/// later tool change rewrites the request's tool list and invalidates the
/// whole prompt cache.
fn lead_with_system(mut messages: Vec<Message>) -> Vec<Message> {
    let Some(index) = messages
        .iter()
        .position(|message| !matches!(message, Message::User(_)))
    else {
        return messages;
    };
    if index == 0 || !matches!(messages[index], Message::System(_)) {
        return messages;
    }
    let system = messages.remove(index);
    messages.insert(0, system);
    messages
}

/// One active entry's model messages after its edit and excluded stop
/// reasons, before tool result ordering.
fn contribute(entry: &EntryRecord, edit: Option<&ContextEdit>) -> Vec<Message> {
    let contributed: &[Message] = match edit.map(|edit| &edit.action) {
        Some(ContextEditAction::Omit) => return Vec::new(),
        Some(ContextEditAction::Replace { messages }) => messages,
        None => entry.model.as_deref().unwrap_or_default(),
    };
    contributed
        .iter()
        .filter(|message| !is_excluded(message))
        .cloned()
        .collect()
}

/// Move the ordered messages before the last assistant message of `open` to
/// `settled`. `order_tool_results()` of a sequence equals the concatenation
/// over its parts when each later part starts with an assistant message.
fn settle(mut settled: Vec<Message>, mut open: Vec<Message>) -> (Vec<Message>, Vec<Message>) {
    let last = open
        .iter()
        .rposition(|message| matches!(message, Message::Assistant(_)));
    match last {
        Some(last) if last > 0 => {
            let rest = open.split_off(last);
            settled.extend(order_tool_results(&open));
            (settled, rest)
        }
        Some(_) | None => (settled, open),
    }
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
    let (min_entry_id, max_entry_id) = range_bounds(bounds);
    let range = scan_range(storage, conversation_id, min_entry_id, max_entry_id, cx).await?;
    Ok(select_active(bounds.head.as_ref(), range))
}

/// The visible range of `bounds`: from the head marker's head, or transcript
/// start, through the tail.
fn range_bounds(bounds: &ContextBounds) -> (Option<EntryId>, EntryId) {
    (bounds.head.as_ref().and_then(|head| head.head), bounds.tail)
}

/// Visible entries within `min_entry_id..=max_entry_id`, oldest first.
async fn scan_range(
    storage: &dyn Storage,
    conversation_id: ConversationId,
    min_entry_id: Option<EntryId>,
    max_entry_id: EntryId,
    cx: &Context,
) -> SessionResult<Vec<EntryRecord>> {
    let query = EntryQuery {
        conversation_id,
        min_entry_id,
        max_entry_id: Some(max_entry_id),
        order: None,
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
        duration_ms: None,
    })
}
