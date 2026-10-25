//! Model context derivation (`harness/context.ts`, spec §2.1): the active
//! transcript range of one conversation, its edits, and the messages the next
//! provider request sends.

use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use eukhe_bend::rules::context_order::{
    self, Added, Edit, Extension, Fact, Keep, Ranged, Role, Step,
};
use eukhe_chord::context::Context;
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, Message, TextContent, ToolCall, ToolResultMessage,
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

/// The context view the committed `entries` of one conversation derive:
/// every visible entry, oldest first, as a context read scans them. The
/// newest head marker bounds the range, as `capture_context_bounds` finds
/// it. A worker derives the context it shows from its event mirror with
/// this, without a storage read.
#[must_use]
pub fn derive_view(entries: &[EntryRecord]) -> ContextView {
    let head = entries.iter().rev().find(|entry| entry.head.is_some());
    let from = head
        .and_then(|head| head.head)
        .map_or(0, |start| entries.partition_point(|entry| entry.id < start));
    derive(head, &entries[from..]).view
}

/// What [`derive`] gives a [`ContextRange`].
struct Derived {
    view: ContextView,
    edited: HashSet<EntryId>,
    settled: Vec<Message>,
    open: Vec<Message>,
}

/// Derive the view from the visible `entries` of one range under the head
/// marker `head`. The compiled core picks the active entries (the marker,
/// then the range's non-head entries), what each contributes after its
/// edit and the excluded stop reasons, the order of their messages and
/// where its settled part ends.
fn derive(head: Option<&EntryRecord>, entries: &[EntryRecord]) -> Derived {
    let mut edits: HashMap<EntryId, &ContextEdit> = HashMap::new();
    // Edits of every entry in the range count, including older head markers
    // that are not active.
    for entry in entries {
        for edit in entry.edits.iter().flatten() {
            edits.insert(edit.target, edit);
        }
    }
    let asked: Vec<&EntryRecord> = head.into_iter().chain(entries).collect();
    let replacements: Vec<&[Message]> = asked
        .iter()
        .map(
            |entry| match edits.get(&entry.id).map(|edit| &edit.action) {
                Some(ContextEditAction::Replace { messages }) => messages.as_slice(),
                Some(ContextEditAction::Omit) | None => &[],
            },
        )
        .collect();
    let mut calls = Calls::default();
    let own: Vec<Vec<Fact>> = asked
        .iter()
        .map(|entry| calls.facts(own_messages(entry)))
        .collect();
    let replaced: Vec<Vec<Fact>> = replacements
        .iter()
        .map(|messages| calls.facts(messages.iter()))
        .collect();
    let ranged: Vec<Ranged<'_>> = asked
        .iter()
        .zip(own.iter().zip(&replaced))
        .map(|(entry, (own, replaced))| Ranged {
            head: entry.head.is_some(),
            edit: match edits.get(&entry.id).map(|edit| &edit.action) {
                None => Edit::None,
                Some(ContextEditAction::Omit) => Edit::Omit,
                Some(ContextEditAction::Replace { .. }) => Edit::Replace(replaced),
            },
            own,
        })
        .collect();
    let (parts, plan) = context_order::derive(head.is_some(), &ranged);
    let active: Vec<EntryRecord> = parts.iter().map(|part| asked[part.at].clone()).collect();
    let contributions: Vec<Vec<Message>> = parts
        .iter()
        .map(|part| match &part.keep {
            Keep::Omitted => Vec::new(),
            Keep::Own(picks) => pick(own_messages(asked[part.at]), picks),
            Keep::Replaced(picks) => pick(replacements[part.at], picks),
        })
        .collect();
    let edited = edits.into_keys().collect();
    let mut open = contributions.concat();
    let ordered = Seq::new(&open).ordered(&plan.steps);
    let settled = ordered[..plan.settles].to_vec();
    if let Some(split) = plan.split {
        open = open.split_off(split);
    }
    Derived {
        view: ContextView {
            head: head.cloned(),
            entries: active,
            contributions,
            messages: lead_with_system(ordered),
        },
        edited,
        settled,
        open,
    }
}

/// An entry's own model messages.
fn own_messages(entry: &EntryRecord) -> &[Message] {
    entry.model.as_deref().unwrap_or_default()
}

/// Clones of the messages at `picks`.
fn pick(messages: &[Message], picks: &[usize]) -> Vec<Message> {
    picks.iter().map(|&index| messages[index].clone()).collect()
}

/// Derive the context view from the entries scanned within `bounds`.
fn derive_range(bounds: ContextBounds, entries: Vec<EntryRecord>) -> ContextRange {
    let Derived {
        view,
        edited,
        settled,
        open,
    } = derive(bounds.head.as_ref(), &entries);
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
/// The compiled core decides when the whole range derives again (an added
/// edit can change an earlier entry) and orders the open messages followed
/// by the added ones; the ordered messages before its split settle.
fn extend_range(
    previous: &ContextRange,
    bounds: ContextBounds,
    added: Vec<EntryRecord>,
) -> ContextRange {
    let extension = {
        let mut calls = Calls::default();
        let own: Vec<Vec<Fact>> = added
            .iter()
            .map(|entry| calls.facts(own_messages(entry)))
            .collect();
        let asked: Vec<Added<'_>> = added
            .iter()
            .zip(&own)
            .map(|(entry, own)| Added {
                edits: entry.edits.is_some(),
                head: entry.head.is_some(),
                edited: previous.edited.contains(&entry.id),
                own,
            })
            .collect();
        let open = calls.facts(&previous.open);
        context_order::extend(&asked, &open)
    };
    let (keeps, plan) = match extension {
        Extension::Rederive => {
            let mut entries = previous.entries.clone();
            entries.extend(added);
            return derive_range(bounds, entries);
        }
        Extension::Extend { keeps, plan } => (keeps, plan),
    };
    let contributions: Vec<Vec<Message>> = added
        .iter()
        .zip(&keeps)
        .map(|(entry, picks)| pick(own_messages(entry), picks))
        .collect();
    let mut open = previous.open.clone();
    open.extend(contributions.iter().flatten().cloned());
    let ordered = Seq::new(&open).ordered(&plan.steps);
    let mut settled = previous.settled.clone();
    settled.extend_from_slice(&ordered[..plan.settles]);
    if let Some(split) = plan.split {
        open = open.split_off(split);
    }
    let messages = lead_with_system(previous.settled.iter().cloned().chain(ordered).collect());
    let mut view_entries = previous.view.entries.clone();
    view_entries.extend(added.iter().cloned());
    let mut view_contributions = previous.view.contributions.clone();
    view_contributions.extend(contributions);
    let mut entries = previous.entries.clone();
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

/// Move the system message the compiled core picks to the front: one that
/// only user messages precede. A run's input is committed before generation
/// renders the system prompt, so a transcript, or the range after a
/// compaction or reset, starts with user messages followed by the baseline
/// system message. Providers treat only a leading system message as the
/// initial prompt and tool set; without it, a later tool change rewrites the
/// request's tool list and invalidates the whole prompt cache.
fn lead_with_system(mut messages: Vec<Message>) -> Vec<Message> {
    let roles: Vec<Role> = messages
        .iter()
        .map(|message| match message {
            Message::System(_) => Role::System,
            Message::User(_) => Role::User,
            Message::Assistant(_) => Role::Assistant,
            Message::ToolResult(_) => Role::Result,
        })
        .collect();
    if let Some(index) = context_order::lead(&roles) {
        let system = messages.remove(index);
        messages.insert(0, system);
    }
    messages
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

/// The active entries of `range` under the head marker `head`, as the
/// compiled core picks them: the marker followed by the range's non-head
/// entries, or the whole range without a marker.
fn select_active(head: Option<&EntryRecord>, range: Vec<EntryRecord>) -> Vec<EntryRecord> {
    let marker = usize::from(head.is_some());
    let picked: Vec<usize> = {
        let ranged: Vec<Ranged<'_>> = head
            .into_iter()
            .chain(&range)
            .map(|entry| Ranged {
                head: entry.head.is_some(),
                edit: Edit::None,
                own: &[],
            })
            .collect();
        let (parts, _) = context_order::derive(head.is_some(), &ranged);
        parts.iter().map(|part| part.at).collect()
    };
    // The core's entry indices increase (`eukhe_bend::rules::context_order`
    // checks it): one pass over the range moves the picked entries out.
    let mut picked = picked.into_iter().peekable();
    let mut active = Vec::with_capacity(picked.len());
    if let Some(head) = head {
        if picked.next_if_eq(&0).is_some() {
            active.push(head.clone());
        }
    }
    for (index, entry) in range.into_iter().enumerate() {
        if picked.next_if_eq(&(index + marker)).is_some() {
            active.push(entry);
        }
    }
    active
}

/// Place each assistant's tool results directly after it in call order.
/// Results are taken from the messages before the next assistant; a missing
/// result is synthesized and unmatched results are dropped (the compiled
/// core's order).
#[must_use]
pub fn order_tool_results(messages: &[Message]) -> Vec<Message> {
    let facts = Calls::default().facts(messages);
    Seq::new(messages).ordered(&context_order::order(&facts))
}

/// Call ids interned to the numbers the compiled core compares: equal ids,
/// equal numbers, within one question.
#[derive(Default)]
pub(crate) struct Calls<'a> {
    ids: HashMap<&'a str, u64>,
}

impl<'a> Calls<'a> {
    fn id(&mut self, id: &'a str) -> u64 {
        let next = u64::try_from(self.ids.len()).unwrap_or(u64::MAX);
        *self.ids.entry(id).or_insert(next)
    }

    /// The facts of each of `messages`.
    pub(crate) fn facts(&mut self, messages: impl IntoIterator<Item = &'a Message>) -> Vec<Fact> {
        messages
            .into_iter()
            .map(|message| match message {
                Message::System(_) => Fact::System,
                Message::User(_) => Fact::User,
                Message::Assistant(assistant) => Fact::Assistant {
                    stop: assistant.stop_reason,
                    calls: tool_calls(assistant)
                        .map(|call| self.id(&call.id))
                        .collect(),
                },
                Message::ToolResult(result) => Fact::Result {
                    call: self.id(&result.tool_call_id),
                },
            })
            .collect()
    }
}

/// The tool calls of an assistant message, in order.
pub(crate) fn tool_calls(assistant: &AssistantMessage) -> impl Iterator<Item = &ToolCall> {
    assistant
        .content
        .iter()
        .filter_map(|content| match content {
            AssistantContentBlock::ToolCall(call) => Some(call),
            AssistantContentBlock::Text(_) | AssistantContentBlock::Thinking(_) => None,
        })
}

/// The messages a plan's steps index, with each assistant's calls and
/// timestamp (empty for the others).
struct Seq<'a> {
    messages: &'a [Message],
    calls: Vec<(Vec<&'a ToolCall>, u64)>,
}

impl<'a> Seq<'a> {
    fn new(messages: &'a [Message]) -> Seq<'a> {
        let calls = messages
            .iter()
            .map(|message| match message {
                Message::Assistant(assistant) => {
                    (tool_calls(assistant).collect(), assistant.timestamp)
                }
                Message::System(_) | Message::User(_) | Message::ToolResult(_) => (Vec::new(), 0),
            })
            .collect();
        Seq { messages, calls }
    }

    /// The messages of `steps`: a clone of each one taken, a synthesized
    /// result for each missing one. `eukhe_bend::rules::context_order`
    /// checks every index against the facts of these messages.
    fn ordered(&self, steps: &[Step]) -> Vec<Message> {
        steps
            .iter()
            .map(|step| match *step {
                Step::Take(index) => self.messages[index].clone(),
                Step::Missing { assistant, call } => {
                    let (calls, timestamp) = &self.calls[assistant];
                    missing_result(calls[call], *timestamp)
                }
            })
            .collect()
    }
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
