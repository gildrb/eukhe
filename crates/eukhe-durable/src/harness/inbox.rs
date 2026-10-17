//! The built-in `pi.inbox` document and boundaries (`harness/inbox.ts`, spec
//! §6): queued submissions of one conversation and their placement.

use eukhe_chord::delta::{Draft, DraftItem, Op};
use eukhe_chord::json::{from_json, to_json, JsonObject, JsonValue};
use eukhe_types::input_origin::InputOrigin;
use eukhe_types::pi_ai::{Message, UserContent, UserMessage};
use futures::future::BoxFuture;
use futures::FutureExt;
use serde::ser::SerializeStruct;
use serde::{Deserialize, Serialize};

use crate::documents::{ConversationDoc, DocDefinition};
use crate::entries::{UserData, USER_ENTRY};
use crate::harness::types::{
    InputEntry, InputSubmissionDraft, QueueMode, SubmissionDraft, WhenBusy, WriteSubmissionDraft,
};
use crate::session::{SessionResult, Tx};
use crate::types::{
    CheckpointInfo, ConversationId, EntryDraft, EntryHead, EntryId, LatestFork, SubmissionId,
    SubmissionSettlement, TypedEntryDraft,
};

/// A queued submission: user input for a run, with the entry it is placed as
/// when not `pi.user`, or a passive entry write.
#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(tag = "mode")]
pub enum InboxItem {
    /// Input admitted with `whenBusy: "steer"`.
    #[serde(rename = "steer")]
    Steer {
        id: SubmissionId,
        content: UserContent,
        #[serde(default)]
        entry: Option<InputEntry>,
        #[serde(default = "user_origin")]
        origin: InputOrigin,
    },
    /// Input admitted with `whenBusy: "followUp"` or no `whenBusy`.
    #[serde(rename = "followUp")]
    FollowUp {
        id: SubmissionId,
        content: UserContent,
        #[serde(default)]
        entry: Option<InputEntry>,
        #[serde(default = "user_origin")]
        origin: InputOrigin,
    },
    /// A passive write; `entry` is an `EntryDraft`, stored as plain JSON.
    #[serde(rename = "write")]
    Write { id: SubmissionId, entry: JsonValue },
}

impl InboxItem {
    /// The queued item of submission `id` admitted as `draft`.
    ///
    /// # Errors
    ///
    /// A write entry that is not strict JSON.
    pub(crate) fn queued(id: SubmissionId, draft: SubmissionDraft) -> SessionResult<Self> {
        Ok(match draft {
            SubmissionDraft::Write(WriteSubmissionDraft { entry, .. }) => Self::Write {
                id,
                entry: to_json(&entry)?,
            },
            SubmissionDraft::Input(InputSubmissionDraft {
                content,
                when_busy,
                origin,
                entry,
                ..
            }) => match when_busy {
                Some(WhenBusy::Steer) => Self::Steer {
                    id,
                    content,
                    entry,
                    origin,
                },
                Some(WhenBusy::FollowUp | WhenBusy::Reject) | None => Self::FollowUp {
                    id,
                    content,
                    entry,
                    origin,
                },
            },
        })
    }

    /// The queued submission.
    #[must_use]
    pub fn id(&self) -> SubmissionId {
        match self {
            Self::Steer { id, .. } | Self::FollowUp { id, .. } | Self::Write { id, .. } => *id,
        }
    }
}

/// An input item without `origin` is the user's input.
fn user_origin() -> InputOrigin {
    InputOrigin::User
}

/// TS object-literal order: `{ id, mode, content, entry? }` /
/// `{ id, mode, entry }`; an eukhe `origin` follows unless the input is the
/// user's.
impl Serialize for InboxItem {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self {
            Self::Steer {
                id,
                content,
                entry,
                origin,
            }
            | Self::FollowUp {
                id,
                content,
                entry,
                origin,
            } => {
                let mut item = serializer.serialize_struct("InboxItem", 5)?;
                item.serialize_field("id", id)?;
                let mode = if matches!(self, Self::Steer { .. }) {
                    "steer"
                } else {
                    "followUp"
                };
                item.serialize_field("mode", mode)?;
                item.serialize_field("content", content)?;
                match entry {
                    Some(entry) => item.serialize_field("entry", entry)?,
                    None => item.skip_field("entry")?,
                }
                match origin {
                    InputOrigin::User => item.skip_field("origin")?,
                    InputOrigin::Goal { .. }
                    | InputOrigin::Autonomous { .. }
                    | InputOrigin::QuotaResume
                    | InputOrigin::Report { .. } => item.serialize_field("origin", origin)?,
                }
                item.end()
            }
            Self::Write { id, entry } => {
                let mut item = serializer.serialize_struct("InboxItem", 3)?;
                item.serialize_field("id", id)?;
                item.serialize_field("mode", "write")?;
                item.serialize_field("entry", entry)?;
                item.end()
            }
        }
    }
}

/// Built-in queue of one conversation's submissions waiting for a boundary,
/// in ID order.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct InboxState {
    pub items: Vec<InboxItem>,
}

fn inbox_checkpoint_when(value: &JsonObject, _ops: &[Op], _info: CheckpointInfo) -> bool {
    value
        .get("items")
        .and_then(JsonValue::as_array)
        .is_some_and(<[JsonValue]>::is_empty)
}

/// The `pi.inbox` document token (TS `InboxDoc`).
pub static INBOX_DOC: ConversationDoc<InboxState> = match ConversationDoc::define(
    DocDefinition {
        kind: "pi.inbox",
        version: 1,
        initial: InboxState::default,
        migrate: None,
        checkpoint_when: Some(inbox_checkpoint_when),
    },
    LatestFork::Initial,
) {
    Ok(token) => token,
    Err(_) => panic!("invalid pi.inbox definition"),
};

/// The settings a boundary reads, on the Session line.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct QueueModes {
    pub steering_mode: QueueMode,
    pub follow_up_mode: QueueMode,
}

/// Where a boundary runs: after a tool round, or at the end of a run.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BoundaryAt {
    PostTools,
    Final,
}

/// What a boundary reads before the commit's first table write, and the
/// newest head it has seen so far.
#[derive(Debug, Clone)]
pub struct Boundary {
    pub conversation_id: ConversationId,
    /// The `pi.inbox` draft.
    pub inbox: Draft,
    pub steering_mode: QueueMode,
    pub follow_up_mode: QueueMode,
    /// Start of the active range, the newest head marker's `head`; advanced by
    /// heads written in this commit.
    pub head: Option<EntryId>,
}

impl Boundary {
    /// The `items` array draft of the inbox.
    ///
    /// # Errors
    ///
    /// A tracker failure.
    pub fn items(&self) -> SessionResult<Draft> {
        Ok(self.inbox.child("items")?)
    }

    /// Whether the inbox holds no item.
    ///
    /// # Errors
    ///
    /// A tracker failure.
    pub fn is_empty(&self) -> SessionResult<bool> {
        Ok(self.items()?.is_empty()?)
    }
}

/// Selected user items, in ID order, and whether a `head: "self"` write (a
/// reset) was placed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoundaryResult {
    pub users: Vec<SubmissionId>,
    pub reset: bool,
}

/// Read what a boundary needs. Table reads must precede the commit's first
/// table write, so callers prepare the boundary at the start of their commit.
///
/// # Errors
///
/// Transaction read and document failures.
pub async fn prepare_boundary(
    tx: &Tx,
    conversation_id: ConversationId,
    modes: QueueModes,
) -> SessionResult<Boundary> {
    let head = tx
        .latest_head_marker(conversation_id)
        .await?
        .and_then(|marker| marker.head);
    let inbox = tx.doc(&INBOX_DOC, conversation_id).await?;
    Ok(Boundary {
        conversation_id,
        inbox,
        steering_mode: modes.steering_mode,
        follow_up_mode: modes.follow_up_mode,
        head,
    })
}

/// The mode string of the item JSON at `item`.
fn mode_of(item: &JsonValue) -> Option<&str> {
    item.get("mode").and_then(JsonValue::as_str)
}

fn submission_id_of(item: &JsonValue) -> SessionResult<SubmissionId> {
    Ok(from_json(&item["id"])?)
}

/// Place the queued items a boundary selects (spec §6): every write, the
/// first or all steers, and at `final` the first or all follow-ups. A
/// selected reset turns a `postTools` boundary into `final`. Writes are placed
/// first and user items after them, each in ID order, so user items queued
/// before a reset run in the new context. A write whose head targets an entry
/// before the active range, including a range started earlier in this
/// commit, is stale. Selected and stale items are removed positionally.
///
/// # Errors
///
/// Transaction, document, and JSON failures.
pub async fn apply_boundary(
    tx: &Tx,
    boundary: &mut Boundary,
    at: BoundaryAt,
    now: u64,
) -> SessionResult<BoundaryResult> {
    let conversation_id = boundary.conversation_id;
    let items_draft = boundary.items()?;
    let items_value = items_draft.value()?;
    let items = items_value.as_array().unwrap_or_default();
    let reset = has_queued_reset(items);
    let is_final = at == BoundaryAt::Final || reset;
    let pick = |mode: &str, queue_mode: QueueMode| -> Vec<usize> {
        let indexes = items
            .iter()
            .enumerate()
            .filter(|(_, item)| mode_of(item) == Some(mode))
            .map(|(index, _)| index);
        match queue_mode {
            QueueMode::All => indexes.collect(),
            QueueMode::OneAtATime => indexes.take(1).collect(),
        }
    };
    let writes = pick("write", QueueMode::All);
    let mut users = pick("steer", boundary.steering_mode);
    if is_final {
        users.extend(pick("followUp", boundary.follow_up_mode));
    }
    users.sort_unstable();

    // `append_entry()` copies the drafts' values; the items are removed only afterwards.
    for &index in &writes {
        let item = &items[index];
        let id = submission_id_of(item)?;
        let draft: EntryDraft = from_json(&item["entry"])?;
        if is_stale(boundary, &draft) {
            tx.settle_submission(
                id,
                SubmissionSettlement::Unanswered {
                    reason: "stale".to_owned(),
                    detail: None,
                },
            )?;
            continue;
        }
        let head = draft.head;
        let entry = tx.append_entry(conversation_id, draft).await?;
        if let Some(head) = head {
            boundary.head = Some(match head {
                EntryHead::SelfEntry => entry.id,
                EntryHead::Entry(head) => head,
            });
        }
        tx.place_submission(id, entry.id)?;
    }
    let mut placed = Vec::with_capacity(users.len());
    for &index in &users {
        let item = &items[index];
        let id = submission_id_of(item)?;
        let input = PlacedInput {
            content: from_json(&item["content"])?,
            entry: item.get("entry").map(from_json).transpose()?,
            origin: match item.get("origin") {
                Some(origin) => from_json(origin)?,
                None => user_origin(),
            },
        };
        let entry = append_input(tx, conversation_id, input, now).await?;
        tx.place_submission(id, entry)?;
        placed.push(id);
    }
    let mut removed: Vec<usize> = writes.into_iter().chain(users).collect();
    removed.sort_unstable_by(|a, b| b.cmp(a));
    for index in removed {
        items_draft.splice(index_i64(index), 1, Vec::<JsonValue>::new())?;
    }
    Ok(BoundaryResult {
        users: placed,
        reset,
    })
}

/// An input being placed: its content, the entry it is placed as when not
/// `pi.user`, and who produced it.
pub(crate) struct PlacedInput {
    pub content: UserContent,
    pub entry: Option<InputEntry>,
    pub origin: InputOrigin,
}

/// Append the entry an input is placed as: `entry`'s kind and data, or
/// `pi.user` with the origin as data, with the user message of `content`.
///
/// # Errors
///
/// Transaction and JSON failures.
pub(crate) async fn append_input(
    tx: &Tx,
    conversation_id: ConversationId,
    input: PlacedInput,
    now: u64,
) -> SessionResult<EntryId> {
    let message = Message::User(UserMessage {
        content: input.content,
        timestamp: now,
    });
    if let Some(InputEntry { kind, data }) = input.entry {
        let draft = EntryDraft {
            kind,
            model: Some(vec![message]),
            data,
            head: None,
            edits: None,
        };
        return Ok(tx.append_entry(conversation_id, draft).await?.id);
    }
    let draft = TypedEntryDraft {
        model: Some(vec![message]),
        data: UserData {
            origin: input.origin,
        },
        head: None,
        edits: None,
    };
    Ok(tx
        .append_typed_entry(&USER_ENTRY, conversation_id, draft)
        .await?
        .id)
}

/// Whether a write is display-only: it has no `model`, `head`, or `edits`
/// (present counts, even if empty), so it changes nothing the model sees and
/// needs no boundary.
#[must_use]
pub fn is_display_only(entry: &EntryDraft) -> bool {
    entry.model.is_none() && entry.head.is_none() && entry.edits.is_none()
}

/// Whether a reset (`head: "self"` write) is queued among the inbox `items`;
/// entries appended before it leave the active range when it lands.
#[must_use]
pub fn has_queued_reset(items: &[JsonValue]) -> bool {
    items.iter().any(|item| {
        mode_of(item) == Some("write")
            && item["entry"].get("head").and_then(JsonValue::as_str) == Some("self")
    })
}

/// Whether a compaction summary (a `pi.compaction` write) is queued among
/// the inbox `items`: admitted, but neither placed nor settled `stale`.
#[must_use]
pub(crate) fn has_queued_summary(items: &[JsonValue]) -> bool {
    items.iter().any(|item| {
        mode_of(item) == Some("write")
            && item["entry"].get("kind").and_then(JsonValue::as_str)
                == Some(crate::entries::COMPACTION_ENTRY.kind())
    })
}

/// Whether a head write targets an entry before the active range, so placing
/// it would bring back cut history.
#[must_use]
pub fn is_stale(boundary: &Boundary, entry: &EntryDraft) -> bool {
    match (entry.head, boundary.head) {
        (Some(EntryHead::Entry(head)), Some(start)) => head < start,
        _ => false,
    }
}

/// An array index as the `i64` Draft positions take; arrays never reach
/// `i64::MAX` items.
fn index_i64(index: usize) -> i64 {
    i64::try_from(index).unwrap_or(i64::MAX)
}

/// The index of the item with submission `id`, if queued.
fn find_item(items: &Draft, id: SubmissionId) -> SessionResult<Option<usize>> {
    for index in 0..items.len()? {
        let item = items.child(index)?;
        if let Some(DraftItem::Value(value)) = item.get("id")? {
            if value.as_u64() == Some(id.get()) {
                return Ok(Some(index));
            }
        }
    }
    Ok(None)
}

/// Remove a withdrawn submission's item; the caller settles the submission.
///
/// # Errors
///
/// Document and tracker failures.
pub async fn remove_inbox_item(
    tx: &Tx,
    conversation_id: ConversationId,
    id: SubmissionId,
) -> SessionResult<()> {
    let items = tx.doc(&INBOX_DOC, conversation_id).await?.child("items")?;
    if let Some(index) = find_item(&items, id)? {
        items.splice(index_i64(index), 1, Vec::<JsonValue>::new())?;
    }
    Ok(())
}

/// Withdraw every queued input of a conversation, as `Conversation.abort()`
/// and abort cascades do: each settles `unanswered` with `aborted` and leaves
/// the inbox; queued writes stay for later placement.
///
/// The future is `'static` so the scheduler can hold it as its
/// `withdraw_inputs` callback.
pub fn withdraw_queued_inputs(
    tx: Tx,
    conversation_id: ConversationId,
) -> BoxFuture<'static, SessionResult<()>> {
    async move {
        let items = tx.doc(&INBOX_DOC, conversation_id).await?.child("items")?;
        let values = items.value()?;
        let values = values.as_array().unwrap_or_default();
        for index in (0..values.len()).rev() {
            let item = &values[index];
            if mode_of(item) == Some("write") {
                continue;
            }
            tx.settle_submission(
                submission_id_of(item)?,
                SubmissionSettlement::Unanswered {
                    reason: "aborted".to_owned(),
                    detail: None,
                },
            )?;
            items.splice(index_i64(index), 1, Vec::<JsonValue>::new())?;
        }
        Ok(())
    }
    .boxed()
}
