//! Scans, storage writes, commit publications, and the [`Storage`] contract
//! (`types.ts`, spec §10).

use std::ops::Deref;
use std::sync::Arc;

use eukhe_chord::context::Context;
use eukhe_chord::delta::Op;
use eukhe_chord::json::{JsonObject, JsonValue};
use futures::future::BoxFuture;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use super::documents::{
    DocumentAddress, DocumentBase, DocumentContent, DocumentCopySource, DocumentCreate,
    DocumentPoint, DocumentRecord, DocumentScope, StoredDocument,
};
use super::ids::{ConversationId, DocumentId, EntryId, Seq, SubmissionId, TaskId};
use super::json_serde::into_object;
use super::submissions::{SubmissionRecord, SubmissionStatus};
use super::tasks::{AnyTaskRecord, TaskStatus};
use super::transcript::{ConversationRecord, EntryRecord};
use crate::errors::StorageError;

/// One ordered scan result and its optional continuation state.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Page<T, C = Cursor> {
    /// The results, at most the requested limit.
    pub items: Vec<T>,
    /// Continuation state; absent when the scan is complete.
    #[serde(default = "no_cursor", skip_serializing_if = "Option::is_none")]
    pub next: Option<C>,
}

/// `#[serde(default)]` for `Option<C>` without a `C: Default` bound.
fn no_cursor<C>() -> Option<C> {
    None
}

/// Backend-owned JSON continuation state that callers only round-trip to the
/// same scan on the same storage.
#[derive(Debug, Clone, PartialEq)]
pub struct Cursor(Arc<JsonObject>);

impl Cursor {
    /// A cursor holding `state`.
    #[must_use]
    pub fn new(state: JsonObject) -> Self {
        Self(Arc::new(state))
    }

    /// The JSON state.
    #[must_use]
    pub fn state(&self) -> &Arc<JsonObject> {
        &self.0
    }
}

impl From<JsonObject> for Cursor {
    fn from(state: JsonObject) -> Self {
        Self::new(state)
    }
}

impl From<Arc<JsonObject>> for Cursor {
    fn from(state: Arc<JsonObject>) -> Self {
        Self(state)
    }
}

impl Deref for Cursor {
    type Target = JsonObject;

    fn deref(&self) -> &JsonObject {
        &self.0
    }
}

impl Serialize for Cursor {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_map(self.0.iter())
    }
}

impl<'de> Deserialize<'de> for Cursor {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        into_object(JsonValue::deserialize(deserializer)?).map(Self)
    }
}

/// ID order of a scan: `ascending` is oldest first, `descending` newest first.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum ScanOrder {
    /// Oldest first.
    Ascending,
    /// Newest first.
    Descending,
}

impl ScanOrder {
    /// The TS string.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Ascending => "ascending",
            Self::Descending => "descending",
        }
    }
}

/// Optional filters for an ordered conversation scan; owner filters are indexed and conjunctive.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ConversationQuery {
    /// Only conversations owned by a task of this conversation.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub owner_conversation_id: Option<ConversationId>,
    /// Only conversations owned by this task.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub owner_task_id: Option<TaskId>,
    /// Default `ascending`; with a cursor, the cursor's order.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub order: Option<ScanOrder>,
}

/// Inclusive ID bounds for a scan of one conversation's fork-aware history.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct EntryQuery {
    /// The conversation whose visible history is scanned.
    pub conversation_id: ConversationId,
    /// Oldest entry ID that may be returned.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub min_entry_id: Option<EntryId>,
    /// Newest entry ID that may be returned.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub max_entry_id: Option<EntryId>,
    /// Default `descending`; with a cursor, the cursor's order.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub order: Option<ScanOrder>,
}

impl EntryQuery {
    /// The unbounded scan of one conversation's visible history.
    #[must_use]
    pub fn new(conversation_id: ConversationId) -> Self {
        Self {
            conversation_id,
            min_entry_id: None,
            max_entry_id: None,
            order: None,
        }
    }
}

/// Optional filters for an ordered scan of durable task records.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TaskQuery {
    /// Only tasks of this conversation.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub conversation_id: Option<ConversationId>,
    /// Only tasks of this definition name.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub kind: Option<String>,
    /// Only tasks in this state.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub status: Option<TaskStatus>,
    /// Only tasks with or without an abort mark.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub abort_requested: Option<bool>,
    /// Only background or ordinary tasks.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub background: Option<bool>,
    /// Default `ascending`; with a cursor, the cursor's order.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub order: Option<ScanOrder>,
}

/// Optional filters for an ordered scan of submission records.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SubmissionQuery {
    /// Only submissions of this conversation.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub conversation_id: Option<ConversationId>,
    /// Only submissions with this status.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub status: Option<SubmissionStatus>,
    /// Default `ascending`; with a cursor, the cursor's order.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub order: Option<ScanOrder>,
}

/// Ordered scan of document incarnations alive in one exact scope at one point.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DocumentQuery {
    /// The exact scope.
    pub scope: DocumentScope,
    /// The membership point.
    pub at: DocumentPoint,
    /// Only incarnations of this definition kind.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub kind: Option<String>,
}

/// One global entry and the sequence of the commit that persisted it.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct StoredEntry {
    /// The entry.
    pub entry: EntryRecord,
    /// The commit that persisted it.
    pub commit_seq: Seq,
}

/// One record or document mutation in an atomic storage commit.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum StorageWrite {
    /// Create a conversation (immutable once created).
    #[serde(rename = "conversation")]
    Conversation {
        /// The record.
        value: ConversationRecord,
    },
    /// Create an entry (immutable once created).
    #[serde(rename = "entry")]
    Entry {
        /// The record.
        value: EntryRecord,
    },
    /// Create or replace a task record.
    #[serde(rename = "task")]
    Task {
        /// The complete record.
        value: AnyTaskRecord,
    },
    /// Create or replace a submission record.
    #[serde(rename = "submission")]
    Submission {
        /// The complete record.
        value: SubmissionRecord,
    },
    /// Create an incarnation from a complete base.
    #[serde(rename = "document.create")]
    DocumentCreate {
        /// The incarnation to create.
        record: DocumentCreate,
        /// Its first content; creation always starts from a complete base.
        content: DocumentBase,
    },
    /// Create an incarnation as an independent copy of committed source state.
    #[serde(rename = "document.copy")]
    DocumentCopy {
        /// The incarnation to create.
        record: DocumentCreate,
        /// The source state, read from pre-batch committed state.
        source: DocumentCopySource,
    },
    /// Store a new base or delta for an existing incarnation.
    #[serde(rename = "document.change")]
    DocumentChange {
        /// The incarnation.
        id: DocumentId,
        /// The new content.
        content: DocumentContent,
    },
    /// Retire an incarnation; applied after content in the same batch.
    #[serde(rename = "document.retire")]
    DocumentRetire {
        /// The incarnation.
        id: DocumentId,
    },
}

/// Committed change of one document incarnation.
#[derive(Debug, Clone, PartialEq)]
pub enum DocumentCommitChange {
    /// `type: "document"`: creation, ordinary update, or retirement.
    Document {
        /// The incarnation's record after the commit.
        record: DocumentRecord,
        /// Conversation owning the document; task documents derive it from
        /// their task record. `None` only for Session documents.
        conversation_id: Option<ConversationId>,
        /// Definition version of `value`; `None` when this commit retired the incarnation.
        version: Option<u64>,
        /// Exact adopted immutable revision; `None` (TS `null`) when this commit
        /// retired the incarnation.
        value: Option<Arc<JsonObject>>,
        /// Exact adopted operations for an ordinary update; empty for creation and retirement.
        ops: Arc<[Op]>,
    },
    /// `type: "document.copy"`: definition-free child initialization;
    /// consumers hydrate through state or watch acquisition.
    Copy {
        /// The created incarnation's record.
        record: DocumentRecord,
        /// The child conversation.
        conversation_id: ConversationId,
        /// The copied source.
        source: DocumentCopySource,
    },
}

/// One change of a successful Session commit: a complete table record
/// (TS `TableCommitChange`, the table members of [`StorageWrite`]) or a
/// document change.
#[derive(Debug, Clone, PartialEq)]
pub enum CommitChange {
    /// A created conversation.
    Conversation(ConversationRecord),
    /// A created entry.
    Entry(EntryRecord),
    /// A created or replaced task record.
    Task(AnyTaskRecord),
    /// A created or replaced submission record.
    Submission(SubmissionRecord),
    /// A document change.
    Document(DocumentCommitChange),
}

/// Every immutable change from one successful Session commit. Change order is unspecified.
#[derive(Debug, Clone, PartialEq)]
pub struct CommitPublication {
    /// The commit's sequence.
    pub seq: Seq,
    /// The changes.
    pub changes: Vec<CommitChange>,
}

/// Atomic persistence boundary for Session records.
///
/// Storage trusts the owning Session to supply semantically valid records,
/// references, ancestry, and transitions. Implementations enforce atomicity,
/// global ID ownership, immutable conversation/entry creation, document record
/// consistency, and detached values; the Session serializes commits, so
/// implementations add no second caller-facing commit mutex. Sequences
/// strictly increase but may have gaps.
///
/// Errors: an error a method returns is final: it fails the Session, which
/// nothing retries, so retry transient failures inside the method. Two errors
/// of a read fail only that read: a [`StorageError::Request`] for an invalid
/// request (an unknown conversation, a foreign or malformed cursor, history a
/// document does not keep), which must have no durable effect, and a failure
/// because its caller's context was cancelled. Any error from `commit()` or
/// `mint_id()` is fatal.
///
/// Cursors carry the scan's order: a scan given a cursor continues in that
/// order, and rejects a different `order` in its query.
///
/// Cursors are backend-owned JSON objects that callers only round-trip to the
/// same scan on the same storage. `limit` is always the maximum page size.
pub trait Storage: Send + Sync {
    /// Atomically persist one batch and return its sequence. Once resolved,
    /// later reads through this storage observe it.
    ///
    /// One normalized batch contains at most one create/change content command
    /// per incarnation and may also retire that incarnation; content applies
    /// before retirement independent of write order. Create plus retire stamps
    /// both lifetime bounds with the batch sequence; retire plus create at one
    /// logical address makes the new incarnation current at that sequence.
    /// Deltas cannot cross a stored version boundary; a version transition
    /// must be a base. A `document.copy` reads committed pre-batch source state
    /// independent of command order: the source must be an alive conversation
    /// document at the selected point whose kind/key/history/fork match the
    /// child create record; storage persists one independent complete child
    /// base at the source's stored version, and the batch may not create,
    /// change, or retire a selected source.
    fn commit<'a>(
        &'a self,
        writes: &'a [StorageWrite],
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Seq, StorageError>>;

    /// Return a fresh candidate from the Session-global numeric ID namespace,
    /// greater than every ID minted or stored before, also across reopen:
    /// scans order by ID as creation order, and the Harness relies on it;
    /// brand it with [`crate::ids::id_from_number`] or use [`crate::ids::mint`].
    fn mint_id(&self) -> BoxFuture<'_, Result<u64, StorageError>>;

    /// Look up one conversation by exact ID.
    fn conversation<'a>(
        &'a self,
        id: ConversationId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<ConversationRecord>, StorageError>>;

    /// Scan conversations in `query.order` (default ascending) by ID.
    fn scan_conversations<'a>(
        &'a self,
        query: &'a ConversationQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<ConversationRecord>, StorageError>>;

    /// Look up one global entry and the sequence of the commit that persisted
    /// it (the TS `entry(id)` overload).
    fn entry<'a>(
        &'a self,
        id: EntryId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<StoredEntry>, StorageError>>;

    /// Look up one entry only when it is visible through the requested
    /// conversation's ancestry (the TS `entry(conversationId, id)` overload).
    fn entry_in<'a>(
        &'a self,
        conversation_id: ConversationId,
        id: EntryId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<StoredEntry>, StorageError>>;

    /// Return the newest visible entry with a `head` at or below the optional
    /// inclusive cutoff. The returned entry is the marker; its `head` value is
    /// the range's actual lower bound. To read context through entry `E`, find
    /// the marker at or before `E`, then scan from `marker.head` through `E`.
    fn find_latest_head_marker<'a>(
        &'a self,
        conversation_id: ConversationId,
        at_or_before_entry_id: Option<EntryId>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<EntryRecord>, StorageError>>;

    /// Scan the inclusive visible range in `query.order` (default
    /// descending), returning at most `limit` entries and applying every
    /// conversation ancestry cap; oldest first, it reads the root's segment
    /// first and then each fork's. With no bounds it pages complete visible
    /// history.
    fn scan_entries<'a>(
        &'a self,
        query: &'a EntryQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<EntryRecord>, StorageError>>;

    /// Look up the latest complete record for one task.
    fn task<'a>(
        &'a self,
        id: TaskId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<AnyTaskRecord>, StorageError>>;

    /// Scan task records matching every supplied filter in `query.order`
    /// (default ascending) by ID.
    fn scan_tasks<'a>(
        &'a self,
        query: &'a TaskQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<AnyTaskRecord>, StorageError>>;

    /// Look up the latest complete record for one admitted submission.
    fn submission<'a>(
        &'a self,
        id: SubmissionId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<SubmissionRecord>, StorageError>>;

    /// Scan submissions matching every supplied filter in `query.order`
    /// (default ascending) by ID.
    fn scan_submissions<'a>(
        &'a self,
        query: &'a SubmissionQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<SubmissionRecord>, StorageError>>;

    /// Find a submission by its conversation-scoped host deduplication key.
    fn submission_by_request<'a>(
        &'a self,
        conversation_id: ConversationId,
        request_id: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<SubmissionRecord>, StorageError>>;

    /// Resolve the incarnation occupying one exact logical address at the
    /// selected point. A missing key means the singleton, not every family member.
    fn find_document<'a>(
        &'a self,
        address: &'a DocumentAddress,
        at: DocumentPoint,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<DocumentRecord>, StorageError>>;

    /// Materialize one specific incarnation by ID at the selected point
    /// without following a replacement at its address.
    ///
    /// Selects the newest applicable base and applies its ordered delta tail.
    /// An unknown ID returns `None`; at `Current` a retired incarnation returns
    /// `None`. A numeric lookup of a rewindable conversation incarnation
    /// returns `None` outside its half-open lifetime and reconstructs the value
    /// inside it; a numeric lookup of a known current-only incarnation rejects.
    /// A missing required base, a version change inside a delta tail, or an
    /// operation that cannot be applied inside an addressable lifetime is
    /// storage corruption, not absence.
    fn document<'a>(
        &'a self,
        id: DocumentId,
        at: DocumentPoint,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<StoredDocument>, StorageError>>;

    /// Scan incarnations alive in one exact scope at the selected point, in
    /// ascending incarnation ID order, optionally restricted to one kind.
    fn scan_documents<'a>(
        &'a self,
        query: &'a DocumentQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<DocumentRecord>, StorageError>>;

    /// Release backend resources; all later operations must reject.
    fn close<'a>(&'a self, cx: &'a Context) -> BoxFuture<'a, Result<(), StorageError>>;
}
