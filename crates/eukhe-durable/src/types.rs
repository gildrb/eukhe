//! Durable records, scans, writes, and the [`Storage`] contract (`types.ts`,
//! spec §2, §3, §10).
//!
//! Every record serializes to the JSON the TS package writes: camelCase keys
//! in the TS construction order, optional fields omitted when absent, IDs as
//! plain numbers. Open JSON is [`eukhe_chord::json::JsonValue`]; JSON objects
//! a record shares with the Session (document values, memos, cursors) are
//! `Arc<JsonObject>` so they are never copied.
//!
//! The Session-facing interfaces of `types.ts` (`Tx`, `Session`, watches)
//! live with the Session; `DocumentReader` and `DocumentObserver` are
//! object-safe traits (`types/readers.rs`); task definitions and runtimes live in
//! [`crate::tasks`].

#[cfg(doctest)]
pub mod compile_checks;
mod documents;
mod ids;
pub(crate) mod json_serde;
mod readers;
mod storage;
mod submissions;
mod tasks;
#[cfg(test)]
mod tests;
mod transcript;

/// JSON object used as the root of every durable document.
pub use eukhe_chord::json::JsonObject;

pub use documents::{
    CheckpointInfo, ConversationSemantics, DocumentAddress, DocumentBase, DocumentContent,
    DocumentCopySource, DocumentCreate, DocumentDelta, DocumentFork, DocumentHistory,
    DocumentIdentity, DocumentPoint, DocumentRecord, DocumentRecordScope, DocumentScope,
    DocumentSemantics, LatestFork, RewindableFork, StoredDocument,
};
pub use ids::{
    ConversationId, DocumentId, DurableId, EntryId, Seq, SubmissionId, TaskId, ROOT_CONVERSATION_ID,
};
pub use readers::{DocumentObserver, DocumentObserverExt, DocumentReader, DocumentReaderExt};
pub use storage::{
    CommitChange, CommitPublication, ConversationQuery, Cursor, DocumentCommitChange,
    DocumentQuery, EntryQuery, Page, ScanOrder, Storage, StorageWrite, StoredEntry,
    SubmissionQuery, TaskQuery,
};
pub use submissions::{
    InputSubmission, SubmissionCreate, SubmissionRecord, SubmissionSettlement, SubmissionState,
    SubmissionStatus, SubmissionType, WriteSubmission,
};
pub use tasks::{
    AnyTaskRecord, JoinPolicy, TaskAbortReason, TaskOptions, TaskOutcome, TaskOutcomeError,
    TaskOutcomeStatus, TaskOwnership, TaskRecord, TaskState, TaskStatus,
};
pub use transcript::{
    ContextEdit, ContextEditAction, ConversationOwner, ConversationOwnership, ConversationParent,
    ConversationRecord, EntryData, EntryDraft, EntryHead, EntryRecord, NoData, TypedEntry,
    TypedEntryDraft,
};
