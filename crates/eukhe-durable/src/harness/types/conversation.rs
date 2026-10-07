//! Conversation-facing harness types: submissions, invocation-bound
//! conversation handles, creation options, context views, and inspection
//! (TS `SubmissionDraft`, `Submission`, `ConversationHandle`,
//! `ConversationCreateOptions`, `ContextView`, `CompactionResult`,
//! `HarnessInspection`).

use std::fmt;
use std::ops::Deref;
use std::sync::Arc;

use eukhe_chord::context::Context;
use eukhe_types::pi_ai::{Message, UserContent};
use futures::future::BoxFuture;
use serde::{Deserialize, Serialize};

use super::agent::AgentChange;
use crate::session::{SessionError, SessionResult, Tx};
use crate::types::{
    AnyTaskRecord, ConversationId, ConversationOwnership, EntryDraft, EntryId, EntryRecord,
    SubmissionId, SubmissionRecord, TaskId,
};

/// User message content (TS `UserMessage["content"]`).
pub type UserInput = UserContent;

/// What a busy conversation does with an input submission.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum WhenBusy {
    /// `"steer"`.
    Steer,
    /// `"followUp"`.
    FollowUp,
    /// `"reject"`.
    Reject,
}

/// Host submission of user input that may start a run (TS
/// `InputSubmissionDraft`).
#[derive(Debug, Clone, PartialEq)]
pub struct InputSubmissionDraft {
    pub request_id: Option<String>,
    pub content: UserInput,
    pub when_busy: Option<WhenBusy>,
}

impl InputSubmissionDraft {
    /// Input `content` without a request ID or busy mode.
    #[must_use]
    pub fn new(content: impl Into<UserInput>) -> Self {
        Self {
            request_id: None,
            content: content.into(),
            when_busy: None,
        }
    }
}

/// Host submission of a passive entry write.
#[derive(Debug, Clone, PartialEq)]
pub struct WriteSubmissionDraft {
    pub request_id: Option<String>,
    pub entry: EntryDraft,
}

/// Host submission: user input that may start a run, or a passive entry
/// write.
#[derive(Debug, Clone, PartialEq)]
pub enum SubmissionDraft {
    /// `type: "input"`.
    Input(InputSubmissionDraft),
    /// `type: "write"`.
    Write(WriteSubmissionDraft),
}

impl SubmissionDraft {
    /// The idempotency key, when given.
    #[must_use]
    pub fn request_id(&self) -> Option<&str> {
        match self {
            Self::Input(draft) => draft.request_id.as_deref(),
            Self::Write(draft) => draft.request_id.as_deref(),
        }
    }
}

impl From<InputSubmissionDraft> for SubmissionDraft {
    fn from(draft: InputSubmissionDraft) -> Self {
        Self::Input(draft)
    }
}

impl From<WriteSubmissionDraft> for SubmissionDraft {
    fn from(draft: WriteSubmissionDraft) -> Self {
        Self::Write(draft)
    }
}

/// A submission record whose status is `done` or `unanswered`.
#[derive(Debug, Clone, PartialEq)]
pub struct SettledSubmissionRecord(SubmissionRecord);

impl SettledSubmissionRecord {
    /// The record.
    #[must_use]
    pub fn record(&self) -> &SubmissionRecord {
        &self.0
    }

    /// The record.
    #[must_use]
    pub fn into_record(self) -> SubmissionRecord {
        self.0
    }
}

impl TryFrom<SubmissionRecord> for SettledSubmissionRecord {
    type Error = SubmissionRecord;

    /// `Err(record)` unless the record is settled.
    fn try_from(record: SubmissionRecord) -> Result<Self, SubmissionRecord> {
        if record.state.is_settled() {
            Ok(Self(record))
        } else {
            Err(record)
        }
    }
}

impl Deref for SettledSubmissionRecord {
    type Target = SubmissionRecord;

    fn deref(&self) -> &SubmissionRecord {
        &self.0
    }
}

/// Result of aborting one submission.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SubmissionAbort {
    /// `"aborted"`: withdrawn while queued.
    Aborted,
    /// `"already_placed"`.
    AlreadyPlaced,
    /// `"settled"`.
    Settled,
}

impl SubmissionAbort {
    /// The TS string.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Aborted => "aborted",
            Self::AlreadyPlaced => "already_placed",
            Self::Settled => "settled",
        }
    }
}

/// Awaitable host object for one durably admitted submission (TS
/// `Submission`). The Harness implements it; handles are
/// `Arc<dyn Submission>`. Invocation-bound handles reject after their
/// invocation ends.
pub trait Submission: Send + Sync {
    fn id(&self) -> SubmissionId;
    /// The current record.
    fn status(&self, cx: &Context) -> BoxFuture<'static, SessionResult<SubmissionRecord>>;
    /// Resolve once the submission is settled.
    fn wait(&self, cx: &Context) -> BoxFuture<'static, SessionResult<SettledSubmissionRecord>>;
    /// Withdraw the submission when still queued.
    fn abort(&self, cx: &Context) -> BoxFuture<'static, SessionResult<SubmissionAbort>>;
}

/// Options of `Conversation.abort()`.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ConversationAbortOptions {
    /// Cross background boundaries: mark every live task reached ignoring
    /// the background flag when the abort is admitted, withdraw the queued
    /// inputs of every conversation reached, and wait until those tasks are
    /// terminal and the conversation is ordinarily idle. Background work
    /// created afterwards is neither marked nor awaited.
    pub background: bool,
}

/// Invocation-bound conversation operations for tasks and tools (TS
/// `ConversationHandle`). The Harness implements it; every operation rejects
/// after the invocation ends. Passive entries are written with ordinary
/// transaction writes instead.
pub trait ConversationHandle: Send + Sync {
    fn id(&self) -> ConversationId;
    fn submit(
        &self,
        submission: InputSubmissionDraft,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Arc<dyn Submission>>>;
    /// `Conversation.abort()`: withdraw queued inputs, abort the ordinary
    /// ownership scope, and wait until it is idle.
    fn abort(
        &self,
        options: ConversationAbortOptions,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<()>>;
    /// Resolve when the conversation's ordinary ownership scope has no live
    /// non-background task.
    fn wait_for_idle(&self, cx: &Context) -> BoxFuture<'static, SessionResult<()>>;
}

/// Runs inside the creating commit, after the creation hook and the `agent`
/// change. The conversation creation is already a table write, so table
/// reads here fail with `ReadAfterWrite`; document access remains available.
pub type ConversationInit =
    Box<dyn FnOnce(Tx, ConversationId) -> BoxFuture<'static, SessionResult<()>> + Send>;

/// Options of creating or forking a conversation.
pub struct ConversationCreateOptions {
    pub ownership: ConversationOwnership,
    /// Applied in the creating commit after the creation hook's copy, before
    /// `init`.
    pub agent: Option<AgentChange>,
    pub init: Option<ConversationInit>,
}

impl ConversationCreateOptions {
    /// Options with only `ownership`.
    #[must_use]
    pub fn new(ownership: ConversationOwnership) -> Self {
        Self {
            ownership,
            agent: None,
            init: None,
        }
    }
}

impl fmt::Debug for ConversationCreateOptions {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ConversationCreateOptions")
            .field("ownership", &self.ownership)
            .field("agent", &self.agent)
            .field("init", &self.init.is_some())
            .finish()
    }
}

/// Raw active transcript and derived model context.
#[derive(Debug, Clone, PartialEq)]
pub struct ContextView {
    /// Newest applicable head marker, if any.
    pub head: Option<EntryRecord>,
    /// Raw active entries: the head marker followed by non-head entries from
    /// its head through the tail.
    pub entries: Vec<EntryRecord>,
    /// Per entry of `entries`, its model messages after edits and excluded
    /// stop reasons, before tool result ordering.
    pub contributions: Vec<Vec<Message>>,
    /// Model context for the next provider request.
    pub messages: Vec<Message>,
}

/// `entry_id` of a blocking compaction's summary, or the `submission_id` of
/// a conversation-owned compaction's summary write; both absent when nothing
/// was compacted.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CompactionResult {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub entry_id: Option<EntryId>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub submission_id: Option<SubmissionId>,
}

/// Whether the Harness schedules tasks.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SchedulingState {
    /// `"paused"`.
    Paused,
    /// `"running"`.
    Running,
    /// `"closing"`.
    Closing,
}

/// Why no registered definition can take a task.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TaskBlockedReason {
    /// `"missing_task"`.
    MissingTask,
    /// `"task_too_old"`.
    TaskTooOld,
    /// `"migration_failed"`.
    MigrationFailed,
}

impl TaskBlockedReason {
    /// The TS string.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::MissingTask => "missing_task",
            Self::TaskTooOld => "task_too_old",
            Self::MigrationFailed => "migration_failed",
        }
    }
}

/// What the scheduler would do with a live task under the current registry.
#[derive(Debug, Clone)]
pub enum TaskInspectionState {
    /// An invocation is active.
    Running,
    /// The next scheduling pass reserves it; `migrates` when its definition
    /// is newer and has `migrate`.
    Ready { migrates: bool },
    /// Waits for these live tasks: the live part of its `on`, or, when
    /// abort-marked, its live ordinary owned work, which must end before its
    /// abort handler starts.
    Waiting { on: Vec<TaskId> },
    /// Outcome held until its ordinary owned work drains.
    Completing,
    /// No registered definition can take it; aborting it settles it as
    /// `orphaned`.
    Blocked {
        reason: TaskBlockedReason,
        error: Option<SessionError>,
    },
}

/// Live task and what the scheduler would do with it.
#[derive(Debug, Clone)]
pub struct TaskInspection {
    pub record: AnyTaskRecord,
    pub state: TaskInspectionState,
}

/// Point-in-time view of live work: unfinished tasks and submissions, read
/// on the Session line.
#[derive(Debug, Clone)]
pub struct HarnessInspection {
    pub scheduling: SchedulingState,
    pub tasks: Vec<TaskInspection>,
    /// Queued and placed submissions, in ID order.
    pub submissions: Vec<SubmissionRecord>,
}
