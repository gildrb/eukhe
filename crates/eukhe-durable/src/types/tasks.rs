//! Task records, states, and outcomes (`types.ts`, spec §5).

use std::sync::Arc;

use eukhe_chord::json::{JsonObject, JsonValue};
use serde::{Deserialize, Serialize};

use super::ids::{ConversationId, TaskId};
use super::json_serde::{option_object, present};

/// Who owns a task: its conversation (a top-level task) or another task of
/// the same conversation (a child task).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(
    tag = "kind",
    rename_all = "camelCase",
    rename_all_fields = "camelCase"
)]
pub enum TaskOwnership {
    /// A top-level task owned by its conversation.
    Conversation,
    /// A child task owned by another task of the same conversation.
    Task {
        /// The owning task.
        task_id: TaskId,
    },
}

/// How a waiting task treats the tasks it waits on (spec §5.5).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum JoinPolicy {
    /// Resume as soon as one awaited task fails.
    FailFast,
    /// Resume once every awaited task is terminal.
    AllSettled,
}

/// Creation options for a durable task.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TaskOptions {
    /// Required: a task always names its owner (spec §5.5).
    pub ownership: TaskOwnership,
    /// Default: the owner task's conversation, or the transaction's bound
    /// conversation; required for conversation-owned tasks created by Session
    /// commits that are not bound to a conversation.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub conversation_id: Option<ConversationId>,
    /// Conversation-owned tasks only: excluded from ordinary idle waits,
    /// conversation aborts, and cascades.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub background: Option<bool>,
}

/// JSON-safe error snapshot persisted instead of a runtime error object.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TaskOutcomeError {
    /// The error message.
    pub message: String,
    /// Optional structured diagnostic data for inspection or recovery.
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        deserialize_with = "present"
    )]
    pub detail: Option<JsonValue>,
}

/// Durable reason and optional result recorded when a task becomes terminal.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "status", rename_all = "camelCase")]
pub enum TaskOutcome<R = JsonValue> {
    /// The task produced its result.
    Completed {
        /// The task result.
        result: R,
    },
    /// Expected task or domain failure explicitly committed by its implementation.
    Failed {
        /// The failure.
        error: TaskOutcomeError,
        /// An optional partial result.
        #[serde(
            default = "none",
            skip_serializing_if = "Option::is_none",
            deserialize_with = "present"
        )]
        result: Option<R>,
    },
    /// Explicit cancellation handled by the task's abort protocol.
    Aborted {
        /// Why the task was aborted.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        reason: Option<String>,
        /// An optional partial result.
        #[serde(
            default = "none",
            skip_serializing_if = "Option::is_none",
            deserialize_with = "present"
        )]
        result: Option<R>,
    },
    /// Task that cannot resume because its definition or migration is unavailable.
    Orphaned {
        /// Why the task cannot resume.
        reason: String,
    },
    /// Runtime-detected contract failure, such as an uncaught throw or no durable progress.
    Faulted {
        /// The fault.
        error: TaskOutcomeError,
    },
}

/// `#[serde(default)]` for `Option<R>` without an `R: Default` bound.
fn none<R>() -> Option<R> {
    None
}

/// Status of a task outcome (TS `TaskOutcome["status"]`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum TaskOutcomeStatus {
    /// See [`TaskOutcome::Completed`].
    Completed,
    /// See [`TaskOutcome::Failed`].
    Failed,
    /// See [`TaskOutcome::Aborted`].
    Aborted,
    /// See [`TaskOutcome::Orphaned`].
    Orphaned,
    /// See [`TaskOutcome::Faulted`].
    Faulted,
}

impl<R> TaskOutcome<R> {
    /// The outcome status.
    #[must_use]
    pub fn status(&self) -> TaskOutcomeStatus {
        match self {
            Self::Completed { .. } => TaskOutcomeStatus::Completed,
            Self::Failed { .. } => TaskOutcomeStatus::Failed,
            Self::Aborted { .. } => TaskOutcomeStatus::Aborted,
            Self::Orphaned { .. } => TaskOutcomeStatus::Orphaned,
            Self::Faulted { .. } => TaskOutcomeStatus::Faulted,
        }
    }
}

/// Complete durable execution state of a task.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "status", rename_all = "camelCase")]
pub enum TaskState<S = JsonValue, R = JsonValue> {
    /// Eligible for scheduling.
    Pending {
        /// Complete durable state from which execution resumes.
        checkpoint: S,
    },
    /// Reserved by one in-memory task invocation.
    Running {
        /// Complete durable state from which execution resumes.
        checkpoint: S,
    },
    /// Parked without an invocation until every task in `on` is terminal; then
    /// resumes at `checkpoint`.
    Waiting {
        /// Complete durable state from which execution resumes.
        checkpoint: S,
        /// The awaited tasks.
        on: Vec<TaskId>,
        /// How failures of awaited tasks are treated.
        policy: JoinPolicy,
    },
    /// Outcome decided; becomes terminal once no ordinary owned work below is
    /// live. Runs no more code.
    Completing {
        /// The decided outcome.
        outcome: TaskOutcome<R>,
    },
    /// Permanently settled durable result receipt.
    Terminal {
        /// The final outcome.
        outcome: TaskOutcome<R>,
    },
}

/// Status of a task state (TS `TaskState["status"]`), used by [`TaskQuery`](super::TaskQuery).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum TaskStatus {
    /// See [`TaskState::Pending`].
    Pending,
    /// See [`TaskState::Running`].
    Running,
    /// See [`TaskState::Waiting`].
    Waiting,
    /// See [`TaskState::Completing`].
    Completing,
    /// See [`TaskState::Terminal`].
    Terminal,
}

impl<S, R> TaskState<S, R> {
    /// The state status.
    #[must_use]
    pub fn status(&self) -> TaskStatus {
        match self {
            Self::Pending { .. } => TaskStatus::Pending,
            Self::Running { .. } => TaskStatus::Running,
            Self::Waiting { .. } => TaskStatus::Waiting,
            Self::Completing { .. } => TaskStatus::Completing,
            Self::Terminal { .. } => TaskStatus::Terminal,
        }
    }

    /// The checkpoint of a live (`pending`, `running`, or `waiting`) state.
    #[must_use]
    pub fn checkpoint(&self) -> Option<&S> {
        match self {
            Self::Pending { checkpoint }
            | Self::Running { checkpoint }
            | Self::Waiting { checkpoint, .. } => Some(checkpoint),
            Self::Completing { .. } | Self::Terminal { .. } => None,
        }
    }

    /// The outcome of a `completing` or `terminal` state.
    #[must_use]
    pub fn outcome(&self) -> Option<&TaskOutcome<R>> {
        match self {
            Self::Completing { outcome } | Self::Terminal { outcome } => Some(outcome),
            Self::Pending { .. } | Self::Running { .. } | Self::Waiting { .. } => None,
        }
    }
}

/// Complete replacement record for one durable task state machine.
///
/// `memos` is only retained while the state is `pending`, `running`, or
/// `waiting`; TS enforces that in the type, Rust leaves it to the Session.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TaskRecord<I = JsonValue, S = JsonValue, R = JsonValue> {
    /// The task's ID.
    pub id: TaskId<R>,
    /// The conversation the task lives in.
    pub conversation_id: ConversationId,
    /// Registered task definition name.
    pub kind: String,
    /// Definition version used to migrate live input and checkpoints.
    pub version: u64,
    /// Original task input retained while the task is live or terminal.
    pub input: I,
    /// Owning task of a child task; absent for a task its conversation owns. Immutable.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub owner: Option<TaskId>,
    /// Whether this conversation-owned task is excluded from ordinary idle
    /// waits, conversation aborts, and cascades.
    pub background: bool,
    /// Durable abort mark checked before run-mode progress is committed.
    pub abort_requested: bool,
    /// The execution state.
    pub state: TaskState<S, R>,
    /// Small first-writer-wins values retained while the task can run.
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        with = "option_object"
    )]
    pub memos: Option<Arc<JsonObject>>,
}

/// A task record with JSON input, checkpoint, and result, as storage holds it
/// (TS `TaskRecord<JsonValue, JsonValue, JsonValue>`).
pub type AnyTaskRecord = TaskRecord<JsonValue, JsonValue, JsonValue>;
