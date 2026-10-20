//! The child-session host seam: the supervisor operations an
//! `eukhe.rlm.child` task drives, narrowed to primitives.
//!
//! The host is a set of idempotent primitives rather than an in-memory
//! owner of the child lifecycle (spawn, settle watching, the terminal
//! notice, the roster): the lifecycle lives in the parent's durable
//! task, so it survives a parent restart. Every mutating call carries an
//! explicit idempotency key; a rerun after a crash repeats the call with the
//! same key and must observe the first call's effect, never a second one.

use crate::child_workspace::{Handback, WorkspaceMode};
use eukhe_types::input_origin::ChildFailure;
use eukhe_types::pi_ai::Usage;
use futures::future::BoxFuture;
use serde::{Deserialize, Serialize};

/// One pending host call. Boxed because the host crosses the
/// eukhe-core/eukhe-daemon boundary as a dyn object.
pub type RlmHostFuture<'a, T> = BoxFuture<'a, anyhow::Result<T>>;

/// The identity of one child session, derived from the parent session id
/// and the child task id, so a rerun of the spawn names the same child.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RlmChildIdentity {
    /// Roster id (`sub-<8 hex>`), the kernel-visible child handle.
    pub rlm_child_id: String,
    /// Durable session id (UUID) of the child session.
    pub session_id: String,
}

/// Create one recursive child session (no prompt yet).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RlmChildSpawnRequest {
    /// `rlm:<taskId>:spawn`.
    pub idempotency_key: String,
    pub child: RlmChildIdentity,
    /// The resolved session name (explicit or the default slug).
    pub name: String,
    /// The task prompt, mirrored into the child's runtime metadata.
    pub prompt: String,
    /// Model reference (selector or short form); `None` inherits the
    /// parent's. The host resolves it against its allowlist.
    pub model: Option<String>,
    /// Validated thinking level; the host checks model support. `None`
    /// inherits the parent's.
    pub thinking: Option<String>,
    /// The child's recursion depth (parent depth + 1).
    pub depth: u32,
    /// The depth bound the child inherits.
    pub max_depth: u32,
    /// The parent's in-flight request the spawn anchors to (TS
    /// `spawnedByRequestId`).
    pub spawned_by_request_id: Option<String>,
    /// The parent's durable task that owns the child (`eukhe.rlm.child`).
    pub parent_task_id: String,
    /// Where the child works: the parent's directory or its own
    /// copy-on-write copy of the parent's workspace.
    pub workspace: WorkspaceMode,
}

/// The created (or, on a repeated key, the previously created) child.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RlmChildSession {
    /// The supervisor routing id of the child session.
    pub active_session_id: String,
    /// The persisted session id; equals the requested identity's.
    pub session_id: String,
    /// The session name the supervisor admitted.
    pub session_name: String,
    /// Directory holding the child's durable session.
    pub session_dir: String,
    /// The resolved `provider/id` model selector.
    pub model: String,
}

/// Prompt a created child with its task, once per key. The host admits the
/// task as the parent's spawn kickoff (TS `spawnMessage`): an
/// `agent_message` row from the parent labeled `[task from parent]`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RlmChildPromptRequest {
    /// `rlm:<taskId>:prompt`.
    pub idempotency_key: String,
    pub session_id: String,
    /// The child's roster id: the kickoff row's id is `spawn:<rlm_child_id>`.
    pub rlm_child_id: String,
    pub prompt: String,
}

/// Take an isolated child's workspace changes back into the parent's.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RlmChildHandbackRequest {
    pub session_id: String,
    pub rlm_child_id: String,
}

/// Long-poll one child until its run settles or the budget ends.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RlmChildWaitRequest {
    pub session_id: String,
    /// The child's roster id: a settled run completes the child's display
    /// entry (`rlm-subagent.json`) in its per-child directory.
    pub rlm_child_id: String,
    /// The long-poll budget; returning earlier with `Running` is allowed.
    pub timeout_ms: u64,
}

/// What one wait observed.
#[derive(Debug, Clone, PartialEq)]
pub struct RlmChildObservation {
    pub state: RlmChildRunState,
    /// The child's cumulative billable usage (its own spend plus its
    /// descendants'); `None` when the host has nothing to report yet.
    pub usage: Option<Usage>,
    /// The child's progress token ([`RlmChildOutcome::progress`]); `None`
    /// when the observation did not read the child's outcome.
    pub progress: Option<u64>,
    /// The full text of the child's final answer, once it answered
    /// ([`RlmChildOutcome::answer`]).
    pub answer: Option<String>,
}

/// A child's `get_run_outcome` reply: its run state and its progress
/// token. The token changes when the child or one of its unsettled
/// descendants does new work (a tool call with a result it did not have
/// before, or an accepted progress note: [`super::WorkLedger`]; or output
/// a job of its kernel wrote). Events alone (streamed deltas, retries,
/// answers, a repeat of the same calls with the same results) do not
/// change it: the parent's watch reports a child whose token stays the
/// same for `subagentStallMs` as stalled. A worker started by an older
/// binary sends no token (`None`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RlmChildOutcome {
    #[serde(flatten)]
    pub state: RlmChildRunState,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub progress: Option<u64>,
    /// The full text of the child's last assistant answer, capped at
    /// [`RLM_CHILD_ANSWER_MAX_BYTES`]; `None` while it runs, after a
    /// failure, and from a worker of an older binary.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub answer: Option<String>,
}

/// The largest final answer a child's outcome carries, in bytes.
pub const RLM_CHILD_ANSWER_MAX_BYTES: usize = 256 * 1024;

/// Run state of a child's task, read from the child's own durable state:
/// its run in flight, the terminal of its last run, and the background
/// jobs it still owns. A child worker answers this as its
/// `get_run_outcome`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(
    tag = "state",
    rename_all = "camelCase",
    rename_all_fields = "camelCase"
)]
pub enum RlmChildRunState {
    /// The child (or one of its descendants) still has work in flight.
    Running,
    /// The child's run ended, but background jobs it started (kernel jobs,
    /// its own children) still run; their settlement wakes it, so the
    /// child is not done.
    Idle { pending_jobs: u32 },
    /// The child's last run ended with an answer and nothing is pending.
    /// Whether the child replied to this parent meanwhile is the child
    /// row's own durable mark ([`super::mark_child_replied`]).
    Answered {
        /// The child's final assistant text, compacted for the roster.
        answer_preview: Option<String>,
    },
    /// The child's run failed.
    Failed {
        failure: ChildFailure,
        error: String,
    },
}

/// Abort a child's in-flight run, or stop the child's agent, once per key.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RlmChildCancelRequest {
    /// `rlm:<taskId>:cancel` or `rlm:<taskId>:stop`.
    pub idempotency_key: String,
    pub session_id: String,
}

/// Tear a child session down with its ledger tombstone, once per key.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RlmChildDeleteRequest {
    /// `rlm:<taskId>:delete`.
    pub idempotency_key: String,
    pub session_id: String,
    pub rlm_child_id: String,
}

/// Live facts about one child the host can see (overlaid on the durable
/// roster by `rlm.list_subagents`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RlmChildListing {
    pub session_id: String,
    /// `waiting` | `writing` | `executing`; `None` when unknown.
    pub activity: Option<RlmChildActivityKind>,
    pub tool_name: Option<String>,
    pub tool_use_count: Option<u64>,
    /// The child's latest accepted `rlm.progress.note`.
    pub progress_note: Option<String>,
    pub last_activity_at: Option<u64>,
}

/// What a running child is doing (`RlmSubagentActivity.kind`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RlmChildActivityKind {
    Waiting,
    Writing,
    Executing,
}

impl RlmChildActivityKind {
    /// The wire string.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Waiting => "waiting",
            Self::Writing => "writing",
            Self::Executing => "executing",
        }
    }
}

/// Create and prompt one resident depth-0 session (`rlm.create_session`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RlmCreateSessionRequest {
    /// `rlm.create_session:<call id>:<n>`: one session per tool call request.
    pub idempotency_key: String,
    pub prompt: String,
    pub name: Option<String>,
    pub model: Option<String>,
    pub thinking: Option<String>,
    pub cwd: Option<String>,
}

/// `rlm.create_session` handle: one resident depth-0 daemon session.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize)]
pub struct RlmCreateSessionHandle {
    pub active_session_id: String,
    pub session_id: String,
    pub name: String,
    pub session_file: String,
    pub model: String,
}

/// What one `rlm.rename` renames (TS `renameAgentFamilySession`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RlmRenameTarget {
    /// The calling session. `selector` is an explicit `session_id` the
    /// parent registry could not resolve: the host renames itself only when
    /// it names this session's routing id, else refuses. `None` when the
    /// caller omitted it or named the durable session id.
    Session { selector: Option<String> },
    /// One direct child, by its durable session id.
    Child { session_id: String },
}

/// Rename the calling session or one direct child (`rlm.rename`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RlmRenameRequest {
    /// The normalized name (spawn-name rules already applied).
    pub name: String,
    pub target: RlmRenameTarget,
}

/// The family-wide inputs of the spawn cap (omp2 `sv_task_max_concurrency`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RlmSpawnCapacity {
    /// `subagentMaxConcurrency`: running or starting subagents the family
    /// may hold at once; `0` is unlimited.
    pub max_concurrency: u32,
    /// Durable session ids of the family's subagents that are running or
    /// starting right now, as the host sees them (the caller unions its
    /// own not-yet-visible children in).
    pub active_session_ids: Vec<String>,
}

/// The supervisor child-session machinery the daemon supplies to a parent
/// session.
///
/// Implementations must make every keyed call idempotent: a repeated key
/// returns the first call's outcome (or an equivalent no-op success) and
/// never creates, prompts, cancels, or deletes twice. `spawn` must create the
/// child under the requested [`RlmChildIdentity`] so a parent restart finds
/// the same session. `wait_settled` is a long poll: it returns `Running`
/// when its budget ends, `Settled` only after a stability re-check (a prompt
/// admitted to an idle worker can read idle once before its turn starts),
/// and `Err` when the child cannot be reached right now (the watch counts
/// these; a child whose worker is gone settles `Failed`). Sessions without a
/// host use [`NoRlmChildren`].
pub trait RlmSubagentHost: Send + Sync {
    /// Create one recursive child session (no prompt).
    fn spawn(&self, request: RlmChildSpawnRequest) -> RlmHostFuture<'_, RlmChildSession>;
    /// Create and prompt a resident depth-0 daemon session.
    fn create_session(
        &self,
        request: RlmCreateSessionRequest,
    ) -> RlmHostFuture<'_, RlmCreateSessionHandle>;
    /// Admit the task prompt into a created child.
    fn prompt(&self, request: RlmChildPromptRequest) -> RlmHostFuture<'_, ()>;
    /// Long-poll a child for its run to settle.
    fn wait_settled(&self, request: RlmChildWaitRequest) -> RlmHostFuture<'_, RlmChildObservation>;
    /// Abort a child's in-flight run.
    fn cancel(&self, request: RlmChildCancelRequest) -> RlmHostFuture<'_, ()>;
    /// Stop a child's agent (the `rlm` kill path): its worker ends and the
    /// session stays (a later prompt wakes it). A child no worker hosts is
    /// already stopped.
    fn stop(&self, request: RlmChildCancelRequest) -> RlmHostFuture<'_, ()>;
    /// Delete a child session.
    fn delete(&self, request: RlmChildDeleteRequest) -> RlmHostFuture<'_, ()>;
    /// Live facts about this parent's children: one listing per child the
    /// host spawned in this process. `rlm.list_subagents` addresses a
    /// spawned child without a listing (spawned by an earlier process of
    /// the session) by its durable session id instead of its recorded
    /// routing id.
    fn list(&self) -> RlmHostFuture<'_, Vec<RlmChildListing>>;
    /// Rename this session or one direct child. The host owns name
    /// reservation across the agent family; a parent-directed rename marks
    /// the child's transcript notice with the parent.
    fn rename(&self, request: RlmRenameRequest) -> RlmHostFuture<'_, ()>;
    /// The spawn cap's bound and the family's active subagents, read
    /// before a spawn admits.
    fn spawn_capacity(&self) -> RlmHostFuture<'_, RlmSpawnCapacity>;
    /// Stop an isolated child (its session stays), then take its
    /// workspace changes back into the parent's workspace (idempotent: a
    /// repeat returns the first hand-back's record and stops nothing).
    /// `None`: the child works in the shared workspace.
    fn hand_back(&self, request: RlmChildHandbackRequest) -> RlmHostFuture<'_, Option<Handback>>;
}

/// Host behavior for sessions with no child runtime: spawns and creates fail
/// explicitly, the roster overlay is empty. Child primitives fail because no
/// child can exist without a spawn.
pub struct NoRlmChildren;

const NO_CHILD_RUNTIME: &str = "this session has no RLM child runtime";

impl RlmSubagentHost for NoRlmChildren {
    fn spawn(&self, _request: RlmChildSpawnRequest) -> RlmHostFuture<'_, RlmChildSession> {
        Box::pin(async {
            anyhow::bail!(
                "rlm.spawn requires a daemon-backed session: this session has no RLM child runtime"
            );
        })
    }

    fn create_session(
        &self,
        _request: RlmCreateSessionRequest,
    ) -> RlmHostFuture<'_, RlmCreateSessionHandle> {
        Box::pin(async {
            anyhow::bail!("rlm.create_session requires a daemon-backed depth-0 session");
        })
    }

    fn prompt(&self, _request: RlmChildPromptRequest) -> RlmHostFuture<'_, ()> {
        Box::pin(async { anyhow::bail!("{NO_CHILD_RUNTIME}") })
    }

    fn wait_settled(
        &self,
        _request: RlmChildWaitRequest,
    ) -> RlmHostFuture<'_, RlmChildObservation> {
        Box::pin(async { anyhow::bail!("{NO_CHILD_RUNTIME}") })
    }

    fn cancel(&self, _request: RlmChildCancelRequest) -> RlmHostFuture<'_, ()> {
        Box::pin(async { anyhow::bail!("{NO_CHILD_RUNTIME}") })
    }

    fn stop(&self, _request: RlmChildCancelRequest) -> RlmHostFuture<'_, ()> {
        Box::pin(async { anyhow::bail!("{NO_CHILD_RUNTIME}") })
    }

    fn delete(&self, _request: RlmChildDeleteRequest) -> RlmHostFuture<'_, ()> {
        Box::pin(async { anyhow::bail!("{NO_CHILD_RUNTIME}") })
    }

    fn list(&self) -> RlmHostFuture<'_, Vec<RlmChildListing>> {
        Box::pin(async { Ok(Vec::new()) })
    }

    fn rename(&self, _request: RlmRenameRequest) -> RlmHostFuture<'_, ()> {
        Box::pin(async {
            anyhow::bail!(
                "rlm.rename requires a daemon-backed session: this session has no RLM child runtime"
            )
        })
    }

    fn spawn_capacity(&self) -> RlmHostFuture<'_, RlmSpawnCapacity> {
        Box::pin(async { anyhow::bail!("{NO_CHILD_RUNTIME}") })
    }

    fn hand_back(&self, _request: RlmChildHandbackRequest) -> RlmHostFuture<'_, Option<Handback>> {
        Box::pin(async { Ok(None) })
    }
}
