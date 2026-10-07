//! The child-session host seam: the supervisor operations an
//! `eukhe.rlm.child` task drives (port of `session_engine/rlm_host.rs`'s
//! `RlmSubagentHost`, narrowed to primitives).
//!
//! The old host owned the whole child lifecycle in daemon memory (spawn,
//! settle watching, the terminal notice, the roster). The durable host is a
//! set of idempotent primitives: the lifecycle lives in the parent's durable
//! task, so it survives a parent restart. Every mutating call carries an
//! explicit idempotency key; a rerun after a crash repeats the call with the
//! same key and must observe the first call's effect, never a second one.

use eukhe_types::pi_ai::Usage;
use futures::future::BoxFuture;

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

/// Prompt a created child with its task, once per key.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RlmChildPromptRequest {
    /// `rlm:<taskId>:prompt`.
    pub idempotency_key: String,
    pub session_id: String,
    pub prompt: String,
}

/// Long-poll one child until its run settles or the budget ends.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RlmChildWaitRequest {
    pub session_id: String,
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
}

/// Run state of a child's task.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RlmChildRunState {
    /// The child (or one of its descendants) still has work in flight.
    Running,
    /// The child's run settled and stayed idle across the host's stability
    /// re-check.
    Settled {
        /// The child's final assistant text, compacted for the roster.
        answer_preview: Option<String>,
        /// The child sent an agent message to this parent since its task
        /// was admitted (TS `_parentReplyCount`): no no-reply notice is owed.
        replied_since_task: bool,
    },
    /// The child's run failed.
    Failed { error: String },
}

/// Abort a child's in-flight run, once per key.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RlmChildCancelRequest {
    /// `rlm:<taskId>:cancel`.
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
/// and `Err` when the child cannot be reached right now. Sessions without a
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
    /// Delete a child session.
    fn delete(&self, request: RlmChildDeleteRequest) -> RlmHostFuture<'_, ()>;
    /// Live facts about this parent's children.
    fn list(&self) -> RlmHostFuture<'_, Vec<RlmChildListing>>;
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

    fn delete(&self, _request: RlmChildDeleteRequest) -> RlmHostFuture<'_, ()> {
        Box::pin(async { anyhow::bail!("{NO_CHILD_RUNTIME}") })
    }

    fn list(&self) -> RlmHostFuture<'_, Vec<RlmChildListing>> {
        Box::pin(async { Ok(Vec::new()) })
    }
}
