//! Supervisor-backed RLM child sessions: the daemon's implementation of the
//! eukhe-core durable `eukhe_core::durable::children::RlmSubagentHost`
//! seam (`durable_host`). The parent's durable child task drives keyed
//! primitives that create real daemon sessions through the supervisor link
//! (one supervised worker process per child), prompt them, wait for their
//! runs to settle, and cancel, delete, or rename them.
//!
//! Mechanism note: the TS daemon hosts children in-process
//! (`createRlmSubagentRuntime`); this redesign gives every child its own
//! supervised worker process, created through the supervisor like any other
//! session.

use serde_json::Map;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Duration;

use anyhow::{anyhow, Context, Result};
use eukhe_types::daemon::{DaemonCommand, DaemonSessionLifecycle, PromptInput};
use serde_json::{json, Value};

use crate::rlm_child_model::{
    assert_thinking_supported, compact_rlm_text, resolve_child_model_from_settings,
    UnpinnedChildModel,
};
use crate::supervisor_link::SupervisorLink;
use crate::util::now_ms;

/// Depth bound without an explicit override (TS `resolveRlmMaxDepth` default).
pub const DEFAULT_RLM_MAX_DEPTH: u32 = 2;

/// The depth bound a new session starts from: the global `rlmMaxDepth`
/// setting (`/rlm-max-depth N --global`), else [`DEFAULT_RLM_MAX_DEPTH`].
#[must_use]
pub fn configured_rlm_max_depth(settings: &eukhe_core::settings::SettingsManager) -> u32 {
    settings
        .get_rlm_max_depth()
        .map_or(DEFAULT_RLM_MAX_DEPTH, |depth| {
            u32::try_from(depth).unwrap_or(u32::MAX)
        })
}

/// The close reason a parent hands its resident children (TS
/// `closeSessionOnce`'s reason arms, cascaded through
/// `closeChildSessions(parentState, reason)`):
///
/// - `Killed` — the child closes as killed: its scheduled jobs cancel and
///   its session file archives (TS `cancelScheduledJobsForSession`).
/// - `Shutdown` — the child keeps its resume entry: the jobs survive the
///   close (TS `closeKeepsResumeEntry("shutdown")`), so a later scheduled
///   wake can still fire them.
/// - `Replaced` — the replacement teardown keeps the child's plain cron
///   jobs but cancels its RLM heartbeats (TS
///   `cancelSubagentRlmHeartbeats`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChildCloseReason {
    Killed,
    Shutdown,
    Replaced,
}

impl ChildCloseReason {
    /// The `rlmCloseReason` rest marker of the kill command the parent
    /// routes to the child worker (the plain client kill carries none and
    /// stays `Killed`).
    fn wire_marker(self) -> Option<&'static str> {
        match self {
            Self::Killed => None,
            Self::Shutdown => Some("shutdown"),
            Self::Replaced => Some("replaced"),
        }
    }
}

/// Grace between the first idle observation of a child and the settle
/// decision (see the stability re-check in `watch_child_settle`).
const WATCH_SETTLE_GRACE_MS: u64 = 250;
/// Deadline for one child-session create over the link (TS uses 120s).
const CREATE_TIMEOUT_MS: u64 = 120_000;
const PROMPT_TIMEOUT_MS: u64 = 30_000;
const STATE_TIMEOUT_MS: u64 = 30_000;
const KILL_TIMEOUT_MS: u64 = 30_000;
/// Budget for one session rename over the supervisor route (TS uses 30s).
const RENAME_TIMEOUT_MS: u64 = 30_000;
/// Grace over a collect budget passed to the worker `wait_for_idle`.
const IDLE_WAIT_GRACE_MS: u64 = 5_000;
/// Prompts longer than this are not mirrored into create runtime metadata.
const RUNTIME_METADATA_PROMPT_MAX: usize = 4096;

/// The parent identity children are spawned from: recursion bounds, the
/// inherited model selector and thinking level, and the parent session's
/// persistence identity.
#[derive(Debug, Clone, Default)]
pub struct ParentIdentity {
    pub rlm_depth: u32,
    pub rlm_max_depth: u32,
    /// Parent model selector (`provider/id`); children inherit it.
    pub model: Option<String>,
    /// Parent working directory; children inherit it.
    pub cwd: Option<String>,
    /// Persisted parent session id (keys the session-artifacts tree).
    pub session_id: Option<String>,
    /// Parent session file path.
    pub session_file: Option<String>,
    /// Default thinking level children inherit.
    pub thinking: Option<String>,
    /// Verification seam: create children with a scripted engine file.
    pub child_script: Option<String>,
}

impl ParentIdentity {
    /// Identity with the default depth bound (TS `resolveRlmMaxDepth`).
    #[must_use]
    pub fn with_default_depth() -> Self {
        Self {
            rlm_max_depth: DEFAULT_RLM_MAX_DEPTH,
            ..Default::default()
        }
    }
}

/// One child's family-addressing identity: the same facts the RLM roster
/// row carries, snapshotted without a worker refresh. The agent-message
/// family view (and only it) reads children through this shape.
#[derive(Debug, Clone)]
pub struct RlmChildIdentity {
    pub rlm_child_id: String,
    pub active_session_id: String,
    pub session_id: Option<String>,
    pub session_name: String,
}

/// The selector that reaches a child whether or not its worker is
/// resident: the persisted session id (the session-file stem the
/// supervisor's ledger wake resolves), else the RLM child id. The
/// spawn-time live id stops resolving once the worker passivates.
pub(crate) fn durable_child_selector(session_id: Option<&str>, rlm_child_id: &str) -> String {
    session_id.unwrap_or(rlm_child_id).to_string()
}

/// RLM children as supervisor-managed daemon sessions. A cheap shared handle:
/// the daemon hands the same children registry to every kernel handler call.
pub struct SupervisorChildSessions {
    inner: Arc<SupervisorChildSessionsInner>,
}

/// The child-delete completion hook (the worker wires its context-tree
/// cache invalidation): called once per completed delete with the deleted
/// child's id.
pub type DeleteNotifier = std::sync::Arc<dyn Fn(&str) + Send + Sync>;

/// Reads the parent's current model selector (`provider/id`) at spawn time:
/// the worker answers from its main conversation's agent, so a child spawned
/// without a model inherits the model the parent runs on now.
pub type ParentModelSource =
    std::sync::Arc<dyn Fn() -> futures::future::BoxFuture<'static, Option<String>> + Send + Sync>;

/// Reads the parent session's live name at prompt time (the `sessionName`
/// of the spawn kickoff's `from` endpoint): the worker answers from its
/// session core, so a parent renamed since `create` signs with its new name.
pub type ParentNameSource = std::sync::Arc<dyn Fn() -> Option<String> + Send + Sync>;

/// Reads the parent session's durable children roster (the durable
/// worker's `eukhe.rlm.children` document, the one `rlm.list_subagents`
/// reads) as family identities: the durable path records its children
/// there, never in the registry, and a restarted parent reads them back.
pub type DurableChildrenSource = std::sync::Arc<
    dyn Fn() -> futures::future::BoxFuture<'static, Result<Vec<RlmChildIdentity>>> + Send + Sync,
>;

struct SupervisorChildSessionsInner {
    link: Arc<SupervisorLink>,
    agent_dir: PathBuf,
    parent_active_session_id: String,
    // The identity lock is only ever a data swap (never held across an
    // await), so a std mutex keeps the setter callable from sync engine
    // paths (the create command) without a runtime `block_on`.
    identity: std::sync::Mutex<ParentIdentity>,
    /// The delete notification hook (wired by the worker with its
    /// context-tree cache handle): a deleted child must leave the cached
    /// `/context` children immediately, not ride out the next background
    /// refresh.
    delete_notifier: std::sync::Mutex<Option<DeleteNotifier>>,
    /// Keyed calls of the durable child host (`durable_host`) this process
    /// served, and the children it spawned.
    durable_calls: std::sync::Mutex<durable_host::DurableCalls>,
    /// The parent's live model reader (the durable worker's main
    /// conversation); `None` keeps the identity's model.
    parent_model: std::sync::Mutex<Option<ParentModelSource>>,
    /// The parent's live session-name reader (the durable worker's core);
    /// `None` leaves the kickoff's `from` endpoint unnamed.
    parent_name: std::sync::Mutex<Option<ParentNameSource>>,
    /// The parent's durable children reader (the durable worker's main
    /// conversation); `None` leaves the family view empty.
    durable_children: std::sync::Mutex<Option<DurableChildrenSource>>,
    /// The worker's supervisor token (the family roster read behind the
    /// spawn cap authenticates with it); `None` until the worker wires it.
    worker_token: std::sync::Mutex<Option<String>>,
}

impl Clone for SupervisorChildSessions {
    fn clone(&self) -> Self {
        Self {
            inner: Arc::clone(&self.inner),
        }
    }
}

impl SupervisorChildSessions {
    /// Children registry bound to one parent session worker.
    #[must_use]
    pub fn new(
        link: Arc<SupervisorLink>,
        agent_dir: PathBuf,
        parent_active_session_id: String,
    ) -> Self {
        Self {
            inner: Arc::new(SupervisorChildSessionsInner {
                link,
                agent_dir,
                parent_active_session_id,
                identity: std::sync::Mutex::new(ParentIdentity::with_default_depth()),
                durable_calls: std::sync::Mutex::new(durable_host::DurableCalls::default()),
                parent_model: std::sync::Mutex::new(None),
                parent_name: std::sync::Mutex::new(None),
                delete_notifier: std::sync::Mutex::new(None),
                durable_children: std::sync::Mutex::new(None),
                worker_token: std::sync::Mutex::new(None),
            }),
        }
    }

    /// Wire the delete notification hook (the worker's context-tree cache
    /// invalidation): called once per completed child delete with the
    /// deleted child's id.
    ///
    /// # Panics
    ///
    /// Panics when the delete-notifier mutex is poisoned (a holder
    /// panicked while holding the lock).
    pub fn set_delete_notifier(&self, notifier: DeleteNotifier) {
        *self
            .inner
            .delete_notifier
            .lock()
            .expect("delete notifier lock") = Some(notifier);
    }

    /// Replace the parent identity (the worker session sets it once its own
    /// session exists).
    ///
    /// # Panics
    ///
    /// Panics when the identity mutex is poisoned (a holder panicked
    /// while holding the lock).
    pub fn set_identity(&self, identity: ParentIdentity) {
        *self.inner.identity.lock().expect("identity lock") = identity;
    }

    /// Wire the parent's live model reader: each durable spawn and
    /// `create_session` refreshes the inherited model from it first.
    pub fn set_parent_model_source(&self, source: ParentModelSource) {
        *self
            .inner
            .parent_model
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner) = Some(source);
    }

    /// Wire the parent's live session-name reader: each durable kickoff
    /// signs its `from` endpoint with the name it answers.
    pub fn set_parent_name_source(&self, source: ParentNameSource) {
        *self
            .inner
            .parent_name
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner) = Some(source);
    }

    /// Wire the parent's durable children reader: the family view joins
    /// the children the durable path recorded (a restarted parent's
    /// passivated children included) beside the registry's.
    pub fn set_durable_children_source(&self, source: DurableChildrenSource) {
        *self
            .inner
            .durable_children
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner) = Some(source);
    }

    /// Wire the worker's supervisor token: the spawn cap reads the family
    /// roster (`list_agent_peers`) with it.
    pub fn set_worker_token(&self, token: String) {
        *self
            .inner
            .worker_token
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner) = Some(token);
    }

    /// The inherited RLM depth bound (TS `getRlmMaxDepthStatus().maxDepth`
    /// before any chat override).
    ///
    /// # Panics
    ///
    /// Panics when the identity mutex is poisoned (a holder panicked
    /// while holding the lock).
    #[must_use]
    pub fn rlm_max_depth(&self) -> u32 {
        self.inner
            .identity
            .lock()
            .expect("identity lock")
            .rlm_max_depth
    }

    /// The `agent_message` / `agent_observe` family's children: the durable
    /// children roster (the same document `rlm.list_subagents` reads).
    ///
    /// # Errors
    ///
    /// The durable children roster cannot be read.
    pub async fn family_child_identities(&self) -> Result<Vec<RlmChildIdentity>> {
        let source = self
            .inner
            .durable_children
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .clone();
        match source {
            Some(source) => source().await,
            None => Ok(Vec::new()),
        }
    }

    /// Set only the inherited model selector (the engine resolves its model
    /// when it builds the session, after the create command arrived).
    ///
    /// # Panics
    ///
    /// Panics when the identity mutex is poisoned (a holder panicked
    /// while holding the lock).
    pub fn set_model(&self, model: String) {
        self.inner.identity.lock().expect("identity lock").model = Some(model);
    }

    /// Set the session's RLM depth bound (TS `setRlmMaxDepth`): the
    /// registry is the bound every spawn checks, so the override is the
    /// live limit children respect immediately.
    ///
    /// # Panics
    ///
    /// Panics when the identity mutex is poisoned (a holder panicked
    /// while holding the lock).
    pub fn set_rlm_max_depth(&self, max_depth: u32) {
        self.inner
            .identity
            .lock()
            .expect("identity lock")
            .rlm_max_depth = max_depth;
    }
}

impl SupervisorChildSessionsInner {
    /// Send one daemon command over the supervisor link and return its
    /// response data. The link owns timeouts/reconnects; this only maps the
    /// command to its wire value.
    async fn command(&self, command: &DaemonCommand, timeout_ms: u64) -> Result<Value> {
        let wire = serde_json::to_value(command).context("serialize supervisor link command")?;
        self.link
            .request_success(wire, Duration::from_millis(timeout_ms))
            .await
    }

    /// The per-child session directory under the parent's artifacts tree
    /// (TS `_createChildRlmSessionDir`); the child session persists inside it.
    fn child_session_dir(&self, child_id: &str, identity: &ParentIdentity) -> Result<PathBuf> {
        let base = self.child_session_path(child_id, identity);
        std::fs::create_dir_all(&base)
            .with_context(|| format!("create RLM child session dir {}", base.display()))?;
        Ok(base)
    }

    /// [`Self::child_session_dir`]'s path, without creating it.
    fn child_session_path(&self, child_id: &str, identity: &ParentIdentity) -> PathBuf {
        match &identity.session_id {
            Some(session_id) => self
                .agent_dir
                .join("session-artifacts")
                .join(session_id)
                .join(child_id),
            // No persistent parent artifacts dir: an ephemeral temp dir, the
            // TS `_createEphemeralRlmSessionDir` fallback.
            None => std::env::temp_dir().join(format!("eukhe-rlm-{child_id}")),
        }
    }
}

mod durable_host;
mod lifecycle;

#[cfg(test)]
mod tests {
    use super::*;

    /// Regression: the global `rlmMaxDepth` was saved but never applied;
    /// a new session now starts from it.
    #[test]
    fn new_sessions_start_from_the_global_rlm_max_depth() {
        let dir = tempfile::TempDir::new().unwrap();
        let read = || {
            configured_rlm_max_depth(&eukhe_core::settings::SettingsManager::create(
                dir.path(),
                dir.path(),
            ))
        };
        let unset = read();
        std::fs::write(dir.path().join("settings.json"), r#"{"rlmMaxDepth": 5}"#).unwrap();
        assert_eq!([unset, read()], [DEFAULT_RLM_MAX_DEPTH, 5]);
    }
}
