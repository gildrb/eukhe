//! Shared types of the eukhe durable host: what a session opens with
//! ([`SessionConfig`]) and the services its extensions share ([`HostDeps`]).

use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::{Arc, Mutex, OnceLock, PoisonError, Weak};

use eukhe_durable::harness::types::{Clock, ModelRef, ToolExecutionApi};
use eukhe_durable::harness::{Conversation, Harness};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_pi_ai::models::Models;
use eukhe_types::pi_ai::ModelThinkingLevel;
use futures::future::BoxFuture;
use serde_json::Value;

use super::children::RlmSubagentHost;
use super::settings::EukheSettings;
use crate::kernel::{HostRequestHandlers, KernelPythonSkill};
use crate::memory::{Memory, MemoryRole};
use crate::resources::LoadedResources;
use crate::session_engine::runtime_wiring::KernelCronWiring;

/// The session that spawned a child session.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParentLink {
    /// The parent session's id.
    pub session_id: String,
    /// The parent's `eukhe.rlm.child` durable task that owns this session,
    /// when a durable parent spawned it.
    pub task_id: Option<String>,
    /// Human-readable parent name for the child prompt doctrine.
    pub agent_name: Option<String>,
    /// The parent's in-flight model request the spawn anchored to (TS
    /// `spawnedByRequestId`): the child's semantic-edge ledger registers
    /// with it.
    pub spawned_by_request_id: Option<String>,
}

/// Where a session sits in the RLM tree.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SessionRole {
    /// 0 for top-level sessions.
    pub rlm_depth: u32,
    /// Deepest depth a descendant may reach.
    pub rlm_max_depth: u32,
    /// The spawning session; `None` for top-level sessions.
    pub parent: Option<ParentLink>,
}

impl SessionRole {
    /// Whether this is a top-level session.
    #[must_use]
    pub fn is_root(&self) -> bool {
        self.rlm_depth == 0
    }

    /// The chat-memory side of this session: a root logs and renders the
    /// settled view, a subagent renders once and logs nothing.
    #[must_use]
    pub fn memory_role(&self) -> MemoryRole {
        if self.is_root() {
            MemoryRole::Root
        } else {
            MemoryRole::Subagent
        }
    }
}

/// Where a session's durable records live.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SessionStorage {
    /// Durable JSONL storage in `dir` (`<sessions_dir>/<session-id>/`).
    /// A legacy `<sessions_dir>/<session-id>.jsonl` next to a missing `dir`
    /// is imported before the first open.
    Jsonl {
        dir: PathBuf,
        /// Flush sidecars before each main-log marker (eukhe syncs every row).
        fsync: bool,
    },
    /// Process memory only (no-session mode, tests).
    Memory,
}

/// Inputs of the system prompt that are not derived from the conversation.
#[derive(Clone, Debug, Default)]
pub struct PromptConfig {
    /// `--system-prompt`: replaces the layered static prefix (overrides the
    /// discovered `SYSTEM.md`).
    pub custom_system_prompt: Option<String>,
    /// `--append-system-prompt`: appended after every other section.
    pub append_system_prompt: Option<String>,
    /// Additional guideline bullets.
    pub guidelines: Vec<String>,
    /// Enabled generic MCP servers (merged with the settings' persistent ones).
    pub generic_mcp_servers: Vec<String>,
    /// `Some(false)` disables subagent spawning.
    pub allow_recursion: Option<bool>,
    /// Extra skill paths.
    pub additional_skill_paths: Vec<String>,
    /// Extra prompt-template paths.
    pub additional_prompt_paths: Vec<String>,
    /// Force-exclude patterns for built-in skills.
    pub extra_builtin_skill_overrides: Vec<String>,
    /// Conversation-log path shown in the prompt when the session has no chat
    /// memory; defaults to the durable storage directory.
    pub conversation_log_path: Option<PathBuf>,
}

/// What `OptChat` reports about a turn waiting on the root-turn lease.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TurnWait {
    /// The turn waits for another session's root turn to finish.
    Waiting,
    /// The wait ended.
    Cleared,
}

/// A requested model as the CLI takes it: `--provider` (optional) and
/// `--model` (an id, `provider/id`, a pattern, optionally `:level`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModelRequest {
    pub provider: Option<String>,
    pub pattern: String,
}

impl From<ModelRef> for ModelRequest {
    fn from(model: ModelRef) -> Self {
        Self {
            provider: Some(model.provider),
            pattern: model.model_id,
        }
    }
}

/// Receives [`TurnWait`] changes synchronously (the daemon shows them).
pub type TurnWaitSink = Arc<dyn Fn(TurnWait) + Send + Sync>;

/// Receives every text delta a compaction summary streams while it
/// generates (the daemon's live `compaction_summary_delta` seam; the old
/// engine's `set_compaction_summary_sink`). Fire-and-forget: emissions
/// never gate the compaction.
pub type SummaryDeltaSink = Arc<dyn Fn(&str) + Send + Sync>;

/// Receives an agent message the kernel reports after its `ipython` cell
/// settled (TS `onLateSentAgentMessage`), with the id of the tool call that
/// ran the cell. The daemon worker surfaces it as the
/// `ipython_sent_agent_message` session event.
pub type LateAgentMessageSink =
    Arc<dyn Fn(&str, crate::kernel::shared::KernelSentAgentMessage) + Send + Sync>;

/// What an eukhe session opens with.
#[derive(Clone)]
pub struct SessionConfig {
    /// `~/.eukhe` (or `$EUKHE_CODING_AGENT_DIR`).
    pub agent_dir: PathBuf,
    /// The session's working directory.
    pub cwd: PathBuf,
    /// `UUIDv7` session id.
    pub session_id: String,
    pub storage: SessionStorage,
    pub role: SessionRole,
    /// Model of a new root conversation; `None` resolves the settings default.
    pub model: Option<ModelRequest>,
    /// Thinking level of a new root conversation; `None` resolves the
    /// settings default.
    pub thinking: Option<ModelThinkingLevel>,
    /// Chat memory (`OptChat`); `None` keeps a classic continuing conversation.
    pub memory: Option<Memory>,
    /// Daemon child-session host backing `rlm.*`.
    pub children: Option<Arc<dyn RlmSubagentHost>>,
    pub prompt: PromptConfig,
    /// Model collection; `None` builds it from eukhe auth and `models.json`.
    pub models: Option<Models>,
    /// Shared MCP manager (the daemon worker's); `None` builds one.
    pub mcp: Option<Arc<Mutex<crate::mcp::McpManager>>>,
    /// Harness clock (ms since the epoch); `None` uses the system clock.
    pub now: Option<Clock>,
    /// Turn-wait notifications (`OptChat` root-turn lease).
    pub turn_wait: Option<TurnWaitSink>,
    /// Live compaction-summary deltas (the daemon's TUI block); `None`
    /// keeps the one-shot completion.
    pub summary_delta: Option<SummaryDeltaSink>,
    /// The embedding's kernel cron wiring (the daemon worker's store).
    pub cron: Option<KernelCronWiring>,
    /// The embedding's extra kernel host handlers (daemon message/observe
    /// bridges); handlers registered in [`HostRequestRegistry`] win on
    /// collisions.
    pub extra_host_handlers: Option<HostRequestHandlers>,
    /// Late kernel agent messages (the daemon's session event); `None`
    /// drops them.
    pub late_agent_message: Option<LateAgentMessageSink>,
}

impl SessionConfig {
    /// A top-level session with defaults for every optional input.
    #[must_use]
    pub fn new(
        agent_dir: impl Into<PathBuf>,
        cwd: impl Into<PathBuf>,
        session_id: impl Into<String>,
        storage: SessionStorage,
    ) -> Self {
        Self {
            agent_dir: agent_dir.into(),
            cwd: cwd.into(),
            session_id: session_id.into(),
            storage,
            role: SessionRole::default(),
            model: None,
            thinking: None,
            memory: None,
            summary_delta: None,
            children: None,
            prompt: PromptConfig::default(),
            models: None,
            mcp: None,
            now: None,
            turn_wait: None,
            cron: None,
            extra_host_handlers: None,
            late_agent_message: None,
        }
    }
}

/// The open Harness and its root conversation, set right after
/// `Harness::open` and cleared when the session closes (the cell must not
/// keep a closed Harness alive: extensions hold [`HostDeps`]).
#[derive(Clone, Default)]
pub struct HarnessCell {
    inner: Arc<Mutex<Option<(Harness, Conversation)>>>,
}

impl HarnessCell {
    /// The open Harness, or `None` before open and after close.
    #[must_use]
    pub fn get(&self) -> Option<Harness> {
        self.lock().as_ref().map(|(harness, _)| harness.clone())
    }

    /// The root conversation, or `None` before open and after close.
    #[must_use]
    pub fn root(&self) -> Option<Conversation> {
        self.lock().as_ref().map(|(_, root)| root.clone())
    }

    /// The open Harness.
    ///
    /// # Errors
    ///
    /// `Harness is closed` before open and after close.
    pub fn require(&self) -> SessionResult<Harness> {
        self.get()
            .ok_or_else(|| SessionError::error("Harness is closed"))
    }

    pub(crate) fn set(&self, harness: Harness, root: Conversation) {
        *self.lock() = Some((harness, root));
    }

    pub(crate) fn clear(&self) {
        self.lock().take();
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, Option<(Harness, Conversation)>> {
        self.inner.lock().unwrap_or_else(PoisonError::into_inner)
    }
}

/// One kernel host request, with the durable tool call executing the cell
/// that sent it.
#[derive(Clone)]
pub struct HostCall {
    /// The request payload (`cellSourceCode` merged in when known).
    pub data: Value,
    /// Source of the cell that sent the request, when attributable.
    pub cell_source_code: Option<String>,
    /// The `ipython` tool call running the cell; `None` outside a tool call.
    pub call: Option<Arc<dyn ToolExecutionApi>>,
}

/// Handles one kernel host request type; the value reaches the Python caller.
pub type HostCallHandler =
    Arc<dyn Fn(HostCall) -> BoxFuture<'static, anyhow::Result<Value>> + Send + Sync>;

/// Kernel host-request handlers by request type (`rlm.run`, `goal.get`,
/// ...). Extensions register at construction; the kernel dispatch looks a
/// handler up per request. A later registration of a type replaces the
/// earlier one.
#[derive(Clone, Default)]
pub struct HostRequestRegistry {
    handlers: Arc<Mutex<HashMap<String, HostCallHandler>>>,
}

impl HostRequestRegistry {
    pub fn register(&self, request_type: impl Into<String>, handler: HostCallHandler) {
        self.lock().insert(request_type.into(), handler);
    }

    #[must_use]
    pub fn get(&self, request_type: &str) -> Option<HostCallHandler> {
        self.lock().get(request_type).cloned()
    }

    /// Registered request types, sorted.
    #[must_use]
    pub fn request_types(&self) -> Vec<String> {
        let mut types: Vec<String> = self.lock().keys().cloned().collect();
        types.sort();
        types
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, HashMap<String, HostCallHandler>> {
        self.handlers.lock().unwrap_or_else(PoisonError::into_inner)
    }
}

/// The open session handed to services started at open.
#[derive(Clone)]
pub struct OpenedSession {
    pub harness: Harness,
    pub root: Conversation,
    pub deps: Arc<HostDeps>,
}

/// Stops a service; awaited by `EukheSession::close` before the Harness
/// closes, in reverse start order.
pub type ServiceStop = Box<dyn FnOnce() -> BoxFuture<'static, ()> + Send>;

/// Starts a service (e.g. the `OptChat` post-commit logger) once the Harness
/// and root conversation are open, before scheduling resumes. `None` when
/// the service has nothing to stop.
pub type ServiceStart =
    Box<dyn FnOnce(OpenedSession) -> BoxFuture<'static, SessionResult<Option<ServiceStop>>> + Send>;

/// Services shared by the eukhe extensions of one session.
pub struct HostDeps {
    pub agent_dir: PathBuf,
    pub cwd: PathBuf,
    pub session_id: String,
    /// The durable storage directory; `None` for memory storage.
    pub storage_dir: Option<PathBuf>,
    pub role: SessionRole,
    /// eukhe settings, re-read when the settings files change.
    pub settings: Arc<EukheSettings>,
    pub models: Models,
    pub memory: Option<Memory>,
    pub children: Option<Arc<dyn RlmSubagentHost>>,
    pub prompt: PromptConfig,
    /// Live compaction-summary deltas (the daemon's TUI block).
    pub summary_delta: Option<SummaryDeltaSink>,
    /// Resources loaded at open (skills, context files, `SYSTEM.md`, prompt
    /// templates).
    pub resources: Arc<LoadedResources>,
    /// Enabled generic MCP servers: the configured ones plus the persistent
    /// servers from settings, in that order, deduplicated.
    pub generic_mcp_servers: Vec<String>,
    pub mcp: Arc<Mutex<crate::mcp::McpManager>>,
    /// Python skills the project trust admits into the kernel.
    pub python_skills: Vec<KernelPythonSkill>,
    pub turn_wait: Option<TurnWaitSink>,
    pub cron: Option<KernelCronWiring>,
    pub extra_host_handlers: Option<HostRequestHandlers>,
    pub late_agent_message: Option<LateAgentMessageSink>,
    pub harness: HarnessCell,
    pub host_requests: HostRequestRegistry,
    services: Mutex<Vec<ServiceStart>>,
    /// The provider runtime (failover, quota park, image routing, request
    /// timing), set when the session's own model collection is wrapped at
    /// open; `None` for sessions that share a collection (faux scripts).
    pub provider_runtime: OnceLock<Arc<super::models::provider::ProviderRuntime>>,
    /// The session's semantic-edge recorder (the ACP request-id ledger):
    /// mints the id every model request carries on the wire, and anchors
    /// child spawns and returns. Always built by `open_session` (a memory
    /// storage keeps it in memory-only mode).
    pub semantic_edges: Arc<super::observe::semantic_edges::SemanticEdgeRecorder>,
    /// The `eukhe.rlm` kernel pool, set when the extension installs (the
    /// daemon's out-of-band kernel lanes, [`super::rlm::kernel_bash_activity`]).
    pub(crate) rlm_kernels: OnceLock<Weak<super::rlm::KernelPool>>,
}

/// The services `open_session` resolves before building [`HostDeps`].
pub(crate) struct ResolvedServices {
    pub storage_dir: Option<PathBuf>,
    pub settings: Arc<EukheSettings>,
    pub models: Models,
    pub resources: Arc<LoadedResources>,
    pub generic_mcp_servers: Vec<String>,
    pub mcp: Arc<Mutex<crate::mcp::McpManager>>,
    pub python_skills: Vec<KernelPythonSkill>,
    pub semantic_edges: Arc<super::observe::semantic_edges::SemanticEdgeRecorder>,
}

impl HostDeps {
    pub(crate) fn new(config: &SessionConfig, services: ResolvedServices) -> Self {
        Self {
            agent_dir: config.agent_dir.clone(),
            cwd: config.cwd.clone(),
            session_id: config.session_id.clone(),
            storage_dir: services.storage_dir,
            role: config.role.clone(),
            settings: services.settings,
            summary_delta: config.summary_delta.clone(),
            models: services.models,
            memory: config.memory.clone(),
            children: config.children.clone(),
            prompt: config.prompt.clone(),
            resources: services.resources,
            generic_mcp_servers: services.generic_mcp_servers,
            mcp: services.mcp,
            python_skills: services.python_skills,
            turn_wait: config.turn_wait.clone(),
            cron: config.cron.clone(),
            extra_host_handlers: config.extra_host_handlers.clone(),
            late_agent_message: config.late_agent_message.clone(),
            harness: HarnessCell::default(),
            host_requests: HostRequestRegistry::default(),
            services: Mutex::new(Vec::new()),
            provider_runtime: std::sync::OnceLock::new(),
            rlm_kernels: OnceLock::new(),
            semantic_edges: services.semantic_edges,
        }
    }

    /// Start `start` when the session opens (extensions call this at
    /// construction).
    pub fn add_service(&self, start: ServiceStart) {
        self.services
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(start);
    }

    pub(crate) fn take_services(&self) -> Vec<ServiceStart> {
        std::mem::take(&mut *self.services.lock().unwrap_or_else(PoisonError::into_inner))
    }
}
