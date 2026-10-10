//! Session worker runtime: one process, one session.
//!
//! Port of the TS daemon's worker mode (`modes/daemon/daemon-mode.ts` worker
//! branch, `modes/session-worker/*`). The worker hosts one durable eukhe
//! session (`durable_host`): the Harness owns persistence, the input inbox,
//! retries, compaction, tool execution, and crash resume; the worker keeps
//! the supervisor protocol, client connections, attach, event sequencing,
//! the session lease, the revival evidence, and the command handlers.
//! Supervisors connect over a private-framed Unix socket and authenticate
//! with the bootstrap token before any command.

mod config;
pub mod durable_host;
mod env;
mod session_core;

pub(crate) use config::WorkerConfig;
use env::KillCloseReason;
mod input;
pub(crate) use input::{injection_kind, parse_prompt_images, submit_input, InputRequest};
mod lifecycle;
mod passivation;
mod summary;

mod connection;

pub(crate) use connection::{AuthOutcome, ConnectionSink, EventPump, OutboundFrame};

mod create;

pub(crate) use create::CreateParams;
use create::{active_session_id_of, worker_server_capabilities};
pub(crate) use summary::{
    compact_action_label, emit_action_update_locked, emit_event_locked, emit_worker_event_with,
    model_metadata, push_roster_delta, session_snapshot, RosterPushContext,
};

mod commands;
pub(crate) use commands::resubmit_suspended;
pub(crate) use commands::{drain_withdrawn, mutate_withdrawn, set_withdrawn, WithdrawnList};

#[cfg(test)]
mod tests;

pub(crate) use durable_host::{HostedSession, SessionSlot};
pub use env::{
    WORKER_ACTIVE_SESSION_ID_ENV, WORKER_CWD_ENV, WORKER_INSTANCE_ID_ENV,
    WORKER_RECOVERY_JOURNAL_ENV, WORKER_ROLE_ENV, WORKER_SCRIPT_ENV, WORKER_SOCKET_ENV,
    WORKER_SUPERVISOR_LOST_EXIT_MS_ENV, WORKER_SUPERVISOR_SOCKET_ENV,
    WORKER_TELEMETRY_DISABLED_ENV, WORKER_TOKEN_ENV,
};
use serde_json::Map;
pub(crate) use session_core::SessionCore;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use anyhow::{anyhow, Context, Result};
use eukhe_types::platform::transport::{bind_transport, TransportStream};
use serde_json::{json, Value};
use tokio::sync::broadcast;

use crate::framing::{write_frame, write_frame_segments, DEFAULT_PRIVATE_FRAME_LIMITS};
use crate::journal::WorkerRecoveryJournal;
use crate::paths;
use crate::peer::{
    peer_command_allowed, worker_peer_command_allowed, ConnectionRole, PeerGrantStore,
    PEER_COMMAND_NOT_ALLOWED,
};
use crate::protocol::{
    create_daemon_event_meta, create_daemon_replay_info, current_protocol_info,
    default_client_capabilities, normalize_client_capabilities, response_failure, response_success,
    DaemonOutbound, DaemonResponse, DaemonResumeCursor, DaemonSessionClosedReason,
    DAEMON_APP_VERSION, DAEMON_SCHEMA_ID, DAEMON_SCHEMA_REVISION,
};
use crate::registration::RegistrationHandle;

use crate::types::{AgentConnectionState, SessionActionSnapshot};

/// How long the close paths (`shutdown`, `kill`) wait for aborted side
/// question runs to queue their terminal cancelled events before the
/// process exits.
pub(crate) const SIDE_QUESTION_SETTLE_TIMEOUT: Duration = Duration::from_secs(3);

pub struct Worker {
    pub(crate) config: WorkerConfig,
    /// The bind-time filesystem identity of this worker's own socket file:
    /// the exit cleanups pass it as the unlink's expected identity, so a
    /// successor's socket at the same path is never unlinked. `None` until
    /// `serve` binds.
    pub(crate) bound_socket_identity: std::sync::Mutex<Option<crate::socket::SocketIdentity>>,
    /// The bound-listener close handshake (the TS graceful-shutdown
    /// sequence, daemon-mode.ts:8011-8018: `server.close()` is awaited
    /// FIRST, the socket cleanup runs after): an exiting path requests
    /// the close, the accept loop drops the listener it owns, and the
    /// exit proceeds only once the bind is provably released - which is
    /// what makes the exit cleanup's liveness probe sound (a live
    /// listener at the path afterwards can only be a successor's).
    pub(crate) listener_close_requested: tokio::sync::Notify,
    /// The accept loop's confirmation that it dropped the bound
    /// listener; see [`Worker::listener_close_requested`].
    pub(crate) listener_closed: tokio::sync::Notify,
    /// Supervisor self-registration handle; `None` for standalone workers.
    registration: Option<RegistrationHandle>,
    /// Live connections authenticated as the supervisor role (disarms the
    /// supervisor-lost exit monitor).
    pub(crate) supervisor_claims: std::sync::Arc<std::sync::atomic::AtomicUsize>,
    pub(crate) core: Arc<Mutex<SessionCore>>,
    /// The hosted durable session, once `create` opened it.
    pub(crate) session: SessionSlot,
    /// The monotonic roster-delta counter shared with the roster push queue.
    roster_delta_sequence: std::sync::Arc<std::sync::atomic::AtomicU64>,
    /// Connection tokens -> the client ids their `attach` retained.
    pub(crate) session_attachments:
        std::sync::Mutex<std::collections::HashMap<String, Vec<String>>>,
    /// Connection tokens whose attach guard already released.
    pub(crate) released_attach_tokens: std::sync::Mutex<std::collections::HashSet<String>>,
    pub(crate) events: Arc<EventPump>,
    /// The `/model` catalog background-refresh coalescing gate.
    pub(crate) model_catalog_refresh_gate: std::sync::Arc<crate::model_catalog::RefreshGate>,
    /// The revival evidence: the journal records `busy` while a run is
    /// active on the session.
    recovery: Arc<Mutex<Option<WorkerRecoveryJournal>>>,
    /// Live side-question runs (registry, guards, event frames).
    side_questions: crate::side_question::SideQuestionManager,
    /// Single-use peer-transport grants (worker memory only).
    pub(crate) peer_grants: PeerGrantStore,
    /// Compaction commands.
    pub(crate) compaction: crate::compaction::CompactionManager,
    /// Session-tree navigation: `/tree` moves, branch summaries, forks.
    pub(crate) tree_navigation: crate::branch_navigation::TreeNavigation,
    /// The `get_context_tree` children cache.
    pub(crate) context_tree: std::sync::Arc<crate::context_tree_cache::ContextTreeCache>,
    /// Session export: the `/export` HTML and JSONL branches.
    exports: crate::session_export::ExportCommands,
    /// Session-scoped ACP MCP servers.
    acp_mcp: std::sync::Arc<std::sync::Mutex<eukhe_core::mcp::McpManager>>,
    /// The user-bash slot (`execute_bash` / `execute_bash_and_wait` /
    /// `abort_bash`).
    pub(crate) user_bash: std::sync::Arc<crate::user_bash::UserBash>,
    /// The coalescing roster push queue.
    pub(crate) roster_pushes: crate::roster_activity::RosterPushQueue,
    /// Agent-message ingestion state (`agent_messages_*` arms).
    pub(crate) agent_messages: crate::agent_message_ingest::AgentMessageIngest,
    /// Session input-pause leases (`acquire`/`release_session_input_pause`).
    pub(crate) input_pauses: crate::session_input_pause::InputPauseTable,
    /// Session navigation: `new_session` / `switch_session` / `import_jsonl`.
    pub(crate) navigation: crate::session_navigation::SessionNavigation,
    /// Worker-side prompt admissions (`cancel_prompt_admission`).
    pub(crate) prompt_admissions: crate::prompt_admission::WorkerAdmissions,
    /// The scheduling surface (cron/heartbeat store + scheduler).
    pub(crate) scheduled: std::sync::Arc<crate::scheduled_jobs::ScheduledJobs>,
    /// The session's Herdr reporter, (re)bound at `create`.
    pub(crate) herdr: std::sync::Arc<std::sync::Mutex<crate::herdr::HerdrReporter>>,
    /// The reporter epoch (bumped on every (re)bind).
    pub(crate) herdr_generation: std::sync::Arc<std::sync::atomic::AtomicU64>,
    /// Session creation is one serialized critical section: a concurrent
    /// create joins the in-flight one.
    create_gate: tokio::sync::Mutex<()>,
    /// Fires whenever the session parks (a run ends, a session opens
    /// idle): the idle-passivation loop re-arms its window (and the
    /// settled-child kernel release re-checks) on every park.
    pub(crate) park_notify: std::sync::Arc<tokio::sync::Notify>,
    /// Whole-session replacements are one serialized critical section.
    pub(crate) replacement_gate: tokio::sync::Mutex<()>,
    /// Renames are one serialized critical section: the previous-name read,
    /// the name write, and its `session_renamed` notice stay together.
    pub(crate) rename_gate: tokio::sync::Mutex<()>,
    /// The chat memory root sessions share (`<agent-dir>/chat`), opened at
    /// the first root create.
    chat_memory: tokio::sync::OnceCell<eukhe_core::memory::Memory>,
    /// The create-config faux script's models, built at the first open:
    /// every session this worker opens (create, replacements) consumes the
    /// one script in order.
    scripted_models: std::sync::OnceLock<durable_host::ScriptedModels>,
    /// The RLM child host (supervisor-backed), built once on first use.
    pub(crate) rlm_children:
        std::sync::OnceLock<std::sync::Arc<crate::rlm_children::SupervisorChildSessions>>,
    /// This session's own summary as the kernel messaging controllers
    /// read it (the sender identity block and the family edges),
    /// published at every create and rename.
    pub(crate) own_summary: Arc<Mutex<Option<Value>>>,
    /// The daemon model-allowlist refusal telemetry (`model refused`): one
    /// client per worker, deduplicated per (surface, selector).
    pub(crate) model_refusal_telemetry: Arc<crate::model_allowlist::ModelRefusalTelemetry>,
}

/// Whether a delivery's sender is one of THIS session's children, by the
/// sender's recorded durable parent edge: the persisted session id first,
/// then the live active id, then the session-storage alias.
fn sender_is_child_of(sender: &Value, core: &SessionCore) -> bool {
    sender_parent_edge_is(
        sender,
        (!core.session_id.is_empty()).then_some(core.session_id.as_str()),
        &core.active_session_id,
        core.session_dir.as_deref(),
    )
}

/// The edge test behind [`sender_is_child_of`], pure over the recipient's
/// durable identity: the sender block's parent edge (persisted id, live
/// id, or session path) must point back at this session.
fn sender_parent_edge_is(
    sender: &Value,
    own_session_id: Option<&str>,
    own_active_session_id: &str,
    own_session_file: Option<&std::path::Path>,
) -> bool {
    let text = |key: &str| sender.get(key).and_then(Value::as_str);
    if let (Some(parent), Some(own)) = (text("parentSessionId"), own_session_id) {
        if parent == own {
            return true;
        }
    }
    if text("parentActiveSessionId") == Some(own_active_session_id) {
        return true;
    }
    match (text("parentSessionPath"), own_session_file) {
        (Some(parent), Some(own)) => std::path::Path::new(parent) == own,
        _ => false,
    }
}

impl Worker {
    /// Build the worker: the session core, the event pump, and the
    /// feature managers. The session itself opens at `create`.
    pub fn new(config: WorkerConfig, registration: Option<RegistrationHandle>) -> Self {
        let model_refusal_telemetry = Arc::new(crate::model_allowlist::ModelRefusalTelemetry::new(
            config.agent_dir.clone(),
            config.telemetry_disabled == Some(true),
        ));
        let events = Arc::new(EventPump::new());
        let supervisor_claims = std::sync::Arc::new(std::sync::atomic::AtomicUsize::new(0));
        let core = Arc::new(Mutex::new(SessionCore::new(
            config.active_session_id.clone(),
        )));
        let session = SessionSlot::default();
        let recovery = Arc::new(Mutex::new(None));
        let roster_link = std::sync::Arc::new(crate::supervisor_link::SupervisorLink::new(
            std::env::var_os(WORKER_SUPERVISOR_SOCKET_ENV)
                .map(std::path::PathBuf::from)
                .unwrap_or_default(),
        ));
        let worker_token = std::env::var(WORKER_TOKEN_ENV).unwrap_or_default();
        let roster_delta_sequence = std::sync::Arc::new(std::sync::atomic::AtomicU64::new(0));
        let input_pauses = crate::session_input_pause::InputPauseTable::new();
        let herdr_slot =
            std::sync::Arc::new(std::sync::Mutex::new(crate::herdr::HerdrReporter::default()));
        let herdr_generation = std::sync::Arc::new(std::sync::atomic::AtomicU64::new(0));
        let prompt_admissions = crate::prompt_admission::WorkerAdmissions::new();
        let user_bash = std::sync::Arc::new(crate::user_bash::UserBash::new());
        let scheduled = std::sync::Arc::new(crate::scheduled_jobs::ScheduledJobs::new(
            Arc::clone(&core),
            session.clone(),
            std::sync::Arc::clone(&user_bash),
            Arc::clone(&events),
        ));
        let roster_pushes = crate::roster_activity::RosterPushQueue::spawn(RosterPushContext {
            core: Arc::clone(&core),
            session: session.clone(),
            user_bash: std::sync::Arc::clone(&user_bash),
            roster_link: Arc::clone(&roster_link),
            worker_token: worker_token.clone(),
            worker_instance_id: config.worker_instance_id.clone(),
            roster_delta_sequence: std::sync::Arc::clone(&roster_delta_sequence),
        });
        crate::roster_activity::spawn_roster_activity_watch(&events, roster_pushes.clone());
        // The park loop: the settled-child kernel release and the idle
        // passivation re-check on every run end (and the opening park).
        let park_notify = std::sync::Arc::new(tokio::sync::Notify::new());
        tokio::spawn(passivation::passivation_loop(passivation::ParkContext {
            core: Arc::clone(&core),
            session: session.clone(),
            user_bash: std::sync::Arc::clone(&user_bash),
            input_pauses: input_pauses.clone(),
            scheduled: std::sync::Arc::clone(&scheduled),
            link: Arc::clone(&roster_link),
            worker_token,
            agent_dir: config.agent_dir.clone(),
            park_notify: std::sync::Arc::clone(&park_notify),
        }));
        let side_questions = crate::side_question::SideQuestionManager::new(
            session.clone(),
            events.clone(),
            config.active_session_id.clone(),
        );
        let compaction = crate::compaction::CompactionManager::new(
            session.clone(),
            events.clone(),
            Arc::clone(&core),
        );
        let tree_navigation = crate::branch_navigation::TreeNavigation::new(session.clone());
        let exports = crate::session_export::ExportCommands::new(session.clone());
        let agent_dir = config.agent_dir.clone();
        let acp_mcp = eukhe_core::mcp::McpManager::new(eukhe_core::mcp::McpManagerOptions {
            auth_storage: eukhe_core::auth::AuthStorage::create(&agent_dir),
            get_user_servers: Box::new(|| None),
            begin_login: None,
            agent_dir: Some(agent_dir),
            get_catalog_sources: None,
            remote_source: None,
            probe_override: None,
        });
        let navigation =
            crate::session_navigation::SessionNavigation::new(session.clone(), Arc::clone(&core));
        Worker {
            config,
            bound_socket_identity: std::sync::Mutex::new(None),
            listener_close_requested: tokio::sync::Notify::new(),
            listener_closed: tokio::sync::Notify::new(),
            registration,
            supervisor_claims,
            core,
            session,
            roster_delta_sequence,
            session_attachments: std::sync::Mutex::new(std::collections::HashMap::new()),
            released_attach_tokens: std::sync::Mutex::new(std::collections::HashSet::new()),
            events,
            model_catalog_refresh_gate: std::sync::Arc::new(
                crate::model_catalog::RefreshGate::default(),
            ),
            recovery,
            side_questions,
            peer_grants: PeerGrantStore::new(),
            compaction,
            tree_navigation,
            context_tree: std::sync::Arc::new(crate::context_tree_cache::ContextTreeCache::new()),
            exports,
            acp_mcp: std::sync::Arc::new(std::sync::Mutex::new(acp_mcp)),
            user_bash,
            roster_pushes,
            agent_messages: crate::agent_message_ingest::AgentMessageIngest::new(),
            input_pauses,
            navigation,
            prompt_admissions,
            scheduled,
            herdr: herdr_slot,
            herdr_generation,
            create_gate: tokio::sync::Mutex::new(()),
            park_notify,
            replacement_gate: tokio::sync::Mutex::new(()),
            rename_gate: tokio::sync::Mutex::new(()),
            chat_memory: tokio::sync::OnceCell::new(),
            scripted_models: std::sync::OnceLock::new(),
            rlm_children: std::sync::OnceLock::new(),
            own_summary: Arc::new(Mutex::new(None)),
            model_refusal_telemetry,
        }
    }

    /// The hosted session, or the command failure a command answers before
    /// `create` (or while shutting down).
    // DaemonResponse is the wire response struct and is deliberately wide;
    // the error channel carries the whole response.
    #[allow(clippy::result_large_err)]
    pub(crate) fn hosted(&self, command_type: &str) -> Result<Arc<HostedSession>, DaemonResponse> {
        self.require_created(command_type)?;
        self.session.get().ok_or_else(|| {
            response_failure(None, command_type, "Session is still initializing", None)
        })
    }

    /// The bridge sink of this worker: the core, the event pump, and the
    /// run-activity hook (journal busy verdict, roster push, pane reporter).
    pub(crate) fn bridge_sink(&self) -> durable_host::bridge::BridgeSink {
        let core = Arc::clone(&self.core);
        let recovery = Arc::clone(&self.recovery);
        let roster_pushes = self.roster_pushes.clone();
        let herdr = std::sync::Arc::clone(&self.herdr);
        let park_notify = std::sync::Arc::clone(&self.park_notify);
        durable_host::bridge::BridgeSink {
            core: Arc::clone(&self.core),
            events: Arc::clone(&self.events),
            on_run: Arc::new(move |change| {
                use durable_host::bridge::RunChange;
                // A retry keeps the run busy: only the pane hears it (the
                // TS auto-retry hold clears a pending failure hold).
                let error_hold = match change {
                    RunChange::RetryStarted => {
                        herdr
                            .lock()
                            .unwrap_or_else(std::sync::PoisonError::into_inner)
                            .retry_started();
                        return;
                    }
                    RunChange::Started => None,
                    RunChange::Ended { error_hold } => Some(error_hold),
                };
                let busy = error_hold.is_none();
                let more_queued = {
                    let mut core = core
                        .lock()
                        .unwrap_or_else(std::sync::PoisonError::into_inner);
                    if !busy {
                        core.last_activity_ms = crate::util::now_ms();
                    }
                    core.view
                        .as_ref()
                        .is_some_and(|view| !view.inbox.is_empty())
                };
                record_recovery_with(
                    &recovery,
                    &core,
                    busy,
                    if busy { "run_started" } else { "run_ended" },
                );
                let reporter = herdr
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner);
                match error_hold {
                    None => reporter.run_started(),
                    Some(error_hold) => reporter.run_ended(error_hold, more_queued),
                }
                drop(reporter);
                // The park: the idle-passivation window (and the
                // settled-child kernel release) re-arms from here.
                if !busy {
                    park_notify.notify_one();
                }
                roster_pushes.push();
            }),
        }
    }

    /// Show `conversation` on the wire: rebinds the event bridge (the
    /// attach snapshot and live events follow it). Feature handlers call
    /// this after a fork or tree move changed the main conversation.
    ///
    /// # Errors
    ///
    /// The event stream cannot be attached.
    pub(crate) async fn show_conversation(
        &self,
        hosted: &HostedSession,
        conversation: &eukhe_durable::harness::Conversation,
    ) -> eukhe_durable::session::SessionResult<()> {
        hosted.show(conversation, self.bridge_sink()).await
    }

    /// The Herdr session reference the reports carry: the storage path when
    /// the session has one, otherwise the session id.
    pub(crate) fn herdr_session_ref(core: &SessionCore) -> crate::herdr::HerdrSessionRef {
        crate::herdr::HerdrSessionRef::new(
            core.session_file(),
            (!core.session_id.is_empty()).then(|| core.session_id.clone()),
        )
    }

    /// Close the bound listener, then clean up the socket path: the TS
    /// graceful-shutdown sequence (daemon-mode.ts:8011-8018 awaits
    /// `server.close()` FIRST and runs `cleanupSocketPath()` after). The
    /// accept loop drops the listener it owns on the close request and
    /// confirms, so the cleanup below probes the path with the owner's
    /// listener provably closed - a live listener at the path can only
    /// be a successor's, and even a poisoned bind-time capture (a
    /// replacement landing in the bind->capture window) never unlinks
    /// the successor's live socket. The still-ours direction is
    /// unchanged: the worker's own closed file passes the probe dead and
    /// the identity gate unlinks exactly what it captured, so a respawn
    /// does not wait out the stale-socket path.
    ///
    /// The close confirmation is awaited UNCONDITIONALLY: a bound-flag
    /// check cannot close the check-then-act window between `serve`'s
    /// bind and the flag store (an exit landing exactly there would
    /// skip the wait and leave this worker's own dead socket behind -
    /// the refusal-exit variant of the stale-file bug). `serve` instead
    /// confirms exactly once on every path: after the accept loop drops
    /// the listener, or - with no listener - on the prepare/bind error
    /// returns. An exit that fires before the bind therefore waits out
    /// the whole setup and then unlinks only what the identity gate
    /// still owns, and a booting `serve` never strands a waiting exit
    /// path on a handshake that will not come. The parked confirmation
    /// also orders the identity read for the exits that fire inside
    /// `serve`'s setup (the registration-refusal exit racing the
    /// bind->capture gap): the capture precedes the accept loop's arm,
    /// which precedes this confirmation, so a bound listener's own
    /// cleanup always reads a captured identity, never the gap's
    /// `None`.
    pub(crate) async fn close_listener_then_cleanup_socket(&self) {
        self.listener_close_requested.notify_one();
        self.listener_closed.notified().await;
        let expected_identity = self.bound_socket_identity.lock().unwrap().clone();
        crate::socket::cleanup_socket_path_after_close(&self.config.socket_path, expected_identity);
    }

    /// The durable tail of a successful close: the resume entry, then the
    /// listener close and the worker's own socket cleanup (see
    /// [`Worker::close_listener_then_cleanup_socket`]). Already-accepted
    /// connections keep their own sockets, so the routed `shutdown` reply
    /// still reaches the supervisor after this tail.
    async fn finish_close(&self) {
        // Shutdown keeps the resume entry, like the TS close path.
        let _ = self.record_recovery(false, "shutdown");
        self.close_listener_then_cleanup_socket().await;
    }

    /// The refused-registration self-heal: the supervisor definitively
    /// rejected this worker's identity, so the worker retires with the same
    /// graceful close a routed `shutdown` runs, releasing its session lease.
    pub(crate) async fn exit_refused_registration(&self) {
        eprintln!(
            "eukhe-daemon worker {}: registration refused (the supervisor no longer owns this identity); retiring",
            std::process::id()
        );
        let _ = self.handle_shutdown().await;
        self.finish_close().await;
        std::process::exit(0)
    }
}

/// One revival-evidence record through `recovery` (no-op before `serve`
/// opened the journal).
pub(crate) fn record_recovery_with(
    recovery: &Arc<Mutex<Option<WorkerRecoveryJournal>>>,
    core: &Arc<Mutex<SessionCore>>,
    busy: bool,
    operation: &str,
) {
    let mut guard = recovery.lock().unwrap();
    let Some(journal) = guard.as_mut() else {
        return;
    };
    let (active_session_id, session_id, session_file) = {
        let core = core.lock().unwrap();
        (
            core.active_session_id.clone(),
            core.session_id.clone(),
            core.session_file(),
        )
    };
    if let Err(error) = journal.record(
        &active_session_id,
        &session_id,
        session_file.as_deref(),
        busy,
        operation,
    ) {
        eprintln!("eukhe-daemon worker: recovery journal write failed: {error:#}");
    }
}

/// Entry point for the worker process.
///
/// # Errors
///
/// Returns an error when the worker role env is missing (it must be
/// `WORKER_ROLE_ENV=1`), the worker env pair cannot be read, or the
/// serve loop fails.
pub async fn run_worker() -> Result<()> {
    if std::env::var(WORKER_ROLE_ENV).unwrap_or_default() != "1" {
        return Err(anyhow!("worker mode requires {WORKER_ROLE_ENV}=1"));
    }
    let config = WorkerConfig::from_env()?;
    let registration = crate::registration::start(&config);
    let worker = Arc::new(Worker::new(config, registration));
    if let Some(handle) = worker.registration.clone() {
        let worker = Arc::clone(&worker);
        tokio::spawn(async move {
            handle.retired().await;
            worker.exit_refused_registration().await;
        });
    }
    worker.serve().await
}
