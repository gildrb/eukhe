//! Supervisor runtime: one process spawning one worker per active session.
//!
//! Port of `modes/daemon/daemon-supervisor.ts`: the supervisor hosts no sessions
//! itself. Clients connect over a JSONL Unix socket; the supervisor spawns a
//! dedicated worker process per session, supervises it (restart with
//! exponential backoff, bounded attempts), persists worker descriptors so a
//! restarted supervisor can adopt or relaunch live sessions, and routes
//! commands and events between clients and workers (private-framed channel).

mod accept_loop;
pub(crate) mod adoption;
mod clients;
mod idle_shutdown;
mod launch_budget;
mod liveness;
mod notes;
mod options;
pub(crate) mod restart_budget;
mod root_identity;
mod routing;
mod sessions;
mod signals_shutdown;
pub(crate) mod subscribers;
mod worker_lifecycle;

use launch_budget::WORKER_AUTH_FLOOR_MS;
use signals_shutdown::daemon_closing_shutdown_event;
mod supervision;

#[cfg(test)]
mod handshake_tests;
#[cfg(test)]
mod spawn_record_tests;
#[cfg(test)]
mod tests;

pub(crate) use options::ClientRouting;
pub use options::SupervisorOptions;

pub(crate) use clients::client_command_payload;

// The routing consts and refusal string keep their crate::supervisor::* paths stable
// (external callers: supervisor_parent_death, create_reuse, prompt_admission,
// scheduling_catalog).
pub(crate) use routing::{
    client_route_admission, client_route_timeout, ROUTE_TIMEOUT_MS, SUMMARY_TIMEOUT_MS,
    WORKER_NOT_CONNECTED, WORKER_REQUEST_TIMEOUT_MS,
};

use worker_lifecycle::{probe_worker_socket, worker_connect_deadline};

use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;

use anyhow::{anyhow, bail, Context, Result};
use eukhe_types::daemon::{
    DaemonCommand, DaemonOutbound, DaemonSessionLifecycle, DaemonWorkerDescriptor,
    DaemonWorkerLifecycle, DurableDaemonCreateCommand, SnapshotPurpose,
};
use eukhe_types::platform::transport::{bind_transport, connect_transport, TransportStream};
use serde_json::{json, Map, Value};
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use tokio::process::Child;
use tokio::sync::{broadcast, mpsc, oneshot};

use crate::backpressure::RouteAdmission;
use crate::descriptor::{
    create_command_payload, load_descriptors, persist_supervisor_config, persist_worker,
    persist_worker_at, PersistedSupervisorConfig, TempSync, SUPERVISOR_CONFIG_FILE_NAME,
};
use crate::framing::{write_frame, PrivateFrameReader, DEFAULT_PRIVATE_FRAME_LIMITS};
use crate::paths;
use crate::prompt_admission::input_admission_id;
use crate::protocol::{
    command_active_session_id, command_type_name, current_protocol_info,
    parse_supervisor_command_line, response_failure, response_line, response_success,
    DaemonResponse, DaemonRuntimeIdentity, EnvelopeParseError, TypedCreateRejection,
    DAEMON_APP_VERSION, DAEMON_SCHEMA_ID, DAEMON_SCHEMA_REVISION,
};
use crate::registry::{
    ResidentWorker, SessionRegistry, WorkerRegistration, WorkerReply, WorkerRequest,
};
use crate::saved_session_commands::{name_unavailable_error, reservation_key, NameScope};
use crate::session_store::list_sessions;
use crate::snapshot_stream::{attach_client_capabilities, stream_attach, wants_chunked};
use crate::{socket, util};

pub struct Supervisor {
    pub(crate) options: SupervisorOptions,
    descriptor_dir: PathBuf,
    /// The bind-time filesystem identity of this supervisor's socket file
    /// (TS `DaemonSupervisor` captures `socketIdentity` right after
    /// `listen`, daemon-supervisor.ts:879): the exit cleanup passes it as
    /// the unlink's expected identity, so a file REPLACED at the path
    /// after this bind - an external sweep plus a successor's bind - is
    /// never unlinked by this process. `None` until `run` binds (named
    /// pipes keep `None`: there is no file to stat).
    bound_socket_identity: std::sync::Mutex<Option<socket::SocketIdentity>>,
    /// The per-supervisor launch-probe budget override: `None` rides the
    /// process-wide env seam (`EUKHE_DAEMON_WORKER_CONNECT_TIMEOUT_MS`),
    /// a pinned budget keeps a launch oracle's probe immediate without
    /// mutating that env var (a set value would leak into every
    /// parallel test's launch).
    worker_connect_budget: std::sync::Mutex<Option<Duration>>,
    /// The durable session-binding table (the stale-active-id rebind
    /// surface): every active id the supervisor has routed stays
    /// addressable through its session's durable identity, so a client
    /// holding a superseded id resolves to the session's current
    /// resident instead of `Unknown active session`.
    pub(crate) session_bindings: crate::session_bindings::SessionBindingTable,
    /// Per-session-file single-flight for opens (TS `openingWorkers`):
    /// one open at a time per file, so a concurrent create reuses (or
    /// waits out) the first one's worker instead of launching over it
    /// and losing the runtime session lease. Owned by the create-reuse
    /// seam (`create_reuse.rs`).
    pub(crate) opening_files:
        std::sync::Mutex<std::collections::HashMap<String, Arc<tokio::sync::Mutex<()>>>>,
    /// The boot adoption pass's settle signal (`true` once settled). A
    /// create over an existing session file waits for it: the pass runs
    /// beside the accept loop, and an open that raced it found no resident
    /// for a live worker the pass was still adopting, launched a second
    /// worker over the file, and bounced off the live worker's session
    /// lease. Starts settled (a supervisor that never serves adopts
    /// nothing); `serve` unsettles it before the accept loop and the pass
    /// settles it when it ends.
    pub(crate) boot_adoption: tokio::sync::watch::Sender<bool>,
    pub(crate) registry: SessionRegistry,
    /// Worker outbound frames, with their client routing. The payload is
    /// shared (`Arc`): every connected client's event arm receives every
    /// frame to decide delivery, and a per-receiver deep `Value` clone
    /// would multiply the frame's heap by the connection count on every
    /// event — the refcount bump is the whole cost for non-matching
    /// connections.
    pub(crate) events: broadcast::Sender<(ClientRouting, std::sync::Arc<Value>)>,
    /// Session-event subscribers: the send-time routing index (TS parity —
    /// `handleWorkerFrame` evaluates the attached set in the same pass that
    /// writes the socket). Session events enqueue to the attached
    /// connections' per-connection queues here instead of waking every
    /// connection's ring arm; broadcast-class events keep the ring above.
    pub(crate) session_subscribers: subscribers::SessionSubscribers,
    /// The `subscribe_state_tree` routing index: session -> the
    /// connections that get its `state_tree_update` frames.
    pub(crate) state_tree_subscribers: subscribers::SessionSubscribers,
    /// Live client connections: connection id -> the connection's
    /// effective client id (TS `this.clients` + `protocolClientId`).
    pub(crate) client_connections:
        std::sync::Mutex<std::collections::HashMap<String, Arc<std::sync::Mutex<String>>>>,
    /// The supervisor's agent roster (classified entries; the roster arms
    /// live in `supervisor_roster.rs`).
    pub(crate) roster: std::sync::Mutex<crate::agent_roster::AgentRoster>,
    /// The last `roster_update` content published per agent id (the
    /// content-diff guard, TS #2481): an entry whose content equals its
    /// last published form is dropped from the push (an identical
    /// rewrite broadcasts nothing), so subscribers never re-apply (and
    /// the wire never re-ships) a row that did not change.
    pub(crate) last_published_roster:
        std::sync::Mutex<std::collections::HashMap<String, serde_json::Value>>,
    /// In-flight registration-seed tasks (each `worker_register`'s
    /// background family walk). A `roster_subscribe` drains and awaits
    /// them before building its snapshot: a seeded row's push must
    /// never overtake the snapshot answer (a client that applies the
    /// push first and then the snapshot would lose the rows).
    pub(crate) pending_registration_seeds: std::sync::Mutex<Vec<tokio::task::JoinHandle<()>>>,
    /// In-flight name reservations (TS `pendingSessionNames`): one
    /// reservation per `[depth, parent, name]` scope, shared by the
    /// saved-session rename ladder and the subagent spawn admission (TS
    /// #2396 `createRlmSubagentRuntime`), so a concurrent rename or spawn
    /// of the same name in the same scope fails the second caller.
    pub(crate) pending_session_names: std::sync::Mutex<std::collections::HashSet<String>>,
    pub(crate) shutting_down: AtomicBool,
    /// The gate an idle shutdown holds while it decides: no worker is
    /// launched, relaunched or adopted meanwhile.
    pub(crate) replacement_gate: idle_shutdown::ReplacementGate,
    /// Whether some path has taken ownership of the one terminal stop pass.
    /// `shutting_down` flips synchronously when the shutdown command is
    /// accepted; this flag ensures exactly one connection runs
    /// `begin_shutdown`, even if several clients notice the shutdown.
    shutdown_started: AtomicBool,
    /// The connection that accepted the one terminal shutdown request. Only
    /// this connection may run the stop pass from its response-write or
    /// disconnect paths; another client disconnecting in the response window
    /// cannot preempt the acknowledgement.
    shutdown_owner: std::sync::Mutex<Option<String>>,
    /// The accept loop's exit flag. `shutting_down` refuses new work the
    /// moment a terminal stop begins, but the loop itself must stay up
    /// until [`Supervisor::begin_shutdown`] has stopped every resident
    /// worker: an inbound connection must not fall it out mid-stop and
    /// orphan the workers that pass is still shutting down.
    accept_exit: AtomicBool,
    /// Wakes the accept loop when [`Supervisor::begin_shutdown`] sets
    /// [`Self::accept_exit`]: a listening socket blocks in `accept` until
    /// a client connects, so the completed shutdown must interrupt it for
    /// the process to exit.
    shutdown_notify: tokio::sync::Notify,
    log: paths::RotatingLog,
    /// Memoized ledger over the default sessions dir (ledgers are per
    /// sessions-dir families; another dir gets a fresh instance).
    rlm_ledger: tokio::sync::Mutex<Option<std::sync::Arc<crate::rlm_ledger::RlmSpawnLedger>>>,
    /// The session input-pause leases (wave b8): pause id -> lease, the
    /// bookkeeping behind `acquire`/`release_session_input_pause`.
    pub(crate) input_pauses: crate::input_pause_lease::SupervisorPauseTable,
    /// The supervisor-side passive scheduled-jobs snapshot the catalog
    /// READ paths serve (TS #2487 `passiveScheduledJobs`): the
    /// session-artifacts tree scans once per generation instead of once
    /// per request. Daemon-owned mutations (and the saved-session
    /// delete/rename paths) drop it through
    /// `invalidate_passive_catalog`; a served snapshot older than the
    /// refresh window re-scans in the background
    /// (stale-while-revalidate). The mutation arms keep the fresh scan
    /// (TS `collectPassiveScheduledJobs` durable truth).
    pub(crate) passive_catalog:
        std::sync::Mutex<Option<crate::scheduling_catalog::PassiveCatalogSnapshot>>,
    /// One passive-catalog scan at a time (TS
    /// `passiveScheduledJobsScan ??=`): concurrent cold reads share one
    /// in-flight scan instead of each enqueueing its own.
    pub(crate) passive_scan_gate: tokio::sync::Mutex<()>,
    /// A stale refresh is already queued (TS `??=`'s one in-flight scan):
    /// readers that arrive while the background refresh runs share it
    /// instead of each spawning another refresh task.
    pub(crate) passive_scan_pending: std::sync::atomic::AtomicBool,
    /// The passive snapshot's publish epoch (TS #2487
    /// `passiveScheduledJobsEpoch`): an invalidation claims a newer epoch,
    /// so a scan that raced the invalidation cannot republish its
    /// pre-mutation rows as a fresh snapshot.
    pub(crate) passive_catalog_epoch: std::sync::atomic::AtomicU64,
    /// The terminal-compaction journal (the abort supervision): the
    /// supervisor's own durable record of compactions it declared aborted
    /// when the worker could not answer — feeds the replacement-worker
    /// create replay, cleared by a `compaction_end` that did land.
    pub(crate) compaction_journal:
        std::sync::Mutex<crate::compaction_supervision::TerminalCompactionJournal>,
    /// The chat memory, claimed at boot: the always-on supervisor owns
    /// `<agent-dir>/chat/lock` and runs the compactor, so the summaries
    /// keep up while no session is open; workers are its clients. `None`
    /// before boot, or when another live process owned the chat first
    /// (then this supervisor is a client that takes over when it exits).
    chat_memory: std::sync::Mutex<Option<eukhe_core::memory::Memory>>,
    /// Provider admission for every worker's model requests and the chat
    /// memory's compactor (`providerMaxInFlight`; see
    /// `provider_admission.rs`).
    pub(crate) provider_admission: Arc<crate::provider_admission::SupervisorAdmission>,
}

impl Supervisor {
    /// Build the supervisor: the descriptor dir, the persisted config,
    /// the event channel, the log, and the compaction-supervision
    /// journal.
    ///
    /// # Errors
    ///
    /// Returns an error when the agent dir, the sessions dir or the
    /// descriptor directory cannot be created or made private (0700), the
    /// sessions dir cannot be resolved, the supervisor config
    /// cannot be persisted, or the compaction-supervision journal cannot
    /// be opened.
    pub fn new(options: SupervisorOptions) -> Result<Self> {
        // The agent dir and the sessions root (an `EUKHE_SESSION_DIR`
        // override included) are private at every start.
        paths::ensure_dir(&options.agent_dir)?;
        paths::ensure_dir(&paths::sessions_dir(&options.agent_dir)?)?;
        let descriptor_dir =
            crate::descriptor::descriptor_dir(&options.agent_dir, &options.socket_path);
        paths::ensure_dir(&descriptor_dir)?;
        persist_supervisor_config(
            &descriptor_dir.join(SUPERVISOR_CONFIG_FILE_NAME),
            &PersistedSupervisorConfig {
                version: 1,
                socket_path: options.socket_path.to_string_lossy().to_string(),
                default_session_dir: Some(
                    paths::sessions_dir(&options.agent_dir)?
                        .to_string_lossy()
                        .to_string(),
                ),
            },
        )?;
        let (events, _) = broadcast::channel(crate::backpressure::EVENT_RING_CAPACITY);
        let log = paths::RotatingLog::new(paths::daemon_log_path(
            &options.socket_path,
            &options.agent_dir,
        ));
        let compaction_journal = crate::compaction_supervision::TerminalCompactionJournal::open(
            &descriptor_dir.join("compaction-supervision.jsonl"),
        )?;
        let provider_admission = Arc::new(crate::provider_admission::SupervisorAdmission::new(
            options.agent_dir.clone(),
        ));
        Ok(Supervisor {
            options,
            descriptor_dir,
            bound_socket_identity: std::sync::Mutex::new(None),
            worker_connect_budget: std::sync::Mutex::new(None),
            session_bindings: crate::session_bindings::SessionBindingTable::new(),
            opening_files: std::sync::Mutex::new(std::collections::HashMap::new()),
            boot_adoption: tokio::sync::watch::Sender::new(true),
            registry: SessionRegistry::new(),
            events,
            session_subscribers: subscribers::SessionSubscribers::new(),
            state_tree_subscribers: subscribers::SessionSubscribers::new(),
            client_connections: std::sync::Mutex::new(std::collections::HashMap::new()),
            roster: std::sync::Mutex::new(crate::agent_roster::AgentRoster::new()),
            last_published_roster: std::sync::Mutex::new(std::collections::HashMap::new()),
            pending_registration_seeds: std::sync::Mutex::new(Vec::new()),
            pending_session_names: std::sync::Mutex::new(std::collections::HashSet::new()),
            shutting_down: AtomicBool::new(false),
            replacement_gate: idle_shutdown::ReplacementGate::default(),
            shutdown_started: AtomicBool::new(false),
            shutdown_owner: std::sync::Mutex::new(None),
            accept_exit: AtomicBool::new(false),
            shutdown_notify: tokio::sync::Notify::new(),
            log,
            rlm_ledger: tokio::sync::Mutex::new(None),
            input_pauses: crate::input_pause_lease::SupervisorPauseTable::default(),
            passive_catalog: std::sync::Mutex::new(None),
            passive_scan_gate: tokio::sync::Mutex::new(()),
            passive_scan_pending: std::sync::atomic::AtomicBool::new(false),
            passive_catalog_epoch: std::sync::atomic::AtomicU64::new(0),
            compaction_journal: std::sync::Mutex::new(compaction_journal),
            chat_memory: std::sync::Mutex::new(None),
            provider_admission,
        })
    }

    /// Bind the client socket, adopt or relaunch persisted workers, serve.
    ///
    /// # Errors
    ///
    /// Returns an error when the socket path cannot be prepared (already
    /// in use), the supervisor socket cannot be bound, or the accept
    /// loop exhausts its give-up budget on a permanently broken
    /// listener (transient accept errors are retried; see `accept_loop`).
    ///
    /// # Panics
    ///
    /// Panics when a supervisor mutex is poisoned (a holder panicked
    /// while holding the lock).
    pub async fn run(self: Arc<Self>) -> Result<()> {
        // Before any socket or worker exists: workers and their kernels
        // inherit the raised limit.
        let open_file_limit = eukhe_core::platform::process::raise_open_file_limit();
        socket::prepare_socket_path(&self.options.socket_path).await?;
        // The OS-signal drain (SIGTERM/SIGINT; the loop lives in
        // `crate::signal_drain`): `install` registers the handlers
        // synchronously here, BEFORE the bind below. The socket accepts
        // connects from its `listen` on, and everything between the bind
        // and the accept loop awaits (the bind-capture gap, the chat-memory
        // claim, the boot reap): a client that reached the socket - a
        // readiness probe, a service manager's stop right after it - must
        // find the drain, never the default disposition, whose signal
        // death skips the exit cleanup and strands the socket file. The
        // stale-socket prepare above keeps the default disposition: no
        // client can reach this process yet, and a supervisor parked there
        // still dies to one signal. From here on, the first signal drains
        // (new work refused, running turns settled; a drain begun before
        // the accept loop makes it exit on entry) and a later signal
        // force-exits.
        tokio::spawn(crate::signal_drain::install(Arc::clone(&self)));
        let listener = bind_transport(
            &self.options.socket_path,
            eukhe_bend::rules::fsmode::peer_verdict,
        )
        .await
        .with_context(|| {
            format!(
                "bind supervisor socket {}",
                self.options.socket_path.display()
            )
        })?;
        socket::bind_capture_gap().await;
        // Capture the bound file's identity before anything can replace
        // it (TS daemon-supervisor.ts:879, between `listen` and
        // `restrictDaemonSocketPath`): the exit cleanup below compares
        // against THIS value, never a fresh read, so a successor's file
        // at the same path survives this supervisor's exit.
        *self.bound_socket_identity.lock().unwrap() =
            socket::socket_identity(&self.options.socket_path);
        socket::restrict_socket_path(&self.options.socket_path)?;
        self.log
            .append(&format!("supervisor started pid {}", std::process::id()));
        // Claim the chat memory only once this process owns the daemon
        // socket: a second supervisor that lost the bind never gets here.
        // A failure is logged; sessions report their own when they open it.
        // The compactor's requests take background slots of this daemon's
        // admission, so the sessions' requests come first.
        match eukhe_core::memory::Memory::open(
            eukhe_core::memory::chat_dir(&self.options.agent_dir),
            Arc::new(eukhe_core::memory::SettingsSummarizer::new(
                self.options.agent_dir.clone(),
                eukhe_core::admission::AdmissionHandle::new(Arc::clone(&self.provider_admission)),
            )),
        )
        .await
        {
            Ok(memory) => {
                let owner = if memory.owns().await {
                    "owner"
                } else {
                    "client"
                };
                self.log.append(&format!("chat memory open ({owner})"));
                *self.chat_memory.lock().unwrap() = Some(memory);
            }
            Err(error) => self
                .log
                .append(&format!("chat memory unavailable: {error:#}")),
        }
        match open_file_limit {
            Ok(limit) => self.log.append(&format!("open file limit {limit}")),
            Err(error) => self
                .log
                .append(&format!("open file limit raise failed: {error}")),
        }

        // The boot reap (the operator's same-socket predecessor rule): this
        // daemon now owns the socket's lineage, so leftover worker processes
        // of a dead predecessor - alive, still holding their runtime session
        // leases, unreachable through any descriptor or registration - die
        // here, and a wedged predecessor supervisor dies with them. Daemons
        // and workers on OTHER sockets are never touched (the scan matches
        // the socket path alone). The reap precedes the adoption pass and
        // the first client: a create racing a leftover holder would answer
        // the lease refusal this pass exists to clear. Bounded by
        // construction (every target shares one escalation window).
        crate::boot_reap::reap_predecessors(&self).await;
        // The endpoint half of the same lineage rule: worker sockets (and
        // their cleanup lock dirs) this socket's dead workers left beside
        // it are removed; a killed worker never unlinks its own.
        let removed = socket::reap_stale_worker_sockets(&self.options.socket_path).await;
        if removed > 0 {
            self.log_line(&format!(
                "boot reap: removed {removed} stale worker socket(s)"
            ));
        }

        // Descriptor adoption runs concurrently with the accept loop: a
        // supervisor restarted over live sessions must accept their
        // self-registrations immediately, not behind the whole descriptor
        // scan. The fan-out is capped (recovery_pacing) so a large
        // sessions dir cannot starve the control plane. Once the pass
        // settles, the boot reports the due scheduled jobs that stay
        // dormant (no session auto-boots on daemon start).
        self.boot_adoption.send_replace(false);
        {
            let supervisor = Arc::clone(&self);
            tokio::spawn(async move {
                let settle = SettleBootAdoption(&supervisor.boot_adoption);
                supervisor.adopt_persisted_workers().await;
                drop(settle);
                supervisor.report_dormant_scheduled_jobs().await;
            });
        }

        // Warm the passive scheduled-jobs snapshot (the input-latency
        // lane): the first selector-less `heartbeats_list`/`cron_list`
        // after boot would otherwise scan the whole session-artifacts tree
        // inline while the interactive client's open waits on it. The scan
        // waits out the boot's adopt pass first (the pre-bar review's
        // race finding): the scan's live-worker filter consults the
        // registry, so a scan that raced the adopt pass would cache the
        // just-adopted worker's artifacts as a passive row and serve the
        // stale row for the snapshot's whole refresh window — adoption
        // never invalidates the catalog. After the signal (a plain
        // startup's adopt pass is ms-scale) the scan still lands well
        // before the first client read; every invalidation and refresh
        // rule is unchanged. The signal is fail-open: an adopt pass that
        // died without signaling still warms (a degraded boot keeps the
        // pre-warmup cold-read behavior, never a colder one).
        {
            let supervisor = Arc::clone(&self);
            let mut adopted = self.boot_adoption.subscribe();
            tokio::spawn(async move {
                Supervisor::wait_for_adoption_signal(&mut adopted).await;
                supervisor.spawn_passive_catalog_warmup();
            });
        }

        // Session-archive sweep (roadmap: the sessions directory must not
        // grow forever) and the sweep of the staging dirs, delete
        // tombstones and staging lock files a crash left behind: boot
        // sweep, then the periodic re-sweep at the TS idle-eviction
        // cadence. Housekeeping only — it never gates serving.
        {
            let supervisor = Arc::clone(&self);
            tokio::spawn(async move {
                crate::session_archive::archive_sweep_loop(&supervisor).await;
            });
        }

        // Boot housekeeping, off the executor: dead-owner lease dirs and
        // aged socket logs go. Journals without verifiable ownership stay
        // intact: a missing descriptor does not prove that no worker still
        // needs them.
        {
            let supervisor = Arc::clone(&self);
            tokio::task::spawn_blocking(move || {
                let leases = crate::lease::reclaim_dead_owner_leases(&supervisor.options.agent_dir);
                let logs = crate::worker_stderr::prune_socket_logs(
                    &supervisor.options.agent_dir,
                    &supervisor.options.socket_path,
                );
                if leases + logs > 0 {
                    supervisor.log_line(&format!(
                        "boot cleanup: removed {leases} dead-owner lease dir(s), {logs} old socket log(s)"
                    ));
                }
            });
        }
        accept_loop::serve(&self, listener).await?;
        // The accept loop OWNED the listener, so its return already
        // closed it (TS daemon-supervisor.ts:7436-7491 awaits the
        // "daemon server" close step before the "daemon socket" cleanup
        // step): the cleanup below probes the path with the owner's
        // listener provably closed, so a successor's live socket at the
        // path survives even a poisoned bind-time capture.
        let expected_identity = self.bound_socket_identity.lock().unwrap().clone();
        socket::cleanup_socket_path_after_close(&self.options.socket_path, expected_identity);
        Ok(())
    }
}

/// One outbound client-socket line: a JSON value the connection serializes,
/// or the pre-serialized bytes of a relayed worker response (the zero-copy
/// route hands the worker's own line through with the client's command id
/// spliced in front).
pub(crate) enum Outbound {
    Line(Value),
    Raw(Vec<u8>),
}

/// Settles the boot adoption signal when dropped: at the pass's end, or
/// while a panicking pass unwinds (an unsettled signal would park every
/// open of an existing session).
struct SettleBootAdoption<'a>(&'a tokio::sync::watch::Sender<bool>);

impl Drop for SettleBootAdoption<'_> {
    fn drop(&mut self) {
        self.0.send_replace(true);
    }
}

/// Entry point for the supervisor process.
///
/// # Errors
///
/// Returns an error when the supervisor cannot start (see
/// [`Supervisor::new`]) or its serve loop fails (see
/// [`Supervisor::run`]).
pub async fn run_supervisor(options: SupervisorOptions) -> Result<()> {
    let supervisor = Arc::new(Supervisor::new(options)?);
    supervisor.run().await
}
