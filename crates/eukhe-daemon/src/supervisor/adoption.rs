//! Worker adoption: the boot discovery pass and the per-worker
//! adoption outcomes.

use std::sync::Arc;

use super::{
    anyhow, bail, json, load_descriptors, response_failure, response_success, socket,
    worker_connect_deadline, Child, Context, DaemonCommand, DaemonResponse, DaemonWorkerLifecycle,
    Duration, Ordering, Path, PathBuf, ResidentWorker, Result, RouteAdmission, Supervisor, Value,
    WorkerRegistration,
};
use crate::timeouts::STOP_GRACE_MS;

/// An unobservable start identity does not prove that a live pid was recycled.
/// Only an observed mismatch proves the descriptor's process is gone.
fn recorded_process_alive(
    alive: Option<bool>,
    expected: Option<&str>,
    observed: Option<&str>,
) -> bool {
    alive != Some(false) && (expected.is_none() || observed.is_none() || expected == observed)
}

/// Whether a supervisor keeps a live worker it finds (law
/// `adopt_same_build`, `laws/launcher.bend` D1; the model in bend/launcher.bend).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Adoption {
    /// The worker runs this supervisor's build: it is adopted.
    Adopt,
    /// The worker runs another build, or does not say which: it is not
    /// adopted. It stops the way a lost worker stops (its work stays
    /// resumable) and its session relaunches on this build.
    Replace,
}

/// The adoption verdict for a worker that reports `worker_build` (`None`:
/// a worker that reports no build) to a supervisor of `supervisor_build`.
pub(crate) fn adoption_verdict(supervisor_build: &str, worker_build: Option<&str>) -> Adoption {
    if worker_build == Some(supervisor_build) {
        Adoption::Adopt
    } else {
        Adoption::Replace
    }
}

impl Supervisor {
    /// Adopt or relaunch persisted workers, concurrently: one dead worker's
    /// relaunch (create replay) must not delay adopting live sessions. The
    /// fan-out is capped ([`crate::recovery_pacing::ADOPTION_CONCURRENCY`]):
    /// a large sessions dir must not turn the pass into a relaunch storm
    /// that starves the control plane for its whole duration.
    pub(super) async fn adopt_persisted_workers(self: &Arc<Self>) {
        let descriptors = load_descriptors(&self.descriptor_dir, &self.options.socket_path);
        let jobs: Vec<_> = descriptors
            .into_iter()
            .map(|(path, descriptor)| {
                let supervisor = Arc::clone(self);
                move || async move {
                    supervisor.adopt_persisted_worker(path, descriptor).await;
                }
            })
            .collect();
        crate::recovery_pacing::run_bounded(jobs, crate::recovery_pacing::ADOPTION_CONCURRENCY)
            .await;
        // TS arms the owner cleanup for every adopted worker: an owner that
        // does not reconnect within the grace loses its worker.
        for resident in self.registry.list().await {
            self.schedule_owned_worker_cleanup(&resident).await;
        }
        // The boot roster seed runs exactly once, in the background, now
        // that adoption settled: the registry's residents are the seed
        // roots. TS awaits its seed before adoption; the Rust daemon
        // deliberately accepts before and during adoption, so the seed
        // follows the pass and its one `roster_update` publish carries
        // the rows to early subscribers. Tests drain the pending-seed
        // barrier for completion.
        self.spawn_roster_boot_seed();
    }

    /// Adopt one persisted worker descriptor. Serialized against worker
    /// self-registration by the per-worker adoption gate: whichever path
    /// arrives first (descriptor scan or live re-registration) builds the
    /// roster entry; the other one finds it present.
    async fn adopt_persisted_worker(
        self: &Arc<Self>,
        path: PathBuf,
        descriptor: crate::descriptor::WorkerDescriptor,
    ) {
        let worker_id = descriptor.worker_id.clone();
        // An adoption brings a live worker into the roster: it waits while
        // an idle shutdown decides, like a launch.
        let _launch = self.replacement_gate.enter_launch().await;
        let guard = self.registry.adoption_guard(&worker_id).await;
        if self.registry.get(&worker_id).await.is_some() {
            // The worker re-registered before the descriptor scan reached it.
            self.log_line(&format!(
                "session worker {worker_id} already registered; skipping descriptor adoption"
            ));
            return;
        }
        let socket_path = PathBuf::from(&descriptor.socket_path);
        // A tombstoned descriptor belongs to its recorded process, not
        // whichever listener now owns its pathname. A dead pid (or a
        // recycled one with a different start id) must bypass auth and
        // finish the stop; a foreign listener can otherwise keep adoption
        // waiting behind the worker-auth budget. TS adoptOrRecoverWorker
        // checks the recorded pid before connecting a stopped worker.
        // Ordinary descriptors retain the existing socket-based revival
        // decision, which also handles descriptors without a start id.
        // The identity probes are the tombstone's alone: an ordinary
        // descriptor's stop term is `stop_requested_at.is_none()` and the
        // OR never reads the probes, so running them for every descriptor
        // pays a process spawn (`ps` on Unix platforms without /proc or
        // sysctl) inside the async adoption task - blocking an executor
        // worker at boot. The tombstoned path runs the probes off the
        // runtime through `spawn_blocking`; a join failure conservatively
        // treats the recorded process as alive (the graceful IPC leg
        // below degrades to the same finalize a dead verdict runs).
        let tombstoned = descriptor.stop_requested_at.is_some();
        let recorded_process_alive = if tombstoned {
            let pid = descriptor.pid as u32;
            let expected = descriptor.process_start_id.clone();
            tokio::task::spawn_blocking(move || {
                recorded_process_alive(
                    crate::lease::is_process_alive(pid).ok(),
                    expected.as_deref(),
                    crate::lease::get_process_start_id(pid).as_deref(),
                )
            })
            .await
            .unwrap_or(true)
        } else {
            true
        };
        let alive = (descriptor.stop_requested_at.is_none() || recorded_process_alive)
            && socket::can_connect(&socket_path, Duration::from_millis(500)).await;
        let pid = descriptor.pid;
        let journal_path = PathBuf::from(&descriptor.recovery_journal_path);
        let resident = ResidentWorker::new(worker_id.clone(), descriptor, path);
        // The durable pending FIRST: a failed identity persist left a side
        // record beside this descriptor carrying the moved-to identity —
        // apply it before any routing, relaunch, or revival can act on the
        // stale record (a revived worker replays the moved-to session's
        // create path), and retry the record's persist: the repair removes
        // the side record, a failure arms the resident's pending marker
        // for the first roster write.
        self.apply_identity_pending(&resident).await;
        // The stop tombstone outranks liveness (TS's stop ownership: the
        // stop was durable intent BEFORE the worker was told): a
        // supervisor that died between the tombstone and the worker's
        // shutdown finishes the stop on the next boot — never adopts the
        // still-reachable worker as healthy (that would drop the stop and
        // leave the stopped session resident).
        if resident.descriptor.lock().await.stop_requested_at.is_some() {
            self.finish_tombstoned_stop(&resident, alive).await;
            return;
        }
        // The adoption answer plus the revival's spawned child, when one
        // was launched: the monitor must watch the process that actually
        // runs, never the descriptor's stale pre-restart pid (the
        // zombie-holder incident: a revived worker was alive and serving
        // while the monitor polled the dead pid the supervisor replaced,
        // counted six phantom exits, gave up on the id, and left the live
        // holder - lease and all - orphaned with every create refused).
        let worker_build = resident
            .descriptor
            .lock()
            .await
            .build_id()
            .map(str::to_string);
        let (result, revived_child) = if alive {
            match adoption_verdict(eukhe_build_info::DAEMON_BUILD_ID, worker_build.as_deref()) {
                // A live worker of another build (or of no recorded build)
                // is not adopted: its session moves to this build.
                Adoption::Replace => match self.replace_worker_build(&resident).await {
                    Ok(child) => (Ok(()), Some(child)),
                    Err(error) => (Err(error), None),
                },
                Adoption::Adopt => {
                    let adopted = self
                        .connect_worker(&resident, worker_connect_deadline())
                        .await;
                    if adopted.is_ok() {
                        // The boot reconciliation (the root-identity seam): the
                        // adopted worker already serves a session this supervisor
                        // has only ever seen through its PERSISTED record — and
                        // the record can name a superseded session (a whole-session
                        // replacement whose identity persist failed before the
                        // restart, or any descriptor the restart re-adopted
                        // mid-flight). Pull the live state BEFORE the routing
                        // opens: the roster write carries the identity follow, so
                        // the descriptor, the persisted record, and the binding
                        // re-bind onto the session the worker actually serves
                        // before a single client route can resolve them. A failed
                        // pull serves the persisted identity (logged) until the
                        // next roster write runs the follow from the live state.
                        if !self.refresh_roster_entry(&resident).await {
                            // A failed pull is not proof the worker is dead: the
                            // persisted identity is unreconciled, so the resident
                            // is quarantined from every identity route until the
                            // live word lands (a slow pull retries on the
                            // backoff below; the worker's own roster push or a
                            // later pull clears the fence). The routing refuses
                            // (the conservative miss) instead of serving the
                            // superseded identity.
                            resident.mark_identity_quarantined();
                            self.spawn_identity_reconciliation_retry(&resident);
                            self.log_line(&format!(
                        "session worker {worker_id}: the boot reconciliation pull failed; the resident is quarantined from routing until the live state lands"
                    ));
                        }
                        // The adopted worker's session already exists (its create
                        // ran before the supervisor restart): routed client
                        // commands may reach it immediately.
                        resident.note_session_ready();
                    } else {
                        // A live worker this boot cannot reach would keep the
                        // session's lease with no supervisor routing to it:
                        // the retry under the restart budget below stops it
                        // before each relaunch (never beside it). Only a
                        // recorded start id proves the pid is still that
                        // worker; without one the pid may be recycled, and
                        // the give-up's belt (`reap_abandoned_workers`) is
                        // left to find it.
                        let start_id = resident.descriptor.lock().await.process_start_id.clone();
                        match start_id {
                            Some(start_id) => {
                                *resident.survivor.lock().await =
                                    Some((pid as u32, Some(start_id)));
                                self.log_line(&format!(
                                    "session worker {worker_id} is alive but unreachable; it is stopped before the relaunch"
                                ));
                            }
                            None => self.log_line(&format!(
                                "session worker {worker_id} is alive but unreachable; no recorded start id, not signaled"
                            )),
                        }
                    }
                    (adopted, None)
                }
            }
        } else {
            let interrupted =
                crate::journal::WorkerRecoveryJournal::read_interrupted(&journal_path);
            if !interrupted {
                // Dead worker with no durable busy state: not interrupted
                // work. Leave it down (the descriptor stays on disk, inert)
                // — the session reopens lazily through the next client
                // create, like a TS supervisor that parks dead workers
                // instead of reviving them.
                self.log_line(&format!(
                    "session worker {worker_id} was idle at exit; not revived (reopens on the next client open)"
                ));
                return;
            }
            // The revival ownership gate: the busy-evidence filter above
            // answered "did the journal ever prove live work?"; this gate
            // answers "is that proof still a genuine interruption THIS
            // boot must heal?" A give-up verdict (lifecycle `failed`), a
            // stopped session (the #2592 archived belt), a live session
            // lease held by another worker (this daemon's or another
            // daemon's, on a shared agent dir), or busy evidence older
            // than the freshness bound each vetoes the relaunch: the
            // descriptor stays down and the session reopens through the
            // next client create. Without the gate a boot re-storms the
            // same dead slots (stale journals outliving their era) and
            // resurrects stopped sessions as active workers.
            let busy_recorded_at =
                crate::journal::WorkerRecoveryJournal::latest_busy_recorded_at(&journal_path);
            let gated = resident.descriptor.lock().await;
            let veto = crate::revival_gate::revival_veto(
                &self.options.agent_dir,
                &gated,
                busy_recorded_at.as_deref(),
                crate::util::now_ms(),
            );
            drop(gated);
            if let Some(veto) = veto {
                self.log_line(&format!(
                    "session worker {worker_id} not revived: {}",
                    veto.log_reason()
                ));
                return;
            }
            // Dead worker with journal-proven live work: relaunch from the
            // durable create command. The worker rehydrates the session
            // store, restoring history and the persisted queue snapshot.
            // The spawned child rides out to the monitor arming below: the
            // descriptor's pid is the DEAD pre-restart holder, and a
            // monitor parked on it reports a phantom exit of a process
            // this very adoption just launched.
            match self.relaunch_worker(&resident).await {
                Ok(child) => (Ok(()), Some(child)),
                Err(error) => (Err(error), None),
            }
        };
        match result {
            Ok(()) => {
                self.registry.insert(Arc::clone(&resident)).await;
                // A live leftover keeps its real pid; a revived worker is
                // watched through the child handle itself (the pid the
                // spawn recorded in the descriptor, never the stale one).
                match revived_child {
                    Some(child) => {
                        let child_pid = child.id().unwrap_or(0);
                        self.spawn_monitor(
                            Arc::clone(&resident),
                            Some(child),
                            u64::from(child_pid),
                        );
                    }
                    None => self.spawn_monitor(Arc::clone(&resident), None, pid),
                }
                // The adopted worker joins the roster from its live state.
                self.refresh_roster_entry(&resident).await;
                self.log_line(&format!(
                    "adopted session worker {worker_id} (was alive: {alive})"
                ));
            }
            Err(error) => {
                self.log_line(&format!(
                    "could not adopt worker {worker_id}: {error:#}; retrying under the restart budget"
                ));
                self.retry_failed_launch(&resident).await;
            }
        }
        drop(guard);
    }

    /// `worker_register`: a session worker presenting its identity (boot
    /// registration or re-registration after this supervisor restarted).
    /// The token was issued when the supervisor spawned or adopted the
    /// worker, so an unknown worker id or a token mismatch is rejected.
    pub(super) async fn handle_worker_register(
        self: &Arc<Self>,
        command_id: &str,
        type_name: &str,
        command: &DaemonCommand,
    ) -> DaemonResponse {
        let DaemonCommand::WorkerRegister {
            active_session_id,
            session_id,
            socket_path,
            worker_instance_id,
            token,
            pid,
            build_id,
            ..
        } = command
        else {
            return response_failure(Some(command_id), type_name, "not a registration", None);
        };
        let fail = |error: &str| response_failure(Some(command_id), type_name, error, None);
        if self.shutting_down.load(Ordering::SeqCst) {
            return fail("Supervisor is shutting down");
        }
        if active_session_id.is_empty() || socket_path.is_empty() || *pid == 0 {
            return fail("Session worker registration is missing identity fields");
        }
        let worker_instance_id =
            (!worker_instance_id.is_empty()).then(|| worker_instance_id.clone());
        let registration = WorkerRegistration {
            active_session_id: active_session_id.clone(),
            session_id: session_id
                .clone()
                .filter(|value: &String| !value.is_empty()),
            socket_path: socket_path.clone(),
            worker_instance_id: worker_instance_id.clone(),
            pid: *pid,
        };
        // Serialize against descriptor adoption for the same worker.
        let guard = self.registry.adoption_guard(active_session_id).await;
        let resident = match self.registry.get(active_session_id).await {
            Some(resident) => resident,
            None => match self
                .adopt_registered_worker(
                    &registration,
                    token,
                    adoption_verdict(eukhe_build_info::DAEMON_BUILD_ID, build_id.as_deref()),
                )
                .await
            {
                Ok(resident) => resident,
                Err(error) => {
                    let message = format!("{error:#}");
                    // The definitive unknown-worker refusal is observable
                    // (logged) and the worker retires on it: a live
                    // worker this supervisor will never adopt (its descriptor
                    // is gone, or its registration hit a stop tombstone)
                    // would otherwise hold its session lease forever.
                    if message.starts_with(crate::registration::UNKNOWN_SESSION_WORKER_PREFIX) {
                        self.log_line(&format!(
                            "session worker {active_session_id} registration refused; the worker retires"
                        ));
                    }
                    return fail(&message);
                }
            },
        };
        // Refresh the durable identity from the live worker (the token was
        // issued by this supervisor; a mismatch is a rogue registration).
        {
            let mut descriptor = resident.descriptor.lock().await;
            if token.as_str() != descriptor.authentication_token {
                return fail("Session worker authentication failed");
            }
            let previous_worker_instance_id = descriptor.worker_instance_id.clone();
            // A REPLACEMENT registration flips the roster's stale-delta
            // slot to the replacement BEFORE the replacement is exposed
            // anywhere — the descriptor update below, the persisted
            // record, the recorded registration: a predecessor's pull or
            // frame still in flight must already meet the slot naming the
            // replacement (its own stamp mismatches and drops), never the
            // predecessor it carries. A same-process re-register (a
            // dropped supervisor link, a create replay) keeps the slot
            // untouched — the counter did not restart.
            if previous_worker_instance_id.as_deref() != worker_instance_id.as_deref() {
                let replacement = worker_instance_id.clone().unwrap_or_default();
                let mut roster = self.roster.lock().unwrap();
                roster.note_worker_generation(&resident.worker_id, &replacement);
            }
            descriptor.pid = *pid;
            // Refresh the identity from the live registrant (TS captures
            // an identity while the process is known alive): a supervisor
            // restart re-adopts the worker, and a pid that was recycled in
            // between must not keep the old holder's identity. An
            // unobservable start id keeps the previous value (a possibly
            // live worker is never orphaned on a transient lookup failure).
            if let Some(start_id) = crate::protocol::process_start_id(*pid as u32) {
                descriptor.process_start_id = Some(start_id);
            }
            descriptor.socket_path.clone_from(socket_path);
            // The registrant's own build word (in memory; the next persist
            // carries it to the descriptor the next boot's adoption reads).
            if let Some(build_id) = build_id {
                descriptor.set_build_id(build_id);
            }
            descriptor
                .worker_instance_id
                .clone_from(&worker_instance_id);
            if let Some(session_id) = &registration.session_id {
                descriptor.root_session_id = Some(session_id.clone());
            }
            descriptor.lifecycle = DaemonWorkerLifecycle::Ready;
            // A (re-)registered worker refreshes its binding: the id stays
            // addressable with its current durable identity across supervisor
            // restarts, and a session file this id newly owns supersedes any
            // earlier binding to it.
            self.record_session_binding(
                active_session_id,
                descriptor.root_session_id.as_deref(),
                descriptor.session_file.as_deref(),
            );
            // The registration refreshes the resident in memory only — no
            // persist here. The spawn record already carries the
            // launch-time identity (pid, socket), and the create-completion
            // persist (`launch_worker`'s post-create write) owns the next
            // durable state — `Ready` with the session identity — as the
            // metadata-survival barrier. The boot scan adopts a live worker
            // socket-first regardless of the recorded lifecycle, and a dead
            // worker's recovery replays the durable create command.
        }
        let record = self.registry.record_registration(registration).await;
        let verb = if record.epoch > 1 {
            "re-registered"
        } else {
            "registered"
        };
        self.log_line(&format!(
            "session worker {active_session_id} {verb} (epoch {}, pid {pid})",
            record.epoch
        ));
        drop(guard);
        // Registration rebuilt the resident: refresh its roster entry from
        // the live worker so the roster reflects the re-registered state.
        self.refresh_roster_entry(&resident).await;
        // A worker that registers after the boot seed (a supervisor
        // restart's re-registration, a mid-tree resume, a wakened ledger
        // child) publishes its passive ledger family in the background:
        // TS reseeds the family when the worker's first roster snapshot
        // applies (`applyWorkerRosterSnapshot`), and this port's workers
        // push only their own summary, so the daemon walks the family
        // here instead. Registration answers on the client's open path -
        // the seed never blocks it.
        let family_root = {
            let descriptor = resident.descriptor.lock().await;
            descriptor
                .session_file
                .clone()
                .or_else(|| descriptor.create_command.session_path.clone())
        };
        if let Some(root) = family_root {
            self.spawn_roster_registration_seed(Path::new(&root));
        }
        response_success(
            Some(command_id),
            type_name,
            Some(json!({
                "workerId": active_session_id,
                "sessionId": session_id,
                "supervisorGeneration": format!("sup:{}", std::process::id()),
                "supervisorPid": std::process::id(),
                "epoch": record.epoch,
            })),
        )
    }

    /// A registration for a worker with no roster entry: adopt it from its
    /// persisted descriptor (the durable fallback record). The registration
    /// proves the worker process is alive; adoption connects it for routing.
    async fn adopt_registered_worker(
        self: &Arc<Self>,
        registration: &WorkerRegistration,
        token: &str,
        adoption: Adoption,
    ) -> Result<Arc<ResidentWorker>> {
        // An adoption brings a live worker into the roster: it waits while
        // an idle shutdown decides, like a launch.
        let _launch = self.replacement_gate.enter_launch().await;
        let descriptor_path = self
            .descriptor_dir
            .join(format!("{}.json", registration.active_session_id));
        let content = match std::fs::read_to_string(&descriptor_path) {
            Ok(content) => content,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                // The TS unknown-worker error: this supervisor holds no
                // descriptor for the identity, so it can never adopt the
                // registrant. The worker treats the verdict as terminal
                // (the refused-registration self-heal) and retires
                // instead of retrying forever.
                return Err(anyhow!(
                    "{}: {}",
                    crate::registration::UNKNOWN_SESSION_WORKER_PREFIX,
                    registration.active_session_id
                ));
            }
            // An unreadable descriptor is NOT an unknown worker: the
            // identity exists on disk, and retiring it over a transient
            // I/O failure (permissions, a torn read) would strand a live
            // lease holder behind a healable condition. The worker keeps
            // its backoff loop; the next attempt re-reads the file.
            Err(error) => {
                return Err(anyhow!(
                    "descriptor read failed for {}: {error}",
                    registration.active_session_id
                ));
            }
        };
        let descriptor: crate::descriptor::WorkerDescriptor = serde_json::from_str(&content)
            .with_context(|| format!("invalid descriptor {}", descriptor_path.display()))?;
        crate::descriptor::validate_descriptor(&descriptor, &self.options.socket_path)?;
        if token != descriptor.authentication_token.as_str() {
            return Err(anyhow!("Session worker authentication failed"));
        }
        let worker_id = descriptor.worker_id.clone();
        let resident = ResidentWorker::new(
            registration.active_session_id.clone(),
            descriptor,
            descriptor_path,
        );
        // The durable pending (the same repair the descriptor adoption
        // runs): the registration rebuilt the resident from the PERSISTED
        // record — apply the failed follow's side record before the
        // routing opens, so the in-memory identity serves the moved-to
        // session even when the reconciliation pull below fails (the
        // quarantine fences the routes until the live word lands).
        self.apply_identity_pending(&resident).await;
        // A tombstoned identity is mid-stop (TS `adoptOrRecoverWorker`'s
        // stopRequestedAt branch): adoption finishes the stop — the
        // original command forwarded, the variant's finalize belt, the
        // descriptor retired with the process — and never adopts the
        // worker as healthy (that would undo the stop and leave the
        // stopped session held by the leftover process). The refusal is
        // definitive: the registrant is the process the stop must retire,
        // so it exits on the verdict instead of re-registering into the
        // same unfinished stop.
        if resident.descriptor.lock().await.stop_requested_at.is_some() {
            // The registering process is the identity the stop must
            // retire: the persisted descriptor still carries the stopped
            // worker's stale pid, so observing the registrant's live
            // identity first keeps the retire pass's escalation - and the
            // descriptor's death - tied to the process that actually
            // holds the session (TS `adoptOrRecoverWorker` persists the
            // observed start id after its authenticated connect).
            // Without this, a replacement registrant's stop would retire
            // the stale pid, conclude the replacement was gone, and
            // orphan the live worker as an unadoptable lease holder.
            {
                let mut descriptor = resident.descriptor.lock().await;
                if descriptor.pid != registration.pid {
                    descriptor.pid = registration.pid;
                }
                if let Some(start_id) = crate::lease::get_process_start_id(registration.pid as u32)
                {
                    descriptor.process_start_id = Some(start_id);
                }
                let _ = crate::descriptor::persist_worker(&resident.descriptor_path, &descriptor);
            }
            self.finish_tombstoned_stop(&resident, true).await;
            return Err(anyhow!(
                crate::registration::tombstoned_registration_refusal(
                    &registration.active_session_id
                )
            ));
        }
        match adoption {
            Adoption::Adopt => {}
            Adoption::Replace => {
                // The registrant runs another build: it is not adopted. The
                // persisted pid is stale, so the live registrant's identity
                // is recorded first: the handover waits for this process.
                {
                    let mut descriptor = resident.descriptor.lock().await;
                    descriptor.pid = registration.pid;
                    descriptor.process_start_id =
                        crate::lease::get_process_start_id(registration.pid as u32);
                }
                self.spawn_build_replacement(resident);
                return Err(anyhow!(
                    "{}: {} runs another build: its session moves to this supervisor's build; registration refused",
                    crate::registration::UNKNOWN_SESSION_WORKER_PREFIX,
                    registration.active_session_id
                ));
            }
        }
        self.connect_worker(&resident, worker_connect_deadline())
            .await?;
        // The boot reconciliation (the root-identity seam): registration
        // rebuilt the resident from the PERSISTED record — and the worker
        // already serves a whole-session replacement (a fork/switch the
        // record never learned, or whose identity persist failed before
        // this restart). Pull the live state BEFORE the resident joins the
        // registry: the roster write carries the identity follow, so the
        // descriptor, the persisted record, and the binding re-bind onto
        // the session the worker actually serves before any client route
        // can resolve them (the registration block above recorded the
        // persisted identity — this heals it from the live truth).
        if !self.refresh_roster_entry(&resident).await {
            // A failed pull is not proof the worker is dead: the persisted
            // identity is unreconciled, so the resident is quarantined
            // from every identity route until the live word lands (a slow
            // pull retries; the worker's own roster push or a later pull
            // clears the fence).
            resident.mark_identity_quarantined();
            self.spawn_identity_reconciliation_retry(&resident);
            self.log_line(&format!(
                "session worker {worker_id}: the registration reconciliation pull failed; the resident is quarantined from routing until the live state lands"
            ));
        }
        // The self-registered worker's session already exists: routed
        // client commands may reach it immediately.
        resident.note_session_ready();
        self.registry.insert(Arc::clone(&resident)).await;
        self.spawn_monitor(Arc::clone(&resident), None, registration.pid);
        self.log_line(&format!(
            "adopted session worker {worker_id} via self-registration"
        ));
        Ok(resident)
    }

    /// Move a registrant of another build to this build in the background
    /// (the registrant's connection ends with its exit, and that must not
    /// cancel the move). Under the adoption guard: a descriptor adoption
    /// that moved the session first leaves a resident, and this one stops.
    fn spawn_build_replacement(self: &Arc<Self>, resident: Arc<ResidentWorker>) {
        let supervisor = Arc::clone(self);
        tokio::spawn(async move {
            let worker_id = resident.worker_id.clone();
            let _guard = supervisor.registry.adoption_guard(&worker_id).await;
            if supervisor.registry.get(&worker_id).await.is_some() {
                return;
            }
            match supervisor.replace_worker_build(&resident).await {
                Ok(child) => {
                    supervisor.registry.insert(Arc::clone(&resident)).await;
                    let child_pid = child.id().unwrap_or(0);
                    supervisor.spawn_monitor(
                        Arc::clone(&resident),
                        Some(child),
                        u64::from(child_pid),
                    );
                    supervisor.refresh_roster_entry(&resident).await;
                    supervisor.log_line(&format!("session worker {worker_id} moved to this build"));
                }
                Err(error) => {
                    supervisor.log_line(&format!(
                        "session worker {worker_id} could not move to this build: {error:#}; retrying under the restart budget"
                    ));
                    supervisor.retry_failed_launch(&resident).await;
                }
            }
        });
    }

    /// A launch the supervisor could not finish (a failed revival, a failed
    /// move to this build, an unreachable live worker it stopped): the
    /// session stays resident and its monitor relaunches it with backoff.
    /// The monitor's first turn counts this failure against the restart
    /// budget, so a launch that keeps failing ends in the give-up.
    async fn retry_failed_launch(self: &Arc<Self>, resident: &Arc<ResidentWorker>) {
        if self.is_stopping(resident) {
            return;
        }
        self.registry.insert(Arc::clone(resident)).await;
        // Pid 0: no process to watch; the monitor goes straight to the
        // failure count, the backoff, and the relaunch.
        self.spawn_monitor(Arc::clone(resident), None, 0);
    }

    /// Give a live worker of another build to this build: the worker hands
    /// its session over (its work stays resumable: busy recorded, no
    /// abort, no close) and exits; then the session relaunches here (the
    /// create replay). A worker that does not know the handover, or does
    /// not exit within the stop grace, gets the identity-gated SIGTERM ->
    /// SIGKILL escalation, which also leaves its storage resumable (a
    /// worker has no signal handler: the signal ends it like a crash).
    /// Returns the relaunched worker process.
    async fn replace_worker_build(
        self: &Arc<Self>,
        resident: &Arc<ResidentWorker>,
    ) -> Result<Child> {
        let (pid, start_id) = {
            let descriptor = resident.descriptor.lock().await;
            (descriptor.pid as u32, descriptor.process_start_id.clone())
        };
        let handed_over = match self
            .connect_worker(resident, worker_connect_deadline())
            .await
        {
            Ok(()) => matches!(
                self.route_command_typed(
                    resident,
                    "worker_handover",
                    json!({}),
                    STOP_GRACE_MS,
                    RouteAdmission::Control,
                )
                .await,
                Ok(response) if response.success
            ),
            Err(_) => false,
        };
        let exited = handed_over
            && matches!(
                tokio::time::timeout(
                    Duration::from_millis(STOP_GRACE_MS),
                    eukhe_core::platform::process::wait_for_exit(pid),
                )
                .await,
                Ok(Ok(()))
            );
        if !exited {
            match crate::boot_reap::stop_process(pid, start_id.clone()).await {
                crate::boot_reap::ReapOutcome::Survived => {
                    // Each retry stops it again before its relaunch.
                    *resident.survivor.lock().await = Some((pid, start_id));
                    bail!("the worker of another build survived its stop")
                }
                crate::boot_reap::ReapOutcome::AlreadyGone
                | crate::boot_reap::ReapOutcome::Term
                | crate::boot_reap::ReapOutcome::Kill => {}
            }
        }
        self.log_line(&format!(
            "session worker {} of another build handed over (handover: {handed_over}); relaunching on this build",
            resident.worker_id
        ));
        self.relaunch_worker(resident).await
    }

    /// Record one RLM child admission: the spawn edge in the daemon-owned
    /// ledger (durable topology) and the child's display file (hydration
    /// metadata). No-op for top-level sessions.
    pub(super) async fn record_rlm_child_admission(
        self: &Arc<Self>,
        command: &DaemonCommand,
        summary: &Value,
    ) -> Result<()> {
        let DaemonCommand::Create {
            name,
            config,
            runtime_metadata,
            ..
        } = command
        else {
            return Ok(());
        };
        let Some(metadata) = runtime_metadata else {
            return Ok(());
        };
        if metadata.get("kind").and_then(Value::as_str) != Some("subagent") {
            return Ok(());
        }
        let child_id = metadata
            .get("rlmChildId")
            .and_then(Value::as_str)
            .ok_or_else(|| anyhow!("RLM child admission is missing rlmChildId"))?
            .to_string();
        let depth = metadata
            .get("rlmDepth")
            .and_then(Value::as_u64)
            .unwrap_or(1) as u32;
        let parent = metadata
            .get("parentSessionFile")
            .and_then(Value::as_str)
            .ok_or_else(|| anyhow!("RLM child admission is missing parentSessionFile"))?;
        let child = summary
            .get("sessionFile")
            .and_then(Value::as_str)
            .ok_or_else(|| anyhow!("RLM child admission is missing the child session file"))?;
        let session_name = summary
            .get("sessionName")
            .and_then(Value::as_str)
            .or(name.as_deref())
            .unwrap_or_default()
            .to_string();
        let session_dir = config
            .as_ref()
            .and_then(|config| config.get("sessionDir"))
            .and_then(Value::as_str)
            .map_or_else(
                || {
                    Path::new(child)
                        .parent()
                        .map(|dir| dir.to_string_lossy().to_string())
                        .unwrap_or_default()
                },
                str::to_string,
            );
        let ledger = self.rlm_spawn_ledger_for(None).await?;
        ledger
            .append_spawn(&crate::rlm_ledger::RlmSpawnInput {
                child_id: child_id.clone(),
                parent: parent.to_string(),
                child: child.to_string(),
                depth,
                name: session_name.clone(),
            })
            .inspect_err(|error| {
                self.log_line(&format!("failed to append RLM ledger spawn: {error:#}"));
            })?;
        let display = crate::rlm_ledger::RlmSubagentDisplayEntry {
            type_tag: "rlm_subagent".to_string(),
            child_id,
            session_name,
            session_dir,
            session_file: child.to_string(),
            rlm_parent_node_id: metadata
                .get("rlmParentNodeId")
                .and_then(Value::as_str)
                .map(str::to_string),
            prompt: metadata
                .get("prompt")
                .and_then(Value::as_str)
                .map(str::to_string),
            spawn_code: metadata
                .get("spawnCode")
                .and_then(Value::as_str)
                .map(str::to_string),
            model: metadata.get("model").cloned(),
            status: "running".to_string(),
            created_at: metadata
                .get("createdAt")
                .and_then(Value::as_u64)
                .unwrap_or_else(crate::util::now_ms),
        };
        let written =
            crate::rlm_ledger::write_rlm_subagent_display(&display).inspect_err(|error| {
                self.log_line(&format!(
                    "failed to persist RLM subagent display entry: {error:#}"
                ));
            })?;
        if !written {
            self.log_line(&format!(
                "skipped RLM subagent display entry for {}: deleted tombstone exists",
                display.child_id
            ));
        }
        Ok(())
    }
}

#[cfg(test)]
mod recorded_process_tests {
    use super::recorded_process_alive;

    #[test]
    fn unobservable_start_id_keeps_live_tombstone_owned_by_recorded_pid() {
        assert!(recorded_process_alive(Some(true), Some("original"), None));
        assert!(recorded_process_alive(None, Some("original"), None));
        assert!(recorded_process_alive(Some(true), None, None));
        assert!(recorded_process_alive(
            Some(true),
            Some("original"),
            Some("original")
        ));
        assert!(!recorded_process_alive(
            Some(true),
            Some("original"),
            Some("recycled")
        ));
        assert!(!recorded_process_alive(Some(false), Some("original"), None));
    }
}

#[cfg(test)]
mod build_tests {
    use std::sync::Arc;
    use std::time::Duration;

    use super::{DaemonCommand, Ordering, Supervisor};
    use crate::protocol::response_failure;
    use crate::supervisor::SupervisorOptions;

    /// F10: a live worker of another build that registers is not adopted.
    /// It is told to hand its session over; a registrant that cannot be
    /// reached gets the stop escalation, which leaves its storage
    /// resumable. The relaunch on this build is the existing relaunch
    /// path; here the supervisor is stopping, so no worker image runs.
    #[tokio::test]
    async fn a_registrant_of_another_build_is_not_adopted() {
        let dir = tempfile::TempDir::new().expect("temp dir");
        let socket_path = dir.path().join("daemon.sock");
        let supervisor = Arc::new(
            Supervisor::new(SupervisorOptions {
                socket_path: socket_path.clone(),
                agent_dir: dir.path().join("agent"),
            })
            .expect("supervisor"),
        );
        supervisor.pin_worker_connect_budget_for_tests(Duration::from_millis(1));
        // The registrant's process: a child of this test, so the stop
        // escalation signals nothing else.
        let mut registrant = tokio::process::Command::new("sleep")
            .arg("60")
            .kill_on_drop(true)
            .spawn()
            .expect("spawn the registrant");
        let pid = u64::from(registrant.id().expect("the registrant's pid"));
        let worker_socket = dir.path().join("w-oldbuild.sock");
        std::fs::create_dir_all(&supervisor.descriptor_dir).expect("descriptor dir");
        std::fs::write(
            supervisor.descriptor_dir.join("w-oldbuild.json"),
            serde_json::json!({
                "version": 2,
                "workerId": "w-oldbuild",
                "pid": pid,
                "socketPath": worker_socket,
                "recoveryJournalPath": dir.path().join("w-oldbuild.recovery.jsonl"),
                "supervisorSocketPath": socket_path,
                "authenticationToken": "old-token",
                "rootActiveSessionId": "w-oldbuild",
                "createdAt": "2026-10-19T00:00:00Z",
                "updatedAt": "2026-10-19T00:00:00Z",
                "lifecycle": "ready",
                "createCommand": {},
                "consecutiveFailures": 0,
            })
            .to_string(),
        )
        .expect("write the descriptor");
        let command = DaemonCommand::WorkerRegister {
            id: None,
            active_session_id: "w-oldbuild".to_string(),
            session_id: None,
            socket_path: worker_socket.to_string_lossy().to_string(),
            worker_instance_id: "inst-old".to_string(),
            token: "old-token".to_string(),
            pid,
            build_id: Some("another-build".to_string()),
            rest: serde_json::Map::default(),
        };
        let response = supervisor
            .handle_worker_register("r1", "worker_register", &command)
            .await;
        // Before the background move runs (no await since the answer):
        // the relaunch on this build is refused, so no worker image runs.
        supervisor.shutting_down.store(true, Ordering::SeqCst);
        assert_eq!(
            response,
            response_failure(
                Some("r1"),
                "worker_register",
                "Unknown session worker: w-oldbuild runs another build: its session moves to this supervisor's build; registration refused",
                None,
            )
        );
        let status = tokio::time::timeout(Duration::from_secs(30), registrant.wait())
            .await
            .expect("the registrant was stopped")
            .expect("the registrant's status");
        assert!(!status.success(), "stopped by a signal: {status:?}");
        assert!(supervisor.registry.get("w-oldbuild").await.is_none());
    }
}
