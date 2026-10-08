//! The scheduling surface (protocol breadth wave b10): the worker arms for
//! the cron/heartbeat catalog (`cron_list`, `heartbeats_list`,
//! `heartbeat_manage`, `cron_add`, `cron_cancel`, `heartbeat_get`,
//! `heartbeat_set`, `heartbeat_update` — TS daemon-mode cases over
//! `AgentCronJobStore`), the per-session artifact store they read, and the
//! scheduler that fires due jobs into the session (TS
//! `AgentCronScheduler` + `runCronJob`).
//!
//! Store: one `AgentCronJobStore::for_session_artifacts()` per worker
//! process, like TS daemon-mode (`options.worker ?
//! AgentCronJobStore.forSessionArtifacts() : ...`); sessions register
//! their artifact partition when they bind (create and every
//! replacement flow) and jobs rebind with them. A durable session's
//! "session file" is its storage directory.
//!
//! Delivery: a due job is claimed by the store and fired as an input
//! submission on the main conversation — heartbeats on their delivery-mode
//! lane (steer / follow-up) preceded by the `heartbeat_prompt` custom row
//! (TS `promptHeartbeat` / `createHeartbeatPromptMessage`), plain cron jobs
//! as a follow-up prompt (TS queues a busy session's scheduled prompt as a
//! follow-up). The submission's request id is `<kind>:<job id>:<run
//! count>`: a fire repeated after a crash (the store had not yet recorded
//! the run) dedupes onto the admitted one instead of running twice. A later
//! heartbeat fire withdraws the still-queued earlier one (the TS
//! `heartbeat:<id>` queue key). The fire settles when its submission
//! settles, so the store's run bookkeeping (`lastRunAt`/`runCount`) keeps
//! the TS record-after-run timing.

use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_durable::harness::types::WhenBusy;
use eukhe_durable::types::SubmissionStatus;
use serde_json::{json, Value};

use eukhe_core::cron::scheduler::{AgentCronScheduler, AgentCronSchedulerHooks};
use eukhe_core::cron::store::{
    AgentCronJobStore, CancelJobsFilter, CreateAgentCronJobInput, HeartbeatManagementAction,
    SessionBinding,
};
use eukhe_core::cron::{
    is_heartbeat_cron_job, normalize_heartbeat_delivery_mode, normalize_heartbeat_schedule,
    should_defer_heartbeat_cron_job, AgentCronJob, DeliveryMode, HeartbeatSessionActivity,
    JobStatus,
};
use eukhe_core::session_engine::runtime_wiring::{KernelCronBinding, KernelCronWiring};

use crate::agent_message_ingest::withdraw_queued;
use crate::protocol::{response_failure, response_success, DaemonResponse};
use crate::worker::durable_host::{meta, session_exists, storage_for_path};
use crate::worker::{submit_input, InputRequest, SessionCore, SessionSlot, Worker};

/// How long a scheduler fire waits for its submission to settle before
/// answering the scheduler with a skip (a stuck turn must not pin the
/// dispatch lane forever).
const FIRE_SETTLE_TIMEOUT_MS: u64 = 15 * 60 * 1000;

fn lock<T>(mutex: &Mutex<T>) -> std::sync::MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

/// The session-artifact directory for one session (TS
/// `getSessionArtifactPathForFile`): `<sessions>/../session-artifacts/<id>`
/// for both a storage directory `<sessions>/<id>/` and a legacy
/// `<sessions>/<id>.jsonl`.
pub(crate) fn session_artifact_dir(session_file: &Path, session_id: &str) -> Option<PathBuf> {
    session_file
        .parent()?
        .parent()
        .map(|root| root.join("session-artifacts").join(session_id))
}

/// The request-id prefix of one job's fires (`heartbeat:<id>:` or
/// `cron:<id>:`).
fn fire_request_prefix(job: &AgentCronJob) -> String {
    let kind = if is_heartbeat_cron_job(job) {
        "heartbeat"
    } else {
        "cron"
    };
    format!("{kind}:{}:", job.id)
}

/// The scheduler hooks: how a claimed job reaches this session.
pub(crate) struct QueueHooks {
    core: Arc<Mutex<SessionCore>>,
    session: SessionSlot,
    events: Arc<crate::worker::EventPump>,
    user_bash: Arc<crate::user_bash::UserBash>,
    store: Arc<AgentCronJobStore>,
}

impl QueueHooks {
    /// The session's activity snapshot (TS `shouldDeferHeartbeatCronJob`
    /// inputs): the shown conversation's run, compaction, retry, and inbox
    /// plus the bash slot.
    fn activity(&self) -> HeartbeatSessionActivity {
        let core = lock(&self.core);
        let inbox = core.view.as_ref().map_or(0, |view| view.inbox.len());
        HeartbeatSessionActivity {
            is_streaming: core.is_busy(),
            is_compacting: core.is_compacting(),
            is_retrying: core
                .view
                .as_ref()
                .is_some_and(|view| view.translator.mirror().retry_attempt.is_some()),
            is_bash_running: self.user_bash.is_running(),
            has_pending_session_work: !core.suspended.is_empty(),
            unfinished_action_count: inbox + core.suspended.len(),
        }
    }

    /// TS `isPersistedCronJobRunnable` (the persisted-job half): a
    /// persisted job may only fire at a session that still exists — its
    /// storage present, still the job's session, and (for the hosted
    /// session) not archived by a `kill`. A killed or deleted session fails
    /// the check.
    async fn persisted_target_gone(&self, job: &AgentCronJob) -> bool {
        if job.session_file.is_empty() {
            return true;
        }
        let path = Path::new(&job.session_file);
        if !session_exists(path) {
            return true;
        }
        let (session_id, dir) = storage_for_path(path);
        if session_id != job.session_id {
            return true;
        }
        let Some(hosted) = self.session.get() else {
            return false;
        };
        if hosted.storage_dir() != Some(dir.as_path()) {
            return false;
        }
        meta::read_session_meta(hosted.harness(), &BACKGROUND_CONTEXT)
            .await
            .map_or(true, |meta| meta.archived)
    }

    /// The failed-runnable cancel (TS
    /// `cancelScheduledJobsForSessionFile`): the store cancels the dead
    /// session's whole job set by file, so the artifact never re-fires.
    fn cancel_jobs_for_dead_target(&self, job: &AgentCronJob) {
        self.store.cancel_jobs_for_session(
            &CancelJobsFilter {
                active_session_id: None,
                session_id: None,
                session_file: Some(job.session_file.clone()),
            },
            crate::util::now_ms(),
        );
    }

    /// `removeQueuedHeartbeatFollowUp` (TS daemon-mode): withdraw the
    /// still-queued fires of a heartbeat job (its prompt and row).
    async fn remove_queued_heartbeat_follow_up(&self, job: &AgentCronJob) {
        if !is_heartbeat_cron_job(job) {
            return;
        }
        let Some(hosted) = self.session.get() else {
            return;
        };
        let prefix = fire_request_prefix(job);
        if let Err(error) =
            withdraw_queued(&hosted, |request_id| request_id.starts_with(&prefix)).await
        {
            eprintln!("eukhe-daemon worker: withdrawing a queued heartbeat failed: {error:#}");
        }
    }

    /// The fire's input: a heartbeat's `heartbeat_prompt` row and lane, or
    /// a plain cron job's follow-up prompt.
    fn fire_request(job: &AgentCronJob) -> InputRequest {
        let request_id = Some(format!("{}{}", fire_request_prefix(job), job.run_count));
        if !is_heartbeat_cron_job(job) {
            return InputRequest {
                text: job.prompt.clone(),
                images: Vec::new(),
                custom_row: None,
                when_busy: WhenBusy::FollowUp,
                request_id,
            };
        }
        // TS `runCronJob`: a heartbeat fire delivers through
        // `promptHeartbeat`, so the turn carries the `heartbeat_prompt`
        // custom row (TS `createHeartbeatPromptMessage`) the transcript
        // renders as the heartbeat component.
        let row = eukhe_core::session_engine::messages::create_heartbeat_prompt_message(
            job,
            crate::util::now_ms(),
        );
        InputRequest {
            text: row.content.text(),
            images: Vec::new(),
            custom_row: Some(crate::session_commands::custom_message_value(&row)),
            when_busy: if matches!(job.delivery_mode, Some(DeliveryMode::FollowUp)) {
                WhenBusy::FollowUp
            } else {
                WhenBusy::Steer
            },
            request_id,
        }
    }
}

impl AgentCronSchedulerHooks for QueueHooks {
    async fn run_job(&self, job: &AgentCronJob) -> anyhow::Result<Option<&'static str>> {
        // TS `runCronJob` -> `getOrCreateCronJobSession` ->
        // `isPersistedCronJobRunnable`: a persisted job whose target is no
        // longer live (killed or deleted) cancels the session's jobs and
        // skips, so a fire can never revive a stopped session.
        if self.persisted_target_gone(job).await {
            self.cancel_jobs_for_dead_target(job);
            return Ok(Some("skipped"));
        }
        if should_defer_heartbeat_cron_job(job, &self.activity()) {
            return Ok(Some("skipped"));
        }
        {
            let core = lock(&self.core);
            if !core.created || core.shutdown_requested || job.status != JobStatus::Active {
                return Ok(Some("skipped"));
            }
        }
        let Some(hosted) = self.session.get() else {
            return Ok(Some("skipped"));
        };
        // TS cron fires resume the suspension before admission
        // (`promptHeartbeat`/`promptUntilAccepted` carry `resumeIfIdle:
        // true`): a fire on a post-abort session is a resume site.
        crate::worker::resubmit_suspended(&hosted, &self.core, &self.events)
            .await
            .map_err(|error| anyhow::anyhow!(error))?;
        // The TS `heartbeat:<id>` queue key: a later fire replaces the
        // queued one instead of stacking.
        self.remove_queued_heartbeat_follow_up(job).await;
        let request = Self::fire_request(job);
        let handle = submit_input(&hosted.main()?, &request, &BACKGROUND_CONTEXT).await?;
        // A queued heartbeat fire is an injected prompt: the queue
        // strip's `injectedPrompts` rider marks it while it parks.
        if let Some(kind) = crate::worker::injection_kind(request.custom_row.as_ref()) {
            self.core
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .injected
                .insert(handle.id(), kind);
        }
        match tokio::time::timeout(
            std::time::Duration::from_millis(FIRE_SETTLE_TIMEOUT_MS),
            handle.wait(&BACKGROUND_CONTEXT),
        )
        .await
        {
            // An answered fire is a run (a failed or aborted turn still
            // answered it: TS `promptHeartbeat` resolves normally); a fire
            // withdrawn before delivery (abort, a queue edit, a later fire
            // replacing it) is the TS unrunnable-at-admission skip.
            Ok(Ok(settled)) => match settled.record().state.status() {
                SubmissionStatus::Done => Ok(None),
                SubmissionStatus::Unanswered
                | SubmissionStatus::Queued
                | SubmissionStatus::Placed => Ok(Some("skipped")),
            },
            // The session closed under the wait: the admitted fire is
            // durable and runs when the session resumes.
            Ok(Err(_)) => Ok(None),
            // The settle window expired: the fire did not run.
            Err(_) => Ok(Some("skipped")),
        }
    }
}

/// The worker's schedule catalog: the shared artifact store plus the
/// scheduler (started when the first session binds).
pub(crate) struct ScheduledJobs {
    store: Arc<AgentCronJobStore>,
    hooks: Arc<QueueHooks>,
    scheduler: tokio::sync::Mutex<Option<Arc<AgentCronScheduler<QueueHooks>>>>,
}

impl ScheduledJobs {
    pub(crate) fn new(
        core: Arc<Mutex<SessionCore>>,
        session: SessionSlot,
        user_bash: Arc<crate::user_bash::UserBash>,
        events: Arc<crate::worker::EventPump>,
    ) -> Self {
        let mut store = AgentCronJobStore::for_session_artifacts();
        // TS daemon-mode's `cronStore.onHeartbeatChange` →
        // `broadcastGlobal({ type: "heartbeats_changed" })`: any heartbeat
        // catalog change (user set/manage, agent `rlm_heartbeat` CRUD, a
        // fire's bookkeeping) broadcasts to the clients and the supervisor
        // re-broadcasts daemon-wide.
        let change_events = Arc::clone(&events);
        store.on_heartbeat_change(Box::new(move || {
            change_events.send(crate::worker::OutboundFrame::heartbeats_changed());
        }));
        let store = Arc::new(store);
        ScheduledJobs {
            hooks: Arc::new(QueueHooks {
                core,
                session,
                events,
                user_bash,
                store: Arc::clone(&store),
            }),
            store,
            scheduler: tokio::sync::Mutex::new(None),
        }
    }

    pub(crate) fn store(&self) -> &Arc<AgentCronJobStore> {
        &self.store
    }

    /// Bind the live session (TS `rebindCronJobsToState`): register the
    /// session's artifact partition, move its stored jobs onto the live
    /// ids, and start (or wake) the scheduler.
    pub(crate) async fn bind_session(
        &self,
        binding: SessionBinding,
        artifact_dir: Option<PathBuf>,
    ) {
        if let Some(dir) = artifact_dir {
            if let Err(error) = std::fs::create_dir_all(&dir) {
                eprintln!(
                    "eukhe-daemon worker: creating the session artifact dir {} failed: {error}",
                    dir.display()
                );
            }
            self.store
                .register_session_artifact(&binding.session_id, &dir);
        }
        if !binding.session_file.is_empty() {
            self.store.rebind_session_jobs(&binding);
        }
        let mut guard = self.scheduler.lock().await;
        if let Some(scheduler) = guard.as_ref() {
            scheduler.wake().await;
            return;
        }
        let scheduler = Arc::new(AgentCronScheduler::new(
            Arc::clone(&self.store),
            Arc::clone(&self.hooks),
        ));
        scheduler.start().await;
        *guard = Some(scheduler);
    }

    /// Re-arm the timer after a catalog mutation (TS `cronScheduler.wake`).
    pub(crate) async fn wake(&self) {
        let guard = self.scheduler.lock().await;
        if let Some(scheduler) = guard.as_ref() {
            scheduler.wake().await;
        }
    }

    /// The kernel rlm heartbeat mutation hook (TS daemon-mode's
    /// controller post-mutation work: `removeQueuedHeartbeatFollowUp`
    /// where the mutation withdraws the queued fire, then
    /// `cronScheduler.wake()`): carried by the session's kernel cron
    /// wiring, invoked by the `rlm_heartbeat.*` host handlers after every
    /// create/update/delete. Without the wake the bind-time arm — taken
    /// over an empty store — leaves no timer, and a heartbeat created
    /// afterwards never fires.
    pub(crate) fn mutation_hook(
        self: &Arc<Self>,
    ) -> eukhe_core::session_engine::host_requests::RlmHeartbeatMutationHook {
        let scheduled = Arc::clone(self);
        Arc::new(move |mutation| {
            let scheduled = Arc::clone(&scheduled);
            Box::pin(async move {
                if mutation.drop_queued {
                    scheduled
                        .remove_queued_heartbeat_follow_up(&mutation.job)
                        .await;
                }
                scheduled.wake().await;
            })
        })
    }

    /// `removeQueuedHeartbeatFollowUp` (TS daemon-mode): withdraw the
    /// queued fire of a heartbeat job from the session's inbox.
    pub(crate) async fn remove_queued_heartbeat_follow_up(&self, job: &AgentCronJob) {
        self.hooks.remove_queued_heartbeat_follow_up(job).await;
    }
}

/// The bind inputs of one live session (TS `SessionBinding` plus the
/// session's artifact partition): `None` for in-memory sessions.
pub(crate) fn live_binding(core: &SessionCore) -> Option<(SessionBinding, Option<PathBuf>)> {
    let dir = core.session_dir.as_ref()?;
    Some((
        SessionBinding {
            active_session_id: core.active_session_id.clone(),
            session_id: core.session_id.clone(),
            session_file: dir.to_string_lossy().into_owned(),
            cwd: core.cwd.clone(),
        },
        session_artifact_dir(dir, &core.session_id),
    ))
}

impl Worker {
    /// The kernel cron wiring of a session this worker opens (TS
    /// daemon-mode wires its `AgentCronJobStore.forSessionArtifacts()` into
    /// the session runtime): the shared store, the live/durable identity
    /// kernel-created heartbeats bind to, and the mutation hook.
    pub(crate) fn kernel_cron_wiring(
        &self,
        session_id: &str,
        storage_dir: Option<&Path>,
        cwd: &str,
    ) -> KernelCronWiring {
        let active_session_id = lock(&self.core).active_session_id.clone();
        KernelCronWiring {
            store: Arc::clone(self.scheduled.store()),
            binding: Some(KernelCronBinding {
                active_session_id,
                session_id: session_id.to_owned(),
                session_file: storage_dir
                    .map(|dir| dir.to_string_lossy().into_owned())
                    .unwrap_or_default(),
                cwd: cwd.to_owned(),
            }),
            mutation_hook: Some(self.scheduled.mutation_hook()),
        }
    }

    /// Register the live session's artifact partition on the store
    /// (idempotent) so catalog reads see this session's jobs.
    fn bind_store_artifact(&self, core: &SessionCore) {
        let Some(dir) = core.session_dir.as_ref() else {
            return;
        };
        if let Some(artifacts) = session_artifact_dir(dir, &core.session_id) {
            self.scheduled
                .store()
                .register_session_artifact(&core.session_id, &artifacts);
        }
    }

    /// TS `cancelScheduledJobsForSession(state)` (the killed close's
    /// schedule cancel): the session's whole job set cancels (matched by
    /// any of the session's three identities, exactly the TS filter), each
    /// cancelled heartbeat's queued fire withdraws
    /// (`removeQueuedHeartbeatFollowUp`), and the scheduler re-arms. The
    /// cancel is durable, so the stopped session's own heartbeats can
    /// never revive it.
    pub(crate) async fn cancel_session_scheduled_jobs(&self) {
        let (active_session_id, session_id, session_file) = {
            let core = lock(&self.core);
            self.bind_store_artifact(&core);
            let Some(session_file) = core.session_file() else {
                return;
            };
            (
                core.active_session_id.clone(),
                core.session_id.clone(),
                session_file,
            )
        };
        let cancelled = self.scheduled.store().cancel_jobs_for_session(
            &CancelJobsFilter {
                active_session_id: Some(active_session_id),
                session_id: Some(session_id),
                session_file: Some(session_file),
            },
            crate::util::now_ms(),
        );
        for job in &cancelled {
            self.scheduled.remove_queued_heartbeat_follow_up(job).await;
        }
        if !cancelled.is_empty() {
            self.scheduled.wake().await;
        }
    }

    /// TS `cancelSubagentRlmHeartbeats(state)` (the replaced close of a
    /// subagent): only the subagent's RLM heartbeat jobs cancel; the plain
    /// cron jobs survive the replacement. A top-level session cancels
    /// nothing here (the TS `kind !== "subagent"` gate).
    pub(crate) async fn cancel_session_rlm_heartbeats(&self) {
        let (is_subagent, active_session_id) = {
            let core = lock(&self.core);
            self.bind_store_artifact(&core);
            (
                core.runtime_kind == "subagent",
                core.active_session_id.clone(),
            )
        };
        if !is_subagent {
            return;
        }
        let cancelled = self
            .scheduled
            .store()
            .cancel_rlm_heartbeats_for_session(&active_session_id, crate::util::now_ms());
        for job in &cancelled {
            self.scheduled.remove_queued_heartbeat_follow_up(job).await;
        }
        if !cancelled.is_empty() {
            self.scheduled.wake().await;
        }
    }

    /// TS `cancelScheduledJobsForSessionFile` (the saved-session delete's
    /// `afterFileRemoved` hook): register the deleted session's artifact
    /// partition (only when its store file exists) and cancel its whole
    /// job set by path, so the jobs die with the delete even if the
    /// partition removal fails. The hook runs once the storage is gone, so
    /// the partition derives from the path (`<id>/` or `<id>.jsonl`), not
    /// from a session read. Best-effort: the deletion never fails on a
    /// store error (the TS hook's failures are logged, not thrown).
    pub(crate) fn cancel_deleted_session_jobs(&self, session_file: &Path) {
        let (session_id, _) = storage_for_path(session_file);
        if session_id.is_empty() {
            return;
        }
        let Some(dir) = session_artifact_dir(session_file, &session_id) else {
            return;
        };
        if !dir
            .join(eukhe_core::cron::store::SESSION_SCHEDULED_JOBS_FILENAME)
            .is_file()
        {
            return;
        }
        self.scheduled
            .store()
            .register_session_artifact(&session_id, &dir);
        self.scheduled.store().cancel_jobs_for_session(
            &CancelJobsFilter {
                active_session_id: None,
                session_id: None,
                session_file: Some(session_file.to_string_lossy().to_string()),
            },
            crate::util::now_ms(),
        );
    }
}

// The nine scheduling protocol arms (cron_list, heartbeats_list, heartbeat_manage,
// cron_add, cron_cancel, heartbeat_get, heartbeat_set, heartbeat_update) live in
// the child module (scheduled_jobs::arms) as the same inherent impl Worker block -
// every arm keeps its pub(crate) level, so the command dispatcher and the tests
// resolve them through the type, ZERO path churn.
mod arms;

// The inline unit battery lives in the child module (scheduled_jobs::tests);
// its use-super glob resolves through this facade's bindings.
#[cfg(test)]
mod tests;
