//! The cron scheduler: wake-timer loop, claim-due dispatch, per-session
//! dispatch lanes. Port of the `AgentCronScheduler` half of core/cron-jobs.ts.
//!
//! Deviation from TS, documented: a failing job backs off and then stops.
//! TS re-fires a job at its full cadence no matter how many consecutive
//! fires fail (a dead model route re-fires every tick until the job is
//! cancelled). Here the store's finish step
//! ([`AgentCronJobStore::record_dispatch_result`]) counts the failures in
//! a row on the job, stretches the next run past the schedule (2m, 4m, up
//! to 1h), and pauses the job after 8 of them (the compiled core decides:
//! `bend/cron_store.bend` `finish`, the model's `CAP`). A good run resets
//! the count. A skipped fire (busy session, deferral) neither
//! extends nor resets it.
//!
//! Every pass first recovers interrupted claims: its own claims whose run
//! is no longer live, and the claims of dead processes. The live claim of
//! another process sharing the jobs file is never cleared.

use std::collections::HashMap;
use std::future::Future;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use tokio::sync::{Mutex, Notify};

use super::store::{
    AgentCronDispatch, AgentCronJobStore, DispatchOutcome, DispatchResultOptions, RunningDispatch,
};

const MAX_TIMEOUT_MS: u64 = 2_147_483_647;

/// A claimed dispatch paired with its optional settle callback.
type PendingDispatch = (RunningDispatch, Option<Box<dyn FnOnce() + Send>>);

/// Scheduler hooks: how claimed jobs actually run.
pub trait AgentCronSchedulerHooks: Send + Sync {
    /// Run one claimed job; return `Some("skipped")` to record a skip.
    fn run_job(
        &self,
        job: &super::AgentCronJob,
    ) -> impl Future<Output = anyhow::Result<Option<&'static str>>> + Send;
    /// Observe a dispatch being handed to a lane; the returned closure is
    /// invoked when the lane's work settles (even on errors).
    fn begin_dispatch(&self, _dispatch: &AgentCronDispatch) -> Option<Box<dyn FnOnce() + Send>> {
        None
    }
    fn now(&self) -> u64 {
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|duration| duration.as_millis() as u64)
            .unwrap_or_default()
    }
    fn on_error(&self, _job: &super::AgentCronJob, _error: &str) {}
}

pub struct AgentCronScheduler<H: AgentCronSchedulerHooks> {
    core: Arc<SchedulerCore<H>>,
    timer: Mutex<Option<tokio::task::JoinHandle<()>>>,
}

/// State shared with the timer task.
pub struct SchedulerCore<H: AgentCronSchedulerHooks> {
    store: Arc<AgentCronJobStore>,
    hooks: Arc<H>,
    running: AtomicBool,
    stopped: AtomicBool,
    has_started: AtomicBool,
    dispatch_lanes: Mutex<HashMap<String, Arc<Mutex<()>>>>,
    wake: Notify,
}

impl<H: AgentCronSchedulerHooks + 'static> AgentCronScheduler<H> {
    pub fn new(store: Arc<AgentCronJobStore>, hooks: Arc<H>) -> Self {
        Self {
            core: Arc::new(SchedulerCore {
                store,
                hooks,
                running: AtomicBool::new(false),
                stopped: AtomicBool::new(true),
                has_started: AtomicBool::new(false),
                dispatch_lanes: Mutex::new(HashMap::new()),
                wake: Notify::new(),
            }),
            timer: Mutex::new(None),
        }
    }

    /// Start the scheduler; recovers interrupted dispatches on first start.
    pub async fn start(&self) {
        self.core.stopped.store(false, Ordering::SeqCst);
        if !self.core.has_started.swap(true, Ordering::SeqCst) {
            let now = self.core.hooks.now();
            if let Err(error) = self.core.store.recover_interrupted_dispatches(now) {
                tracing::warn!(%error, "cron recovery failed at start");
            }
        }
        self.schedule_next().await;
    }

    /// Stop the timer loop.
    pub async fn stop(&self) {
        self.core.stopped.store(true, Ordering::SeqCst);
        if let Some(handle) = self.timer.lock().await.take() {
            handle.abort();
        }
    }

    /// Re-evaluate the next wake time immediately.
    pub async fn wake(&self) {
        if self.core.stopped.load(Ordering::SeqCst) {
            return;
        }
        self.core.wake.notify_waiters();
        self.schedule_next().await;
    }

    /// Claim all due jobs and dispatch them. Returns how many ran.
    ///
    /// # Errors
    ///
    /// Returns an error when a cron state lock or write fails.
    pub async fn run_due(&self) -> anyhow::Result<usize> {
        self.core.run_due_at(self.core.hooks.now()).await
    }
}

/// Panic-safe reset for the scheduler's run-pass flag: cleared on drop
/// however the pass unwinds.
struct RunningGuard<'a>(&'a AtomicBool);

impl Drop for RunningGuard<'_> {
    fn drop(&mut self) {
        self.0.store(false, Ordering::SeqCst);
    }
}

impl<H: AgentCronSchedulerHooks + 'static> SchedulerCore<H> {
    /// Run one dispatch pass for jobs due at or before `now`, returning how
    /// many dispatches ran. Returns `Ok(0)` without dispatching when the
    /// scheduler is stopped or another pass is already running.
    ///
    /// # Errors
    ///
    /// Returns an error when a cron state lock or write fails.
    pub async fn run_due_at(&self, now: u64) -> anyhow::Result<usize> {
        // The pass claim is atomic: exactly one pass runs at a time (a
        // concurrent caller returns before touching another pass's
        // dispatches).
        if (self.stopped.load(Ordering::SeqCst) && self.has_started.load(Ordering::SeqCst))
            || self
                .running
                .compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst)
                .is_err()
        {
            return Ok(0);
        }
        // Panic safety: a claim/dispatch that unwinds must not wedge the
        // re-entrancy flag at `true` — that would silence every later
        // pass while the timer keeps spinning. The guard resets it on
        // the way out however the pass ends.
        let _running = RunningGuard(&self.running);
        // Recover interrupted dispatches before claiming: a claim this
        // process left on record (an unwound pass dropped its running
        // dispatch) or a dead process's claim is released here, so its
        // job's next occurrence claims and fires. A live claim stays.
        self.store.recover_interrupted_dispatches(now)?;
        let claimed = self.store.claim_due(now, self.hooks.now())?;
        let dispatches: Vec<PendingDispatch> = claimed
            .into_iter()
            .map(|running| {
                let end_dispatch = self.hooks.begin_dispatch(running.dispatch());
                (running, end_dispatch)
            })
            .collect();
        let ran = self.dispatch_all(dispatches).await;
        Ok(ran)
    }

    async fn dispatch_all(&self, dispatches: Vec<PendingDispatch>) -> usize {
        let mut handles = Vec::new();
        for (dispatch, end_dispatch) in dispatches {
            handles.push(self.queue_dispatch(dispatch, end_dispatch));
        }
        let results = futures::future::join_all(handles).await;
        results
            .into_iter()
            .filter(|result| *result != Some("skipped"))
            .count()
    }

    async fn queue_dispatch(
        &self,
        running: RunningDispatch,
        end_dispatch: Option<Box<dyn FnOnce() + Send>>,
    ) -> Option<&'static str> {
        let lane_key = running.dispatch().job.active_session_id.clone();
        let lane = {
            let mut lanes = self.dispatch_lanes.lock().await;
            lanes
                .entry(lane_key.clone())
                .or_insert_with(|| Arc::new(Mutex::new(())))
                .clone()
        };
        // Serialize per-session dispatches: the lane lock queues this run
        // behind any in-flight work for the same session.
        let _guard = lane.lock().await;
        let result = self.run_dispatch(running, end_dispatch).await;
        let mut lanes = self.dispatch_lanes.lock().await;
        lanes.remove(&lane_key);
        result
    }

    /// Run one claimed dispatch and record its result. The running dispatch
    /// drops at the end, after the result is on record.
    async fn run_dispatch(
        &self,
        running: RunningDispatch,
        end_dispatch: Option<Box<dyn FnOnce() + Send>>,
    ) -> Option<&'static str> {
        let dispatch: &AgentCronDispatch = running.dispatch();
        let outcome = async {
            let Some(job) = self.store.get_claimed_job(&dispatch.job.id) else {
                if let Err(error) = self.store.record_dispatch_result(
                    &dispatch.id,
                    &DispatchResultOptions {
                        now: Some(self.hooks.now()),
                        outcome: DispatchOutcome::Skipped,
                        error: None,
                    },
                ) {
                    tracing::warn!(%error, "cron dispatch result not saved");
                }
                return Some("skipped");
            };
            let mut run_error: Option<String> = None;
            let run_result = match self.hooks.run_job(&job).await {
                Ok(result) => result,
                Err(error) => {
                    let message = error.to_string();
                    self.hooks.on_error(&job, &message);
                    run_error = Some(message);
                    None
                }
            };
            let outcome = if run_result == Some("skipped") && run_error.is_none() {
                DispatchOutcome::Skipped
            } else {
                DispatchOutcome::Ran
            };
            if let Err(error) = self.store.record_dispatch_result(
                &dispatch.id,
                &DispatchResultOptions {
                    now: Some(self.hooks.now()),
                    outcome,
                    error: run_error,
                },
            ) {
                tracing::warn!(%error, "cron dispatch result not saved");
            }
            run_result
        }
        .await;
        drop(running);
        if let Some(end) = end_dispatch {
            end();
        }
        outcome
    }
}

impl<H: AgentCronSchedulerHooks + 'static> AgentCronScheduler<H> {
    /// (Re)start the wake timer to the next active run.
    ///
    /// The timer task parks on the wake notify while the store has no
    /// active runs instead of exiting, so a catalog mutation's wake can
    /// always re-arm it (the TS `recomputeScheduledSessionWake` shape:
    /// every recompute arms a fresh timer). An exited task would leave
    /// the notify with no waiter, and later wakes would reach nobody.
    async fn schedule_next(&self) {
        let mut timer = self.timer.lock().await;
        // A live task is never aborted: the parked loop re-evaluates at
        // its head on the notify, so a wake landing mid-pass needs no
        // respawn. Only a dead task spawns a replacement; the explicit
        // `stop` abort stays (the next `start` recovers the interrupted
        // dispatches).
        if let Some(previous) = timer.as_ref() {
            if !previous.is_finished() {
                self.core.wake.notify_waiters();
                return;
            }
        }
        timer.take();
        let core = self.core.clone();
        let handle = tokio::spawn(async move {
            loop {
                // The wake is registered before the store read (the
                // enabled future holds the waiter slot), so a notify
                // landing between the read and the wait is captured —
                // by the park or by the delay select, whichever the read
                // selects.
                let notified = core.wake.notified();
                tokio::pin!(notified);
                notified.as_mut().enable();
                let Some(next) = core.store.next_active_run_at() else {
                    // Nothing to fire: park until a mutation re-arms
                    // (an explicit stop is the only exit).
                    if core.stopped.load(Ordering::SeqCst) {
                        return;
                    }
                    notified.await;
                    continue;
                };
                let now = core.hooks.now();
                let delay = tokio::time::Duration::from_millis(
                    next.saturating_sub(now).clamp(1, MAX_TIMEOUT_MS),
                );
                tokio::select! {
                    () = tokio::time::sleep(delay) => {}
                    () = &mut notified => continue,
                }
                if core.stopped.load(Ordering::SeqCst) {
                    return;
                }
                // Fire the due batch and reschedule for the following run.
                core.run_due_at(core.hooks.now()).await.ok();
            }
        });
        timer.replace(handle);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cron::store::CreateAgentCronJobInput;
    use crate::cron::{AgentCronJob, ScheduleKind};
    use std::sync::atomic::AtomicUsize;

    struct CountingHooks {
        runs: Arc<AtomicUsize>,
        outcomes: Mutex<Vec<&'static str>>,
    }

    impl AgentCronSchedulerHooks for CountingHooks {
        async fn run_job(&self, _job: &AgentCronJob) -> anyhow::Result<Option<&'static str>> {
            self.runs.fetch_add(1, Ordering::SeqCst);
            let outcome = *self.outcomes.lock().await.last().unwrap_or(&"ran");
            Ok(Some(outcome))
        }
        fn now(&self) -> u64 {
            1_700_000_000_000
        }
    }

    fn input(prompt: &str, schedule_text: &str, now: u64) -> CreateAgentCronJobInput {
        CreateAgentCronJobInput {
            active_session_id: "live-1".to_string(),
            session_id: "session-1".to_string(),
            session_file: "/w/session.jsonl".to_string(),
            cwd: "/w".to_string(),
            prompt: prompt.to_string(),
            schedule_text: schedule_text.to_string(),
            now: Some(now),
            ..Default::default()
        }
    }

    /// The re-arm regression behind the dogfood P0 (a heartbeat created
    /// after the bind-time arm never fires): starting on an empty store
    /// arms no timer (`schedule_next` returns without one), so the
    /// mutation's wake — TS `cronScheduler.wake()` — must re-arm and fire
    /// the job created afterwards.
    #[tokio::test]
    async fn wake_rearms_a_timer_for_a_job_created_after_start() {
        let dir = tempfile::TempDir::new().unwrap();
        let store = Arc::new(AgentCronJobStore::new(dir.path().join("jobs.json")));
        let now = 1_700_000_000_000;
        let runs = Arc::new(AtomicUsize::new(0));
        let hooks = Arc::new(CountingHooks {
            runs: runs.clone(),
            outcomes: Mutex::new(vec!["ran"]),
        });
        let scheduler = AgentCronScheduler::new(store.clone(), hooks);
        // Empty store: the bind-time arm leaves no timer running.
        scheduler.start().await;
        // A later mutation's job (created already-due on the fixed test
        // clock, like the sibling tests' "in 1m" inputs, so the re-armed
        // timer fires within milliseconds).
        store
            .create(&input("tick", "in 1m", now - 61_000))
            .expect("create job");
        // The mutation's wake re-arms; the timer fires within milliseconds.
        scheduler.wake().await;
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(5);
        while runs.load(Ordering::SeqCst) == 0 && std::time::Instant::now() < deadline {
            tokio::time::sleep(std::time::Duration::from_millis(10)).await;
        }
        assert!(
            runs.load(Ordering::SeqCst) >= 1,
            "the woken timer never fired"
        );
        scheduler.stop().await;
    }

    /// The frozen-heartbeat re-adoption incident's structural guard: a
    /// dispatch that panics must not wedge the run-pass re-entrancy flag
    /// at `true` — that silently no-ops every later pass while the timer
    /// keeps firing (a job rows as active with a stale `nextRunAt` and
    /// `runCount` 0 forever, exactly the governance session's frozen
    /// `*/2` heartbeat after its supervisor restart re-adoption).
    #[tokio::test]
    async fn a_panicking_dispatch_does_not_wedge_the_run_pass() {
        struct PanickingHooks {
            runs: Arc<AtomicUsize>,
            panic_first: AtomicBool,
        }
        impl AgentCronSchedulerHooks for PanickingHooks {
            fn run_job(
                &self,
                _job: &AgentCronJob,
            ) -> impl Future<Output = anyhow::Result<Option<&'static str>>> {
                self.runs.fetch_add(1, Ordering::SeqCst);
                assert!(
                    !self.panic_first.swap(false, Ordering::SeqCst),
                    "the first dispatch unwinds"
                );
                std::future::ready(Ok(Some("ran")))
            }
            fn now(&self) -> u64 {
                1_700_000_000_000
            }
        }
        let dir = tempfile::TempDir::new().unwrap();
        let store = Arc::new(AgentCronJobStore::new(dir.path().join("jobs.json")));
        let now = 1_700_000_000_000;
        // Created 10m ago on the fixed test clock: due immediately (a
        // job created at `now` would sit 10m out and never dispatch).
        store
            .create(&input("tick", "every 10m", now - 600_000))
            .unwrap();
        let hooks = Arc::new(PanickingHooks {
            runs: Arc::new(AtomicUsize::new(0)),
            panic_first: AtomicBool::new(true),
        });
        // No start(): the passes below drive `run_due` directly (a
        // started timer would race the manual passes for the same due
        // job — the timer task would claim the first dispatch, and the
        // manual pass would find nothing due).
        let scheduler = Arc::new(AgentCronScheduler::new(store.clone(), hooks.clone()));
        // The first pass panics inside its spawned task (the flag must
        // not stay wedged).
        let first = tokio::time::timeout(
            std::time::Duration::from_secs(5),
            tokio::spawn({
                let scheduler = Arc::clone(&scheduler);
                async move { scheduler.run_due().await }
            }),
        )
        .await
        // The timeout layer unwraps; the panic surfaces as the join
        // error underneath it.
        .expect("first pass settles");
        assert!(first.is_err(), "the panicking pass surfaced: {first:?}");
        // A second job becomes due; the pass must still claim and run it
        // (a wedged flag would silently skip forever).
        store
            .create(&input("tock", "every 10m", now - 600_000))
            .expect("second job");
        let ran = tokio::time::timeout(
            std::time::Duration::from_secs(5),
            tokio::spawn({
                let scheduler = Arc::clone(&scheduler);
                async move { scheduler.run_due().await }
            }),
        )
        .await
        .expect("second pass settles")
        .expect("second pass joined")
        .expect("second pass ran");
        assert!(ran > 0, "the wedged flag skipped the second pass: {ran}");
        scheduler.stop().await;
    }

    /// THE LIVE INCIDENT'S EXACT SHAPE: a catalog mutation whose wake
    /// lands while a fire pass is in-flight must not strand or wedge
    /// the schedule. The pre-fix abort canceled the future at its await
    /// without running the pass's tail, so the claimed dispatch stayed
    /// interrupted and every later pass marked the job skipped instead
    /// of retrying (the governance session's beats froze exactly here:
    /// the job was re-created from inside a running beat). The live
    /// task now consumes the wake at its loop head, and a pass-head
    /// recovery un-sticks any interrupted claim.
    #[tokio::test]
    async fn a_mutation_wake_during_an_in_flight_pass_does_not_wedge_the_flag() {
        struct BlockingHooks {
            runs: Arc<AtomicUsize>,
            block_first: AtomicBool,
        }
        impl AgentCronSchedulerHooks for BlockingHooks {
            async fn run_job(&self, _job: &AgentCronJob) -> anyhow::Result<Option<&'static str>> {
                self.runs.fetch_add(1, Ordering::SeqCst);
                if self.block_first.swap(false, Ordering::SeqCst) {
                    // The delivery holds (the fire's settle wait is
                    // bounded in the real hooks): the pass is still
                    // in-flight when the mutation's wake lands.
                    tokio::time::sleep(std::time::Duration::from_millis(200)).await;
                }
                Ok(Some("ran"))
            }
            fn now(&self) -> u64 {
                1_700_000_000_000
            }
        }
        let dir = tempfile::TempDir::new().unwrap();
        let store = Arc::new(AgentCronJobStore::new(dir.path().join("jobs.json")));
        let now = 1_700_000_000_000;
        let hooks = Arc::new(BlockingHooks {
            runs: Arc::new(AtomicUsize::new(0)),
            block_first: AtomicBool::new(true),
        });
        let scheduler = AgentCronScheduler::new(store.clone(), hooks.clone());
        // The job is created already-due: the timer fires immediately on
        // start. The pass parks inside its first delivery.
        store
            .create(&input("tick", "in 1m", now - 61_000))
            .expect("first job");
        scheduler.start().await;
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(5);
        while hooks.runs.load(Ordering::SeqCst) == 0 && std::time::Instant::now() < deadline {
            tokio::time::sleep(std::time::Duration::from_millis(10)).await;
        }
        assert_eq!(
            hooks.runs.load(Ordering::SeqCst),
            1,
            "the first fire started"
        );
        // A catalog mutation from inside the running beat: its wake
        // aborts the timer task MID-PASS.
        store
            .create(&input("tock", "in 1m", now - 61_000))
            .expect("second job");
        scheduler.wake().await;
        // The aborted pass's flag must not wedge: a fresh wake re-arms
        // the timer and the second job's due pass must claim and run.
        scheduler.wake().await;
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(5);
        while hooks.runs.load(Ordering::SeqCst) < 2 && std::time::Instant::now() < deadline {
            tokio::time::sleep(std::time::Duration::from_millis(10)).await;
        }
        assert!(
            hooks.runs.load(Ordering::SeqCst) >= 2,
            "a wedged flag silently skipped every later pass (runs: {})",
            hooks.runs.load(Ordering::SeqCst)
        );
        scheduler.stop().await;
    }

    /// The timer task parks on an empty store instead of dying: the store
    /// emptying mid-life (every job cancelled or completed) must leave a
    /// parked timer a later mutation wake re-arms — the mid-life death
    /// behind a re-adopted worker whose session never receives a due
    /// fire again.
    #[tokio::test]
    async fn the_timer_parks_on_an_empty_store_and_re_arms_on_wake() {
        let dir = tempfile::TempDir::new().unwrap();
        let store = Arc::new(AgentCronJobStore::new(dir.path().join("jobs.json")));
        let now = 1_700_000_000_000;
        let runs = Arc::new(AtomicUsize::new(0));
        let hooks = Arc::new(CountingHooks {
            runs: runs.clone(),
            outcomes: Mutex::new(vec!["ran"]),
        });
        let scheduler = AgentCronScheduler::new(store.clone(), hooks);
        scheduler.start().await;
        // The store empties mid-life: the only job is cancelled.
        let job = store
            .create(&input("tick", "every 10m", now))
            .expect("first job");
        store
            .cancel(&job.id, now)
            .unwrap()
            .expect("cancel the only job");
        // The parked timer survives the empty era; a later mutation's
        // job + wake must fire.
        let deadline = std::time::Instant::now() + std::time::Duration::from_millis(300);
        while std::time::Instant::now() < deadline {
            tokio::time::sleep(std::time::Duration::from_millis(10)).await;
        }
        store
            .create(&input("tock", "in 1m", now - 61_000))
            .expect("later job");
        scheduler.wake().await;
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(5);
        while runs.load(Ordering::SeqCst) == 0 && std::time::Instant::now() < deadline {
            tokio::time::sleep(std::time::Duration::from_millis(10)).await;
        }
        assert!(
            runs.load(Ordering::SeqCst) >= 1,
            "the parked timer never fired the later job"
        );
        scheduler.stop().await;
    }

    #[tokio::test]
    async fn claims_and_runs_due_jobs() {
        let dir = tempfile::TempDir::new().unwrap();
        let store = Arc::new(AgentCronJobStore::new(dir.path().join("jobs.json")));
        let now = 1_700_000_000_000;
        store.create(&input("tick", "every 10m", now)).unwrap();
        let runs = Arc::new(AtomicUsize::new(0));
        let hooks = Arc::new(CountingHooks {
            runs: runs.clone(),
            outcomes: Mutex::new(vec!["ran"]),
        });
        let scheduler = AgentCronScheduler::new(store.clone(), hooks);
        scheduler.start().await;
        // Not due yet: nothing runs.
        let ran = scheduler.run_due().await.unwrap();
        assert_eq!(ran, 0);
        assert_eq!(runs.load(Ordering::SeqCst), 0);
        // Due later (hooks.now() is fixed; the job fires every 10m).
        store
            .create(&input("tick2", "in 1m", now - 61_000))
            .unwrap();
        let ran = scheduler.run_due().await.unwrap();
        assert!(ran >= 1);
        assert_eq!(runs.load(Ordering::SeqCst), 1);
        scheduler.stop().await;
    }

    #[tokio::test]
    async fn skip_outcomes_are_recorded() {
        let dir = tempfile::TempDir::new().unwrap();
        let store = Arc::new(AgentCronJobStore::new(dir.path().join("jobs.json")));
        let now = 1_700_000_000_000;
        store.create(&input("tick", "in 1m", now - 60_000)).unwrap();
        let runs = Arc::new(AtomicUsize::new(0));
        let hooks = Arc::new(CountingHooks {
            runs: runs.clone(),
            outcomes: Mutex::new(vec!["skipped"]),
        });
        let scheduler = AgentCronScheduler::new(store.clone(), hooks);
        scheduler.start().await;
        let ran = scheduler.run_due().await.unwrap();
        // The skip still claimed the job, so zero runs are counted.
        assert_eq!(ran, 0);
        assert_eq!(runs.load(Ordering::SeqCst), 1);
        let jobs = store.list();
        assert_eq!(jobs[0].status, crate::cron::JobStatus::Completed);
        assert!(jobs[0].last_skipped_at.is_some());
        scheduler.stop().await;
    }

    #[tokio::test]
    async fn lane_serializes_same_session_dispatches() {
        let dir = tempfile::TempDir::new().unwrap();
        let store = Arc::new(AgentCronJobStore::new(dir.path().join("jobs.json")));
        let now = 1_700_000_000_000;
        store.create(&input("a", "in 1m", now - 60_000)).unwrap();
        store.create(&input("b", "in 1m", now - 60_000)).unwrap();
        let runs = Arc::new(AtomicUsize::new(0));
        let hooks = Arc::new(CountingHooks {
            runs: runs.clone(),
            outcomes: Mutex::new(vec!["ran"]),
        });
        let scheduler = AgentCronScheduler::new(store, hooks);
        scheduler.start().await;
        let ran = scheduler.run_due().await.unwrap();
        assert_eq!(ran, 2);
        assert_eq!(runs.load(Ordering::SeqCst), 2);
        scheduler.stop().await;
    }

    #[tokio::test]
    async fn schedule_kind_from_create_is_interval() {
        let dir = tempfile::TempDir::new().unwrap();
        let store = AgentCronJobStore::new(dir.path().join("jobs.json"));
        let now = 1_700_000_000_000;
        let job = store.create(&input("tick", "every 10m", now)).unwrap();
        assert_eq!(job.schedule.kind, ScheduleKind::Interval);
    }

    /// The failure backoff: consecutive failed fires stretch the job's
    /// next run past its schedule (2m, 4m, ... capped at 1h) and record
    /// the error; one good run resets the stretch. Without it, a dead
    /// model route re-fires at the job's full cadence forever (the
    /// dogfood incident: ~120 fires of a failing every-2m heartbeat).
    #[tokio::test]
    async fn consecutive_failures_back_off_the_next_run() {
        const FIRST_PAUSE: u64 = 120_000;
        const SECOND_PAUSE: u64 = 240_000;
        let dir = tempfile::TempDir::new().unwrap();
        let store = Arc::new(AgentCronJobStore::new(dir.path().join("jobs.json")));
        let start = 1_700_000_000_000;
        let job = store.create(&input("tick", "every 1m", start)).unwrap();
        let job_id = job.id.clone();
        // First due moment: 60s after creation.
        let t1 = start + 61_000;
        let hooks = Arc::new(FailingHooks {
            runs: Arc::new(AtomicUsize::new(0)),
            error: std::sync::Mutex::new(Some("model route gone".to_string())),
            now: std::sync::Mutex::new(t1),
        });
        let scheduler = AgentCronScheduler::new(store.clone(), hooks.clone());
        // No `start()`: the timer task would race the explicit `run_due`
        // calls below (both re-read the mutable clock), so this test
        // drives the claim-dispatch-record loop directly.
        // Failure 1: the schedule rolls next to t1 + 60s, the backoff
        // raises it to t1 + 120s and the error lands on the job.
        assert_eq!(scheduler.run_due().await.unwrap(), 1);
        let job = store
            .list()
            .into_iter()
            .find(|job| job.id == job_id)
            .expect("job kept");
        assert_eq!(job.last_error.as_deref(), Some("model route gone"));
        assert_eq!(job.run_count, 1);
        assert_eq!(
            crate::cron::parse_iso_millis(job.next_run_at.as_deref().unwrap()),
            Some(t1 + FIRST_PAUSE)
        );
        // Failure 2 (clock advanced past the deferred run): the pause
        // doubles.
        let t2 = t1 + FIRST_PAUSE + 1;
        *hooks.now.lock().unwrap() = t2;
        assert_eq!(scheduler.run_due().await.unwrap(), 1);
        let job = store
            .list()
            .into_iter()
            .find(|job| job.id == job_id)
            .expect("job kept");
        assert_eq!(
            crate::cron::parse_iso_millis(job.next_run_at.as_deref().unwrap()),
            Some(t2 + SECOND_PAUSE)
        );
        // A good run clears the streak: the next run goes back to the
        // bare schedule...
        let t3 = t2 + SECOND_PAUSE + 1;
        *hooks.now.lock().unwrap() = t3;
        *hooks.error.lock().unwrap() = None;
        assert_eq!(scheduler.run_due().await.unwrap(), 1);
        let job = store
            .list()
            .into_iter()
            .find(|job| job.id == job_id)
            .expect("job kept");
        assert_eq!(job.last_error, None);
        assert_eq!(
            crate::cron::parse_iso_millis(job.next_run_at.as_deref().unwrap()),
            Some(t3 + 60_000)
        );
        // ...so the failure after it restarts at the base pause.
        let t4 = t3 + 60_000 + 1;
        *hooks.now.lock().unwrap() = t4;
        *hooks.error.lock().unwrap() = Some("model route gone".to_string());
        assert_eq!(scheduler.run_due().await.unwrap(), 1);
        let job = store
            .list()
            .into_iter()
            .find(|job| job.id == job_id)
            .expect("job kept");
        assert_eq!(
            crate::cron::parse_iso_millis(job.next_run_at.as_deref().unwrap()),
            Some(t4 + FIRST_PAUSE)
        );
    }

    /// Hooks whose runs can fail on demand, over a controllable clock.
    struct FailingHooks {
        runs: Arc<AtomicUsize>,
        error: std::sync::Mutex<Option<String>>,
        now: std::sync::Mutex<u64>,
    }

    impl AgentCronSchedulerHooks for FailingHooks {
        fn run_job(
            &self,
            _job: &AgentCronJob,
        ) -> impl Future<Output = anyhow::Result<Option<&'static str>>> {
            self.runs.fetch_add(1, Ordering::SeqCst);
            let error = self.error.lock().unwrap().clone();
            std::future::ready(match error {
                Some(message) => Err(anyhow::anyhow!(message)),
                None => Ok(None),
            })
        }
        fn now(&self) -> u64 {
            *self.now.lock().unwrap()
        }
    }
}
