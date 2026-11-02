//! The worker's park behavior (the old turn runner's park arm): the
//! settled-child kernel release (TS #2483's `canPassivateSettledSession`)
//! and the whole-worker idle passivation (TS `idleEvictionMinutes`,
//! worker-driven). Every run end parks the worker — the `park_notify`
//! wake — and each park re-checks both: a parent-owned child with no
//! work releases its kernel (the next kernel use revives it from the
//! flushed snapshot), and an idle unattached root session under a live
//! threshold asks the supervisor for the graceful stop. Both read the one
//! work set ([`super::run_gate::background_work`]): a running kernel
//! `bash()` handle or detached cell holds the release as it holds the
//! stop, and its settlement wakes a run whose end parks again. Both are
//! best-effort: a rejected or failed ask leaves the worker resident and
//! the next park re-arms.

use std::path::PathBuf;
use std::sync::Arc;
use std::time::Duration;

use eukhe_core::durable::rlm::{kernel_background_jobs, release_settled_kernel};
use eukhe_core::settings::{IdleEviction, SettingsManager};
use serde_json::json;
use tokio::sync::Notify;

use super::{SessionCore, SessionSlot};
use crate::scheduled_jobs::ScheduledJobs;
use crate::session_input_pause::InputPauseTable;
use crate::supervisor_link::SupervisorLink;
use crate::user_bash::UserBash;

fn lock<T>(mutex: &std::sync::Mutex<T>) -> std::sync::MutexGuard<'_, T> {
    mutex
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

/// What the parked loop reads.
pub(crate) struct ParkContext {
    pub(crate) core: Arc<std::sync::Mutex<SessionCore>>,
    pub(crate) session: SessionSlot,
    pub(crate) user_bash: Arc<UserBash>,
    pub(crate) input_pauses: InputPauseTable,
    pub(crate) scheduled: Arc<ScheduledJobs>,
    pub(crate) link: Arc<SupervisorLink>,
    pub(crate) worker_token: String,
    pub(crate) agent_dir: PathBuf,
    pub(crate) park_notify: Arc<Notify>,
}

/// The park gates one locked core read answers: every term the kernel
/// release and the idle window share.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ParkGates {
    /// A client is attached.
    pub(crate) attached: bool,
    pub(crate) compacting: bool,
    pub(crate) shutdown: bool,
    /// A run is live on the shown conversation.
    pub(crate) busy: bool,
    /// Queued input exists (the inbox, or withdrawn inputs). A withdrawn
    /// input is not work (no other idle decision counts it), but it still
    /// keeps the worker resident, so its release needs no revival.
    pub(crate) queued: bool,
    /// An input-pause lease is held.
    pub(crate) paused: bool,
    /// A live background bash handle runs.
    pub(crate) bash: bool,
    /// This worker hosts a parent-owned child (`rlm_depth > 0`).
    pub(crate) child: bool,
}

impl ParkGates {
    /// The gates of one locked core read, with the worker's own pause and
    /// bash state.
    pub(crate) fn of(core: &SessionCore, paused: bool, bash: bool) -> Self {
        Self {
            attached: !core.attached_client_ids.is_empty(),
            compacting: core.is_compacting(),
            shutdown: core.shutdown_requested,
            busy: core.is_busy(),
            queued: core
                .view
                .as_ref()
                .is_some_and(|view| !view.inbox.is_empty())
                || !core.suspended.is_empty()
                || !core.held.is_empty(),
            paused,
            bash,
            child: core.rlm_depth > 0,
        }
    }

    /// The park state both behaviors require: unattached, not compacting,
    /// not shutting down, no run, no queued input, no pause lease, no
    /// live bash.
    pub(crate) fn parked(self) -> bool {
        !self.attached
            && !self.compacting
            && !self.shutdown
            && !self.busy
            && !self.queued
            && !self.bash
    }
}

/// Where the session's run stands for the kernel release.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RunPark {
    /// No run waits at a pause: none runs, or one runs.
    Free,
    /// A paused run waits at its held boundary with no tool call in
    /// flight (`RunPause` `held`): it runs nothing until it goes on.
    Held,
}

/// The settled-child release verdict (TS #2483, worker-side): the park
/// state plus the parent-owned identity. A paused worker counts as idle:
/// its held run and the messages it keeps start nothing. The registered
/// scheduled-jobs gate lives with the fire (a store read cannot run under
/// the core lock).
pub(crate) fn child_release_due(gates: ParkGates, run: RunPark) -> bool {
    gates.child
        && !gates.paused
        && match run {
            RunPark::Free => gates.parked(),
            RunPark::Held => !gates.attached && !gates.compacting && !gates.shutdown && !gates.bash,
        }
}

/// The idle-eviction window of one park (TS's `idleEvictionMinutes`
/// consumer): `Some(remaining)` when the park state holds and the setting
/// is a live threshold, `None` otherwise (attached sessions, `"off"`, a
/// held pause, and a child worker stay parked without a timer — the
/// child's residency is the kernel release's business).
pub(crate) fn idle_window(
    gates: ParkGates,
    last_activity_ms: u64,
    now_ms: u64,
    eviction: IdleEviction,
) -> Option<Duration> {
    if !gates.parked() || gates.paused || gates.child {
        return None;
    }
    let minutes = match eviction {
        IdleEviction::Off => return None,
        IdleEviction::Minutes(minutes) => minutes,
    };
    let idle_ms = now_ms.saturating_sub(last_activity_ms);
    let threshold_ms = minutes.saturating_mul(60_000);
    Some(Duration::from_millis(threshold_ms.saturating_sub(idle_ms)))
}

/// Whether the session still owns a registered active or paused
/// scheduled job (the keep-cron gate: the wake must not lose its worker).
fn has_registered_job(scheduled: &ScheduledJobs, active_session_id: &str) -> bool {
    scheduled.store().list().iter().any(|job| {
        job.active_session_id == active_session_id
            && matches!(
                job.status,
                eukhe_core::cron::JobStatus::Active | eukhe_core::cron::JobStatus::Paused
            )
    })
}

/// The park loop: every wake re-checks the gates, releases a settled
/// child's kernel, and (re-)arms the idle window; the window's fire asks
/// the supervisor for the graceful stop over the worker's link. A queued
/// delivery or fresh prompt wins the select's notified arm and the next
/// park re-arms.
pub(crate) async fn passivation_loop(context: ParkContext) {
    loop {
        context.park_notify.notified().await;
        let (gates, last_activity_ms, cwd, active_session_id) = {
            let core = lock(&context.core);
            (
                ParkGates::of(
                    &core,
                    context.input_pauses.paused(),
                    context.user_bash.is_running(),
                ),
                core.last_activity_ms,
                core.cwd.clone(),
                core.active_session_id.clone(),
            )
        };
        release_settled_child_kernel(&context, gates, &active_session_id).await;
        // The idle window: the fire re-checks everything fresh (the TS
        // fresh-snapshot fence).
        let eviction = SettingsManager::create(std::path::Path::new(&cwd), &context.agent_dir)
            .get_idle_eviction();
        let Some(remaining) = idle_window(gates, last_activity_ms, crate::util::now_ms(), eviction)
        else {
            continue;
        };
        tokio::select! {
            () = context.park_notify.notified() => {}
            () = tokio::time::sleep(remaining) => {
                maybe_request_idle_passivation(&context, cwd.clone()).await;
            }
        }
    }
}

/// The settled-child kernel release of one park (best-effort: a failed
/// dispose leaves nothing behind — the entry is gone either way, so a
/// later use boots fresh). The release disposes the kernel, which ends
/// every `bash()` handle and detached cell it runs, so the idle
/// passivation's work set holds it: a child with background work keeps
/// its kernel, and the run its job's settlement wakes parks again and
/// releases then. A paused child's held run releases too: only its
/// kernel's own jobs hold it (they keep running while paused); its paused
/// children and kept messages do not.
async fn release_settled_child_kernel(
    context: &ParkContext,
    gates: ParkGates,
    active_session_id: &str,
) {
    let Some(hosted) = context.session.get() else {
        return;
    };
    let Ok(main) = hosted.main() else {
        return;
    };
    let run = if hosted.deps().run_pause.view().held {
        RunPark::Held
    } else {
        RunPark::Free
    };
    if !child_release_due(gates, run) || has_registered_job(&context.scheduled, active_session_id) {
        return;
    }
    let working = match run {
        RunPark::Free => {
            super::run_gate::background_work(&context.session, &context.user_bash).await
                == crate::work_gate::Work::Ongoing
        }
        RunPark::Held => {
            context.user_bash.is_running() || kernel_background_jobs(hosted.deps(), main.id()) > 0
        }
    };
    if working {
        return;
    }
    release_settled_kernel(hosted.deps(), main.id()).await;
}

/// The fire: re-check the full gate set on a fresh snapshot (the TS
/// `passivateSession` fresh-snapshot fence), then ask the supervisor for
/// the graceful stop. The request carries the worker token; the
/// supervisor verifies it against the resident worker before stopping. A
/// rejected or failed request leaves the worker resident — the next park
/// re-arms, exactly like the kernel release's best-effort arm.
async fn maybe_request_idle_passivation(context: &ParkContext, cwd: String) {
    let (gates, last_activity_ms, active_session_id) = {
        let core = lock(&context.core);
        (
            ParkGates::of(
                &core,
                context.input_pauses.paused(),
                context.user_bash.is_running(),
            ),
            core.last_activity_ms,
            core.active_session_id.clone(),
        )
    };
    if !gates.parked()
        || gates.paused
        || gates.child
        || has_registered_job(&context.scheduled, &active_session_id)
    {
        return;
    }
    // The work the core does not show (a background job, an unsettled
    // child or workflow run, a durable inbox input) keeps the worker.
    if super::run_gate::background_work(&context.session, &context.user_bash).await
        == crate::work_gate::Work::Ongoing
    {
        return;
    }
    let settings = SettingsManager::create(std::path::Path::new(&cwd), &context.agent_dir);
    let IdleEviction::Minutes(minutes) = settings.get_idle_eviction() else {
        return;
    };
    // The idle threshold still holds on the fresh clock.
    if crate::util::now_ms().saturating_sub(last_activity_ms) < minutes.saturating_mul(60_000) {
        return;
    }
    let command = json!({
        "type": "worker_idle_passivation",
        "workerToken": context.worker_token,
        "idleMinutes": minutes,
    });
    // The bounded ask: the supervisor's stop path routes the shutdown
    // back into this worker (the graceful flush), so the timeout only
    // bounds the ask, not the stop.
    let _ = context.link.request(command, Duration::from_secs(30)).await;
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A fabricated core: `test_core` plus the gates' fields.
    fn core(attached: usize, rlm_depth: u32) -> std::sync::Mutex<SessionCore> {
        let mut core = SessionCore::test_core("/tmp".to_string());
        core.attached_client_ids = vec!["client".to_string(); attached];
        core.rlm_depth = rlm_depth;
        core.last_activity_ms = 10_000;
        std::sync::Mutex::new(core)
    }

    fn gates(attached: usize, rlm_depth: u32, paused: bool, bash: bool) -> ParkGates {
        let core = core(attached, rlm_depth);
        let guard = core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        ParkGates::of(&guard, paused, bash)
    }

    /// The settled-child release needs the park state plus the
    /// parent-owned identity; a held pause defers (the release would
    /// race the pause's own delivery).
    #[test]
    fn the_child_release_needs_the_park_state() {
        assert!(child_release_due(gates(0, 1, false, false), RunPark::Free));
        assert!(
            !child_release_due(gates(0, 0, false, false), RunPark::Free),
            "a root never releases"
        );
        assert!(
            !child_release_due(gates(1, 1, false, false), RunPark::Free),
            "an attached client holds it"
        );
        assert!(
            !child_release_due(gates(0, 1, true, false), RunPark::Free),
            "a pause defers it"
        );
        assert!(
            !child_release_due(gates(0, 1, false, true), RunPark::Free),
            "a live bash holds it"
        );
    }

    /// A busy, compacting, shutting-down, or queued park never releases.
    #[test]
    fn a_live_park_never_releases() {
        let core = core(0, 1);
        {
            let mut locked = core
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            locked.shutdown_requested = true;
        }
        let gates = ParkGates::of(
            &core
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner),
            false,
            false,
        );
        assert!(!child_release_due(gates, RunPark::Free));
        assert!(!child_release_due(gates, RunPark::Held));
    }

    /// A paused worker counts as idle for the kernel release: its run is
    /// live and its kept messages are queued, but the run waits at its
    /// held boundary and starts nothing. Running, the same gates hold the
    /// kernel; an attached client or a live bash still holds it.
    #[test]
    fn a_held_paused_run_counts_as_idle_for_the_release() {
        let paused_worker = ParkGates {
            busy: true,
            queued: true,
            ..gates(0, 1, false, false)
        };
        assert_eq!(
            (
                child_release_due(paused_worker, RunPark::Held),
                child_release_due(paused_worker, RunPark::Free),
                child_release_due(
                    ParkGates {
                        attached: true,
                        ..paused_worker
                    },
                    RunPark::Held
                ),
                child_release_due(
                    ParkGates {
                        bash: true,
                        ..paused_worker
                    },
                    RunPark::Held
                ),
            ),
            (true, false, false, false)
        );
    }

    /// The idle window arms only for a parked root under a live
    /// threshold, and measures from the last activity.
    #[test]
    fn the_idle_window_arms_for_a_parked_root() {
        let parked = gates(0, 0, false, false);
        assert_eq!(
            idle_window(parked, 10_000, 10_000 + 60_000, IdleEviction::Minutes(5)),
            Some(Duration::from_mins(4)),
            "four minutes remain of the five"
        );
        assert_eq!(
            idle_window(parked, 10_000, 10_000 + 60_000, IdleEviction::Off),
            None,
            "an off threshold never arms"
        );
        assert_eq!(
            idle_window(parked, 10_000, 10_000, IdleEviction::Minutes(5)),
            Some(Duration::from_mins(5)),
            "a fresh park arms the whole window"
        );
        // A child, a pause, or an attached client stays parked without a
        // timer.
        assert_eq!(
            idle_window(gates(0, 1, false, false), 0, 0, IdleEviction::Minutes(5)),
            None
        );
        assert_eq!(
            idle_window(gates(0, 0, true, false), 0, 0, IdleEviction::Minutes(5)),
            None
        );
        assert_eq!(
            idle_window(gates(1, 0, false, false), 0, 0, IdleEviction::Minutes(5)),
            None
        );
    }

    /// Regression: a parked child whose kernel ran a background `bash()`
    /// command (a long build) released its kernel at the park, and the
    /// dispose killed the command (`exit -15`). The release holds while
    /// the kernel has background work; once the command settled and the
    /// run its notice woke parked, the release goes through.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn a_parked_child_keeps_its_kernel_while_a_background_job_runs() {
        const SESSION: &str = "child-background-job";
        let gate_dir = tempfile::tempdir().expect("tempdir");
        let gate = gate_dir.path().join("gate");
        let command = format!("while [ ! -f '{}' ]; do sleep 0.05; done", gate.display());
        let cell = format!("from rlm import bash\nbuild = bash({command:?})");
        let (dir, worker) = crate::durable_test_support::created_worker_with(
            SESSION,
            serde_json::json!([
                { "content": [{ "type": "toolCall", "name": "ipython", "arguments": { "code": cell }, "id": "call-1" }] },
                "started",
                "settled",
            ]),
            serde_json::json!({ "rlmDepth": 1 }),
        )
        .await;
        let context = ParkContext {
            core: Arc::clone(&worker.core),
            session: worker.session.clone(),
            user_bash: Arc::clone(&worker.user_bash),
            input_pauses: worker.input_pauses.clone(),
            scheduled: Arc::clone(&worker.scheduled),
            link: Arc::new(SupervisorLink::new(PathBuf::new())),
            worker_token: "token".to_owned(),
            agent_dir: dir.path().join("agent"),
            park_notify: Arc::clone(&worker.park_notify),
        };
        let park = || {
            let core = lock(&worker.core);
            let gates = ParkGates::of(&core, false, false);
            assert!(
                child_release_due(gates, RunPark::Free),
                "the child parked: {gates:?}"
            );
            gates
        };
        let jobs = || {
            let hosted = worker.session.get().expect("a hosted session");
            let main = hosted.main().expect("main conversation");
            eukhe_core::durable::rlm::kernel_background_jobs(hosted.deps(), main.id())
        };
        let idle = |payload: serde_json::Value| {
            let worker = Arc::clone(&worker);
            async move {
                let idle = worker.dispatch("wait_for_idle", &payload).await;
                assert!(idle.success, "wait_for_idle: {idle:?}");
            }
        };

        let prompt = worker
            .dispatch("prompt", &serde_json::json!({ "message": "build" }))
            .await;
        assert!(prompt.success, "prompt: {prompt:?}");
        idle(serde_json::json!({})).await;
        assert_eq!(jobs(), 1, "the build runs in the child's kernel");
        release_settled_child_kernel(&context, park(), SESSION).await;
        assert_eq!(jobs(), 1, "the park kept the kernel and its build");

        std::fs::write(&gate, "").expect("open the gate");
        idle(serde_json::json!({ "waitForRlmQuiescence": true, "waitForBackgroundJobs": true }))
            .await;
        release_settled_child_kernel(&context, park(), SESSION).await;
        let listed = worker
            .dispatch(
                "list_kernel_bash",
                &serde_json::json!({ "activeSessionId": SESSION }),
            )
            .await;
        assert_eq!(
            listed.error.as_deref(),
            Some("Kernel is not running"),
            "the settled child released its kernel: {listed:?}"
        );
    }
}
