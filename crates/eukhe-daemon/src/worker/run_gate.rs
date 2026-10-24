//! The worker's run-start gate (its decisions run as the compiled Bend
//! core, `bend/ffi_launcher.bend`; see `crate::work_gate`). An idle
//! shutdown quiesces it: an idle worker closes the gate, and every run
//! start waits at a closed gate. Each run start passes the gate with a
//! [`RunAdmission`]; while one lives, a quiesce answers busy, so a run that
//! passed the gate before it closed is never lost to the stop.
//!
//! The gate opens again on `worker_release`, or by itself after
//! [`QUIESCE_HOLD_MS`]: a worker whose supervisor died while it decided
//! does not stay quiesced.

use std::sync::{Arc, Mutex, PoisonError};
use std::time::Duration;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_core::durable::children::unsettled_child_tasks;
use eukhe_core::durable::rlm::kernel_background_jobs;
use eukhe_core::durable::workflow::unsettled_run_tasks;
use tokio::sync::Notify;

use super::durable_host::bridge::inbox_previews;
use super::{response_failure, response_success, DaemonResponse, SessionCore, Worker};
use crate::timeouts::QUIESCE_HOLD_MS;
use crate::work_gate::{QuiesceAnswer, Work, WorkGate};

/// The run-start gate on the session core.
#[derive(Default)]
pub(crate) struct RunGate {
    gate: WorkGate,
    /// Counts the gate changes: the hold timer opens only the quiesce that
    /// armed it.
    epoch: u64,
    /// Run starts that passed the gate and did not finish their admission.
    admissions: u32,
    /// Wakes the run starts that wait at the closed gate.
    opened: Arc<Notify>,
}

impl RunGate {
    /// Open the gate and wake the run starts that wait at it.
    fn open(&mut self) {
        self.epoch += 1;
        self.gate.release();
        self.opened.notify_waiters();
    }
}

/// The run-start gate is quiesced: a supervisor replacement is deciding.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[error("Session is paused while the daemon decides a restart; retry")]
pub(crate) struct Quiesced;

/// A run start that passed the gate. Keep it until the run's input is
/// admitted (or the started work is visible); then drop it.
pub(crate) struct RunAdmission {
    core: Arc<Mutex<SessionCore>>,
}

impl RunAdmission {
    /// Pass the gate; wait while a quiesce holds it closed.
    pub(crate) async fn enter(core: &Arc<Mutex<SessionCore>>) -> Self {
        let opened = Arc::clone(&lock(core).run_gate.opened);
        loop {
            // Register for the wake before the gate is read, so an open
            // between the read and the wait is not missed.
            let notified = opened.notified();
            tokio::pin!(notified);
            notified.as_mut().enable();
            if let Ok(admission) = Self::try_enter(core) {
                return admission;
            }
            notified.await;
        }
    }

    /// Pass the gate now, or refuse when a quiesce holds it closed.
    ///
    /// # Errors
    ///
    /// [`Quiesced`] while a quiesce holds the gate closed.
    pub(crate) fn try_enter(core: &Arc<Mutex<SessionCore>>) -> Result<Self, Quiesced> {
        let mut locked = lock(core);
        if locked.run_gate.gate.admits() {
            locked.run_gate.admissions += 1;
            Ok(Self {
                core: Arc::clone(core),
            })
        } else {
            Err(Quiesced)
        }
    }
}

impl Drop for RunAdmission {
    fn drop(&mut self) {
        let mut locked = lock(&self.core);
        locked.run_gate.admissions = locked.run_gate.admissions.saturating_sub(1);
    }
}

fn lock(core: &Mutex<SessionCore>) -> std::sync::MutexGuard<'_, SessionCore> {
    core.lock().unwrap_or_else(PoisonError::into_inner)
}

impl Worker {
    /// `worker_quiesce`: close the run gate when the session is idle. The
    /// work the core shows is read under the core lock together with the
    /// gate change. With the gate closed no run can start, so the durable
    /// work is read after it: unsettled child tasks and workflow runs, kernel background
    /// jobs, a user bash, and a queued input or run the core does not show
    /// yet. Any work opens the gate again and answers busy. Success means
    /// quiesced.
    pub(crate) async fn handle_quiesce(&self) -> DaemonResponse {
        const COMMAND: &str = "worker_quiesce";
        let busy = || response_failure(None, COMMAND, "Session has work in flight", None);
        // A worker with no open main conversation is never quiesced.
        if self
            .session
            .get()
            .is_none_or(|hosted| hosted.main().is_err())
        {
            return busy();
        }
        let epoch = {
            let mut core = lock(&self.core);
            let work = if core.shutdown_requested || !core.created || core.run_gate.admissions > 0 {
                Work::Ongoing
            } else {
                core.work()
            };
            match core.run_gate.gate.quiesce(work) {
                QuiesceAnswer::Busy => return busy(),
                QuiesceAnswer::Quiesced => {
                    core.run_gate.epoch += 1;
                    core.run_gate.epoch
                }
            }
        };
        let durable_idle = background_work(&self.session, &self.user_bash).await == Work::Idle;
        let mut core = lock(&self.core);
        if core.run_gate.epoch != epoch {
            // A release or a later quiesce changed the gate meanwhile.
            return busy();
        }
        let work = if durable_idle {
            core.work()
        } else {
            Work::Ongoing
        };
        match work {
            Work::Idle => {
                let held = Arc::clone(&self.core);
                tokio::spawn(async move {
                    tokio::time::sleep(Duration::from_millis(QUIESCE_HOLD_MS)).await;
                    let mut core = lock(&held);
                    if core.run_gate.epoch == epoch {
                        core.run_gate.open();
                    }
                });
                response_success(None, COMMAND, None)
            }
            Work::Ongoing => {
                core.run_gate.open();
                busy()
            }
        }
    }

    /// `worker_release`: the idle shutdown did not commit; open the gate.
    pub(crate) fn handle_release(&self) -> DaemonResponse {
        lock(&self.core).run_gate.open();
        response_success(None, "worker_release", None)
    }

    /// The session's work: the one set every idle decision reads (the
    /// quiesce, the lost-supervisor exit, the busy refresh and the idle
    /// park): what the core shows (a run, a compaction, a queued view
    /// input), an admitted run, then [`background_work`].
    pub(crate) async fn session_work(&self) -> Work {
        let shown = {
            let core = lock(&self.core);
            if core.run_gate.admissions > 0 {
                Work::Ongoing
            } else {
                core.work()
            }
        };
        match shown {
            Work::Ongoing => Work::Ongoing,
            Work::Idle => background_work(&self.session, &self.user_bash).await,
        }
    }
}

/// The work the core does not show: unsettled child tasks and workflow
/// runs, a queued inbox input, a kernel background job, or a running user
/// bash. A withdrawn (paused or held) input is not work: it waits for its
/// release. A durable read that fails counts as work (unknown never reads
/// idle); a worker with no hosted session holds none.
pub(crate) async fn background_work(
    session: &super::durable_host::SessionSlot,
    user_bash: &crate::user_bash::UserBash,
) -> Work {
    if user_bash.is_running() {
        return Work::Ongoing;
    }
    let Some(hosted) = session.get() else {
        return Work::Idle;
    };
    let Ok(main) = hosted.main() else {
        return Work::Idle;
    };
    let cx = &BACKGROUND_CONTEXT;
    let children = unsettled_child_tasks(hosted.harness(), main.id(), cx).await;
    let runs = unsettled_run_tasks(hosted.harness(), main.id(), cx).await;
    let inbox = inbox_previews(hosted.harness(), main.id(), cx).await;
    let idle = children.is_ok_and(|children| children.is_empty())
        && runs.is_ok_and(|runs| runs.is_empty())
        && inbox.is_ok_and(|inbox| inbox.is_empty())
        && kernel_background_jobs(hosted.deps(), main.id()) == 0;
    if idle {
        Work::Idle
    } else {
        Work::Ongoing
    }
}

#[cfg(test)]
mod tests {
    use std::sync::{Arc, Mutex};

    use serde_json::json;

    use super::{lock, Quiesced, RunAdmission};
    use crate::journal::WorkerRecoveryJournal;
    use crate::protocol::{response_failure, response_success};
    use crate::work_gate::{QuiesceAnswer, Work};
    use crate::worker::{SessionCore, Worker, WorkerConfig};

    /// A run start waits at a quiesced gate and goes on once it opens.
    #[tokio::test]
    async fn a_run_start_waits_at_a_quiesced_gate_until_it_opens() {
        let core = Arc::new(Mutex::new(SessionCore::test_core("/".to_string())));
        assert_eq!(
            lock(&core).run_gate.gate.quiesce(Work::Idle),
            QuiesceAnswer::Quiesced
        );
        assert_eq!(RunAdmission::try_enter(&core).err(), Some(Quiesced));
        let waiting = RunAdmission::enter(&core);
        tokio::pin!(waiting);
        assert!(futures::poll!(&mut waiting).is_pending());
        lock(&core).run_gate.open();
        let admission = waiting.await;
        assert_eq!(lock(&core).run_gate.admissions, 1);
        drop(admission);
        assert_eq!(lock(&core).run_gate.admissions, 0);
    }

    /// A created worker on an in-memory session (no model call runs).
    async fn created_worker(dir: &std::path::Path) -> Arc<Worker> {
        std::fs::create_dir_all(dir.join("agent")).expect("agent dir");
        std::fs::create_dir_all(dir.join("work")).expect("cwd");
        let worker = Worker::new(
            WorkerConfig {
                socket_path: dir.join("worker.sock"),
                supervisor_socket_path: std::path::PathBuf::new(),
                token: "token".to_owned(),
                worker_instance_id: String::new(),
                active_session_id: "worker-test".to_owned(),
                agent_dir: dir.join("agent"),
                recovery_journal_path: dir.join("recovery.jsonl"),
                script: Some(json!({ "responses": [] })),
            },
            None,
        );
        *worker.recovery.lock().unwrap() =
            Some(WorkerRecoveryJournal::open(&dir.join("recovery.jsonl")).expect("journal"));
        let created = worker
            .dispatch(
                "create",
                &json!({ "noSession": true, "cwd": dir.join("work") }),
            )
            .await;
        assert!(created.success, "create failed: {created:?}");
        Arc::new(worker)
    }

    /// A run start that passed the gate makes a quiesce busy (its input
    /// may not be visible yet); an idle worker quiesces, refuses new run
    /// starts, and admits them again after the release.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn a_quiesce_is_busy_while_a_run_start_is_admitted() {
        let dir = tempfile::tempdir().expect("tempdir");
        let worker = created_worker(dir.path()).await;
        let admitted = RunAdmission::try_enter(&worker.core).expect("an open gate");
        assert_eq!(
            worker.dispatch("worker_quiesce", &json!({})).await,
            response_failure(None, "worker_quiesce", "Session has work in flight", None)
        );
        drop(admitted);
        assert_eq!(
            worker.dispatch("worker_quiesce", &json!({})).await,
            response_success(None, "worker_quiesce", None)
        );
        assert_eq!(RunAdmission::try_enter(&worker.core).err(), Some(Quiesced));
        assert_eq!(
            worker.dispatch("worker_release", &json!({})).await,
            response_success(None, "worker_release", None)
        );
        assert!(RunAdmission::try_enter(&worker.core).is_ok());
    }
}
