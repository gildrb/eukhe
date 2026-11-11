//! The responsiveness probe. A worker that stops running (stopped by a
//! signal, its runtime wedged) keeps a live process, so its exit watch and
//! `get_worker_liveness` see nothing wrong, and an abort sent to it (through
//! the supervisor or a client's direct link) never lands: its session shows
//! a running turn forever. Every connected worker answers `worker_ping` on
//! its connection loop (`worker/connection.rs`), ahead of the commands it
//! runs. One that leaves a ping unanswered for [`WORKER_UNRESPONSIVE_MS`],
//! and a fresh ping after it, is killed through the stop escalation
//! (`boot_reap::stop_process`: SIGTERM, then its process group's SIGKILL);
//! its exit takes the crash path (the watch loop counts it against the
//! restart budget and relaunches it), and the relaunch stops the run it
//! hung in ([`super::interrupted_runs`]).
//!
//! The waits run on tokio's monotonic clock, which stands still while the
//! machine sleeps: a suspended laptop never reads as a hung worker. The
//! fresh ping covers a supervisor that was itself stopped past the window:
//! the worker's late answer is already in its socket.

use std::sync::{Arc, Weak};
use std::time::Duration;

use eukhe_types::daemon::DaemonWorkerCommand;

use super::interrupted_runs::InterruptedRun;
use super::{ResidentWorker, RouteAdmission, Supervisor};
use crate::timeouts::{WORKER_PROBE_INTERVAL_MS, WORKER_UNRESPONSIVE_MS};

/// Whether one ping was answered inside its wait.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Ping {
    /// The worker answered (a refusal included: it runs).
    Answered,
    /// The wait ran out.
    Unanswered,
    /// The connection is gone: the exit path owns the worker.
    Disconnected,
}

impl Supervisor {
    /// Probe the worker behind connection `epoch` of `resident` until that
    /// connection ends, the worker stops on purpose, or the probe kills it.
    pub(super) fn spawn_responsiveness_probe(
        self: &Arc<Self>,
        resident: &Arc<ResidentWorker>,
        epoch: u64,
    ) {
        let supervisor = Arc::clone(self);
        let resident = Arc::downgrade(resident);
        tokio::spawn(async move { supervisor.probe_responsiveness(resident, epoch).await });
    }

    #[tracing::instrument(skip(self, resident))]
    async fn probe_responsiveness(self: Arc<Self>, resident: Weak<ResidentWorker>, epoch: u64) {
        loop {
            tokio::time::sleep(Duration::from_millis(WORKER_PROBE_INTERVAL_MS)).await;
            let Some(resident) = resident.upgrade() else {
                return;
            };
            if !self.probes(&resident, epoch) {
                return;
            }
            match self.ping(&resident, WORKER_UNRESPONSIVE_MS).await {
                Ping::Answered => continue,
                Ping::Disconnected => return,
                Ping::Unanswered => {}
            }
            if !self.probes(&resident, epoch) {
                return;
            }
            match self.ping(&resident, WORKER_PROBE_INTERVAL_MS).await {
                Ping::Answered => continue,
                Ping::Disconnected => return,
                Ping::Unanswered => {}
            }
            if self.probes(&resident, epoch) {
                self.kill_unresponsive_worker(&resident).await;
            }
            return;
        }
    }

    /// The probe watches connection `epoch` only while it is the worker's
    /// live connection and nobody stops the worker on purpose.
    fn probes(&self, resident: &Arc<ResidentWorker>, epoch: u64) -> bool {
        resident.connection_is_current(epoch)
            && !self.is_stopping(resident)
            && !resident.route_state().retired
    }

    /// One `worker_ping`, waited for `wait_ms`.
    async fn ping(&self, resident: &Arc<ResidentWorker>, wait_ms: u64) -> Ping {
        let Ok(payload) = serde_json::to_value(DaemonWorkerCommand::WorkerPing {
            id: None,
            rest: serde_json::Map::default(),
        }) else {
            return Ping::Disconnected;
        };
        // The route's own budget outlasts the wait: the wait's end is the
        // verdict, never a route error.
        let route = self.route_command(
            resident,
            "worker_ping",
            payload,
            wait_ms.saturating_add(WORKER_PROBE_INTERVAL_MS),
            RouteAdmission::Control,
        );
        match tokio::time::timeout(Duration::from_millis(wait_ms), route).await {
            Ok(Ok(_)) => Ping::Answered,
            Ok(Err(_)) => Ping::Disconnected,
            Err(_elapsed) => Ping::Unanswered,
        }
    }

    /// Kill a worker that stopped answering, so the crash path restarts it
    /// and its session ends the hung turn with a notice.
    async fn kill_unresponsive_worker(self: &Arc<Self>, resident: &Arc<ResidentWorker>) {
        let (pid, start_id, session_file) = {
            let descriptor = resident.descriptor.lock().await;
            (
                u32::try_from(descriptor.pid).unwrap_or(0),
                descriptor.process_start_id.clone(),
                descriptor.session_file.clone(),
            )
        };
        // Only a recorded worker process: never pid 0 (a process group) or
        // this supervisor.
        if pid == 0 || pid == std::process::id() {
            return;
        }
        self.log_line(&format!(
            "session worker {} (pid {pid}) did not answer for {}s; killing it to restart it",
            resident.worker_id,
            WORKER_UNRESPONSIVE_MS / 1_000
        ));
        // Declared before the kill: the relaunch the exit starts reads it.
        if let Some(session_file) = &session_file {
            self.interrupted_runs.declare(
                session_file,
                InterruptedRun::Unresponsive {
                    after_ms: WORKER_UNRESPONSIVE_MS,
                },
            );
        }
        match crate::boot_reap::stop_process(pid, start_id).await {
            crate::boot_reap::ReapOutcome::Survived => self.log_line(&format!(
                "session worker {} (pid {pid}) survived its kill",
                resident.worker_id
            )),
            crate::boot_reap::ReapOutcome::AlreadyGone
            | crate::boot_reap::ReapOutcome::Term
            | crate::boot_reap::ReapOutcome::Kill => {}
        }
    }
}
