//! The idle shutdown (`shutdown` with `ifIdle`; the model is
//! bend/launcher.bend). The supervisor decides it atomically with the
//! stop; the client never decides:
//!
//! 1. The replacement gate closes: no worker is launched, relaunched or
//!    adopted while the shutdown decides (a launch already in flight
//!    makes the daemon busy).
//! 2. Every worker is asked to quiesce, all at the same time, inside one
//!    [`QUIESCE_ANSWER_MS`] window. An idle worker closes its run gate; a
//!    worker with work, or one that does not answer, is busy.
//! 3. When every worker quiesced, the normal shutdown runs. Else every
//!    worker is released, the gate opens, and the shutdown is refused as
//!    busy.

use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::Duration;

use serde_json::json;
use tokio::sync::Notify;

use super::{RouteAdmission, Supervisor};
use crate::timeouts::QUIESCE_ANSWER_MS;
use crate::work_gate::{idle_shutdown_commits, QuiesceAnswer};

/// The gate an idle shutdown holds while it decides.
#[derive(Default)]
pub(crate) struct ReplacementGate {
    /// An idle shutdown is deciding.
    deciding: AtomicBool,
    /// Worker launches in flight (each holds a [`LaunchTicket`]).
    launches: AtomicUsize,
    /// Wakes the launches that wait for the decision.
    opened: Notify,
}

impl ReplacementGate {
    /// Enter one worker launch (a create, a relaunch, an adoption); wait
    /// while an idle shutdown decides. After the wait the caller checks
    /// whether the supervisor is shutting down.
    pub(crate) async fn enter_launch(&self) -> LaunchTicket<'_> {
        loop {
            // Register for the wake before the gate is read, so an open
            // between the read and the wait is not missed.
            let opened = self.opened.notified();
            tokio::pin!(opened);
            opened.as_mut().enable();
            // The count rises before the gate is read; the decision sets
            // the gate before it reads the count. So either the launch
            // sees the decision, or the decision sees the launch.
            self.launches.fetch_add(1, Ordering::SeqCst);
            if !self.deciding.load(Ordering::SeqCst) {
                return LaunchTicket { gate: self };
            }
            self.launches.fetch_sub(1, Ordering::SeqCst);
            opened.await;
        }
    }

    /// End the decision: the launches that waited go on.
    pub(crate) fn open(&self) {
        self.deciding.store(false, Ordering::SeqCst);
        self.opened.notify_waiters();
    }
}

/// One worker launch in flight; an idle shutdown that starts meanwhile is
/// busy.
pub(crate) struct LaunchTicket<'a> {
    gate: &'a ReplacementGate,
}

impl Drop for LaunchTicket<'_> {
    fn drop(&mut self) {
        self.gate.launches.fetch_sub(1, Ordering::SeqCst);
    }
}

/// The idle shutdown's decision.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum IdleShutdown {
    /// Every worker quiesced. The replacement gate stays closed: the
    /// caller sets the shutdown gate and then opens it.
    Commit,
    /// Some session has work: the workers were released and the gate is
    /// open again.
    Busy,
}

impl Supervisor {
    /// Phases 1 and 2 of the idle shutdown, and phase 3 when it does not
    /// commit (see the module docs).
    pub(super) async fn decide_idle_shutdown(self: &Arc<Self>) -> IdleShutdown {
        let gate = &self.replacement_gate;
        if gate.deciding.swap(true, Ordering::SeqCst) {
            // Another idle shutdown decides: this one does not wait for it.
            return IdleShutdown::Busy;
        }
        if gate.launches.load(Ordering::SeqCst) > 0 {
            gate.open();
            return IdleShutdown::Busy;
        }
        let residents = self.registry.list().await;
        let deadline = tokio::time::Instant::now() + Duration::from_millis(QUIESCE_ANSWER_MS);
        let answers = futures::future::join_all(residents.iter().map(|resident| async move {
            let remaining = deadline.saturating_duration_since(tokio::time::Instant::now());
            match self
                .route_command_typed(
                    resident,
                    "worker_quiesce",
                    json!({}),
                    u64::try_from(remaining.as_millis()).unwrap_or(QUIESCE_ANSWER_MS),
                    RouteAdmission::Control,
                )
                .await
            {
                Ok(response) if response.success => QuiesceAnswer::Quiesced,
                Ok(_) | Err(_) => QuiesceAnswer::Busy,
            }
        }))
        .await;
        if idle_shutdown_commits(answers) {
            return IdleShutdown::Commit;
        }
        futures::future::join_all(residents.iter().map(|resident| async move {
            if let Err(error) = self
                .route_command_typed(
                    resident,
                    "worker_release",
                    json!({}),
                    QUIESCE_ANSWER_MS,
                    RouteAdmission::Control,
                )
                .await
            {
                // The worker's own hold opens its gate when the release
                // does not reach it.
                self.log_line(&format!(
                    "session worker {} release failed: {error:#}",
                    resident.worker_id
                ));
            }
        }))
        .await;
        gate.open();
        IdleShutdown::Busy
    }
}

#[cfg(test)]
mod tests {
    use std::sync::{Arc, Mutex, PoisonError};

    use eukhe_types::daemon::{DaemonErrorInfo, DaemonResponse, DaemonWorkerDescriptor};
    use eukhe_types::platform::transport::TransportStream;
    use tokio::io::{AsyncBufReadExt as _, AsyncWriteExt as _, BufReader};

    use super::{IdleShutdown, Ordering, Supervisor};
    use crate::registry::{ResidentWorker, WorkerReply, WorkerRequest};
    use crate::supervisor::SupervisorOptions;
    use crate::work_gate::{QuiesceAnswer, Work, WorkGate};

    fn supervisor(dir: &std::path::Path) -> Arc<Supervisor> {
        Arc::new(
            Supervisor::new(SupervisorOptions {
                socket_path: dir.join("daemon.sock"),
                agent_dir: dir.join("agent"),
            })
            .expect("supervisor"),
        )
    }

    /// A resident whose worker is faux: it answers `worker_quiesce` with a
    /// real [`WorkGate`] over the session's `work`, answers every other
    /// command with success, and records the command types it received.
    async fn faux_worker(
        supervisor: &Supervisor,
        work: Arc<Mutex<Work>>,
    ) -> Arc<Mutex<Vec<String>>> {
        let descriptor: DaemonWorkerDescriptor = serde_json::from_value(serde_json::json!({
            "version": 2,
            "workerId": "w-faux",
            "pid": 0,
            "socketPath": "/tmp/none.sock",
            "recoveryJournalPath": "/tmp/none.jsonl",
            "supervisorSocketPath": "/tmp/none.sock",
            "authenticationToken": "test",
            "rootActiveSessionId": "w-faux",
            "createdAt": "2026-10-19T00:00:00Z",
            "updatedAt": "2026-10-19T00:00:00Z",
            "lifecycle": "ready",
            "createCommand": {},
            "consecutiveFailures": 0,
        }))
        .expect("descriptor");
        let resident = ResidentWorker::new(
            "w-faux".to_string(),
            descriptor,
            std::path::PathBuf::from("/tmp/none.descriptor.json"),
        );
        let (cmd_tx, mut cmd_rx) = tokio::sync::mpsc::channel::<WorkerRequest>(16);
        *resident.cmd_tx.lock().await = Some(cmd_tx);
        supervisor.registry.insert(Arc::clone(&resident)).await;
        let seen = Arc::new(Mutex::new(Vec::new()));
        let record = Arc::clone(&seen);
        tokio::spawn(async move {
            let mut gate = WorkGate::default();
            while let Some(request) = cmd_rx.recv().await {
                let success = match request.command_type.as_str() {
                    "worker_quiesce" => {
                        let work = *work.lock().unwrap_or_else(PoisonError::into_inner);
                        gate.quiesce(work) == QuiesceAnswer::Quiesced
                    }
                    "worker_release" => {
                        gate.release();
                        true
                    }
                    _ => true,
                };
                let response = if success {
                    crate::protocol::response_success(None, &request.command_type, None)
                } else {
                    crate::protocol::response_failure(None, &request.command_type, "busy", None)
                };
                record
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .push(request.command_type.clone());
                if let Some(reply) = resident.pending.lock().await.remove(&request.request_id) {
                    let _ = reply.send(WorkerReply::Typed(response));
                }
            }
        });
        seen
    }

    /// Send `shutdown { ifIdle: true }` through a real client connection
    /// (`handle_client`) and answer the response.
    async fn idle_shutdown_over_the_wire(supervisor: &Arc<Supervisor>) -> DaemonResponse {
        let (server_side, client_side) = tokio::net::UnixStream::pair().expect("socket pair");
        {
            let supervisor = Arc::clone(supervisor);
            let stream: Box<dyn TransportStream> = Box::new(server_side);
            tokio::spawn(async move { supervisor.handle_client(stream).await });
        }
        let (client_read, mut client_write) = client_side.into_split();
        let mut client = BufReader::new(client_read);
        let mut hello = String::new();
        client.read_line(&mut hello).await.expect("hello line");
        let envelope = serde_json::json!({
            "type": "command",
            "id": "stop-1",
            "protocol": crate::protocol::current_protocol_info(),
            "command": {"type": "shutdown", "ifIdle": true},
        });
        client_write
            .write_all((envelope.to_string() + "\n").as_bytes())
            .await
            .expect("send the shutdown");
        loop {
            let mut line = String::new();
            client.read_line(&mut line).await.expect("a line");
            let value: serde_json::Value = serde_json::from_str(&line).expect("json line");
            if value["type"] == "response" {
                return serde_json::from_value(value).expect("a response");
            }
        }
    }

    /// F4: a run that started after the client last looked (between its
    /// `list` and its shutdown) is never aborted. The supervisor itself
    /// asks the worker, the worker answers busy, nothing stops, and the
    /// worker's gate is released.
    #[tokio::test]
    async fn an_idle_shutdown_never_stops_a_run_that_started_after_the_client_looked() {
        let dir = tempfile::TempDir::new().expect("temp dir");
        let supervisor = supervisor(dir.path());
        let work = Arc::new(Mutex::new(Work::Idle));
        let seen = faux_worker(&supervisor, Arc::clone(&work)).await;
        // The run starts after the client's look and before its shutdown.
        *work.lock().unwrap_or_else(PoisonError::into_inner) = Work::Ongoing;
        let response = idle_shutdown_over_the_wire(&supervisor).await;
        assert_eq!(
            response,
            DaemonResponse {
                id: Some("stop-1".to_string()),
                command: "shutdown".to_string(),
                success: false,
                data: None,
                error: Some("The daemon has work in flight; nothing was stopped".to_string()),
                error_info: Some(DaemonErrorInfo::DaemonBusy),
            }
        );
        assert!(!supervisor.shutting_down.load(Ordering::SeqCst));
        assert_eq!(
            *seen.lock().unwrap_or_else(PoisonError::into_inner),
            ["worker_quiesce", "worker_release"]
        );
    }

    /// When every worker is idle, the idle shutdown commits: every worker
    /// was asked once and none was released (their gates stay closed for
    /// the stop). The decision is driven directly: the stop pass itself is
    /// the plain shutdown's, and a faux worker has no process to stop.
    #[tokio::test]
    async fn an_idle_shutdown_of_idle_workers_commits() {
        let dir = tempfile::TempDir::new().expect("temp dir");
        let supervisor = supervisor(dir.path());
        let seen = faux_worker(&supervisor, Arc::new(Mutex::new(Work::Idle))).await;
        assert_eq!(
            supervisor.decide_idle_shutdown().await,
            IdleShutdown::Commit
        );
        assert_eq!(
            *seen.lock().unwrap_or_else(PoisonError::into_inner),
            ["worker_quiesce"]
        );
    }

    /// A worker launch in flight (its create replay may resume a run)
    /// makes the idle shutdown busy; once it ended, the shutdown commits.
    #[tokio::test]
    async fn a_launch_in_flight_makes_an_idle_shutdown_busy() {
        let dir = tempfile::TempDir::new().expect("temp dir");
        let supervisor = supervisor(dir.path());
        let launch = supervisor.replacement_gate.enter_launch().await;
        assert_eq!(supervisor.decide_idle_shutdown().await, IdleShutdown::Busy);
        drop(launch);
        assert_eq!(
            supervisor.decide_idle_shutdown().await,
            IdleShutdown::Commit
        );
    }
}
