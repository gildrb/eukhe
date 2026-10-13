//! `get_worker_liveness`: the supervisor's process-level verdict on the
//! worker that hosts one session. Liveness comes from the process (its pid
//! and start identity, the lease's own owner rule), never from a request
//! queue: a worker too busy to answer a route is still `Live`, so a parent
//! never settles a slow child as gone because its polls failed.

use eukhe_types::daemon::WorkerLiveness;

use super::{json, response_success, DaemonResponse, Ordering, Supervisor};

impl Supervisor {
    /// Answer the verdict for `selector` without routing to its worker.
    /// No resident is `Gone`; a resident whose process lives is `Live`
    /// (a stopping worker included, until its process is gone); a dead
    /// process the supervisor is still relaunching is `Recovering`, and
    /// one it stopped or gave up on is `Gone`.
    #[tracing::instrument(skip(self))]
    pub(super) async fn handle_get_worker_liveness(
        &self,
        command_id: &str,
        type_name: &str,
        selector: &str,
    ) -> DaemonResponse {
        let resident = match self.registry.resolve(selector).await {
            Ok(resident) => Some(resident),
            Err(_) => self.binding_target(selector).await,
        };
        let liveness = match resident {
            None => WorkerLiveness::Gone,
            Some(resident) => {
                let (pid, start_id) = {
                    let descriptor = resident.descriptor.lock().await;
                    (
                        u32::try_from(descriptor.pid).unwrap_or(0),
                        descriptor.process_start_id.clone(),
                    )
                };
                // The lease's owner rule: a provably dead or recycled pid
                // is gone; an unobservable one counts as alive.
                let alive = pid != 0
                    && crate::lease::is_process_alive(pid).unwrap_or(true)
                    && start_id.as_deref().is_none_or(|expected| {
                        crate::lease::get_process_start_id(pid)
                            .is_none_or(|current| current == expected)
                    });
                let stopped = resident.route_state().retired
                    || resident.intentional_stop.load(Ordering::SeqCst)
                    || self.shutting_down.load(Ordering::SeqCst);
                match (alive, stopped) {
                    (true, _) => WorkerLiveness::Live,
                    (false, false) => WorkerLiveness::Recovering,
                    (false, true) => WorkerLiveness::Gone,
                }
            }
        };
        response_success(
            Some(command_id),
            type_name,
            Some(json!({ "liveness": liveness })),
        )
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use eukhe_types::daemon::{DaemonWorkerDescriptor, WorkerLiveness};
    use serde_json::json;

    use crate::registry::ResidentWorker;
    use crate::supervisor::{Supervisor, SupervisorOptions};

    fn resident(worker_id: &str, pid: u32) -> Arc<ResidentWorker> {
        let descriptor: DaemonWorkerDescriptor = serde_json::from_value(json!({
            "version": 2,
            "workerId": worker_id,
            "pid": pid,
            "processStartId": crate::lease::get_process_start_id(pid),
            "socketPath": "/tmp/none.sock",
            "recoveryJournalPath": "/tmp/none.jsonl",
            "supervisorSocketPath": "/tmp/none.sock",
            "authenticationToken": "test",
            "rootActiveSessionId": worker_id,
            "createdAt": "t",
            "updatedAt": "t",
            "lifecycle": "ready",
            "createCommand": {},
            "consecutiveFailures": 0,
        }))
        .expect("descriptor");
        ResidentWorker::new(
            worker_id.to_string(),
            descriptor,
            std::path::PathBuf::from("/tmp/none.descriptor.json"),
        )
    }

    async fn verdict(supervisor: &Supervisor, selector: &str) -> WorkerLiveness {
        let response = supervisor
            .handle_get_worker_liveness("l-1", "get_worker_liveness", selector)
            .await;
        assert!(response.success, "{response:?}");
        serde_json::from_value(response.data.expect("data")["liveness"].clone())
            .expect("typed verdict")
    }

    /// The verdict follows the worker process: a live pid is `Live` however
    /// its routes fare, a dead one is `Recovering` while the supervisor
    /// still owns its relaunch and `Gone` once it stopped, and a session no
    /// resident hosts is `Gone`.
    #[tokio::test]
    async fn the_verdict_follows_the_worker_process() {
        let dir = tempfile::TempDir::new().expect("temp dir");
        let supervisor = Supervisor::new(SupervisorOptions {
            socket_path: dir.path().join("daemon.sock"),
            agent_dir: dir.path().join("agent"),
        })
        .expect("supervisor");
        let mut worker = std::process::Command::new("sleep")
            .arg("30")
            .spawn()
            .expect("spawn a stand-in worker process");
        let live = resident("w-live", worker.id());
        supervisor.registry.insert(Arc::clone(&live)).await;
        assert_eq!(verdict(&supervisor, "w-live").await, WorkerLiveness::Live);

        worker.kill().expect("kill the stand-in");
        worker.wait().expect("reap the stand-in");
        assert_eq!(
            verdict(&supervisor, "w-live").await,
            WorkerLiveness::Recovering
        );
        live.note_retired();
        assert_eq!(verdict(&supervisor, "w-live").await, WorkerLiveness::Gone);
        assert_eq!(
            verdict(&supervisor, "no-such-session").await,
            WorkerLiveness::Gone
        );
    }
}
