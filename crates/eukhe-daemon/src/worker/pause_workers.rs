//! `pause_workers` / `resume_workers`: pause or resume a session's worker
//! tree. Without `ownRun` (a client on main): main's workers and their
//! trees (`eukhe_core::durable::children::pause_workers`); main keeps
//! talking. With `ownRun` (a parent on its child): this session's own run
//! and every child with work in flight
//! (`eukhe_core::durable::children::pause_own_tree`). A pause cancels
//! nothing: running model requests and tool calls finish, and the next
//! request, tool call or spawn waits. The reply is `{workers}`, this
//! session's worker rows after the change.

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_core::durable::children::{list_workers, pause_own_tree, pause_workers, PauseAction};
use serde_json::{json, Value};

use super::{response_failure, response_success, Worker};
use crate::protocol::DaemonResponse;

impl Worker {
    pub(crate) async fn handle_pause_workers(
        &self,
        payload: &Value,
        action: PauseAction,
    ) -> DaemonResponse {
        let command = match action {
            PauseAction::Pause => "pause_workers",
            PauseAction::Resume => "resume_workers",
        };
        let hosted = match self.hosted(command) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let main = match hosted.main() {
            Ok(main) => main,
            Err(error) => return response_failure(None, command, &error.to_string(), None),
        };
        let Some(host) = hosted.deps().children.clone() else {
            return response_failure(
                None,
                command,
                "This session has no child runtime: it has no workers",
                None,
            );
        };
        let cx = &BACKGROUND_CONTEXT;
        let own_run = payload.get("ownRun").and_then(Value::as_bool) == Some(true);
        let workers = if own_run {
            match pause_own_tree(
                hosted.harness(),
                host.as_ref(),
                &hosted.deps().run_pause,
                main.id(),
                action,
                cx,
            )
            .await
            {
                Ok(()) => list_workers(hosted.harness(), main.id(), cx)
                    .await
                    .map_err(anyhow::Error::new),
                Err(error) => Err(error),
            }
        } else {
            pause_workers(hosted.harness(), host.as_ref(), main.id(), action, cx).await
        };
        match workers {
            Ok(workers) => {
                self.push_roster_delta();
                response_success(None, command, Some(json!({ "workers": workers })))
            }
            Err(error) => response_failure(None, command, &format!("{error:#}"), None),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;
    use std::sync::{Arc, Mutex};
    use std::time::Duration;

    use eukhe_types::platform::transport::bind_transport;
    use serde_json::{json, Value};
    use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
    use tokio::sync::Notify;

    use crate::protocol::response_success;
    use crate::worker::{Worker, WorkerConfig};

    /// A supervisor stand-in at `socket` that answers every command with
    /// success and keeps the `resume_workers` ones.
    async fn supervisor(socket: PathBuf) -> (Arc<Mutex<Vec<Value>>>, Arc<Notify>) {
        let listener = bind_transport(&socket, eukhe_bend::rules::fsmode::peer_verdict)
            .await
            .unwrap();
        let (resumes, arrival) = (Arc::<Mutex<Vec<Value>>>::default(), Arc::new(Notify::new()));
        let (kept, told) = (Arc::clone(&resumes), Arc::clone(&arrival));
        tokio::spawn(async move {
            while let Ok(stream) = listener.accept().await {
                let (kept, told) = (Arc::clone(&kept), Arc::clone(&told));
                tokio::spawn(async move {
                    let (reader, mut writer) = stream.split();
                    let mut reader = BufReader::new(reader);
                    writer
                        .write_all(
                            b"{\"type\":\"daemon_hello\",\"protocol\":{\"name\":\"eukhe.daemon\",\"version\":7}}\n",
                        )
                        .await
                        .unwrap();
                    let mut line = String::new();
                    while reader.read_line(&mut line).await.unwrap_or(0) != 0 {
                        let value: Value = serde_json::from_str(line.trim()).unwrap();
                        line.clear();
                        let id = value["id"].as_str().unwrap_or_default().to_owned();
                        let command = value["command"].clone();
                        let name = command["type"].as_str().unwrap_or_default().to_owned();
                        if name == "resume_workers" {
                            kept.lock().unwrap().push(command);
                            told.notify_one();
                        }
                        let mut answer =
                            serde_json::to_string(&response_success(Some(&id), &name, None))
                                .unwrap();
                        answer.push('\n');
                        if writer.write_all(answer.as_bytes()).await.is_err() {
                            return;
                        }
                    }
                });
            }
        });
        (resumes, arrival)
    }

    /// The user's `@worker` message wakes main's paused worker: the worker
    /// tells main, whose tree pause ends, so main's `workers` row follows
    /// the worker's real state.
    #[tokio::test]
    async fn a_message_that_wakes_the_worker_ends_mains_pause() {
        let dir = tempfile::tempdir().expect("tempdir");
        let socket = dir.path().join("supervisor.sock");
        let (resumes, arrival) = supervisor(socket.clone()).await;
        std::fs::create_dir_all(dir.path().join("agent")).expect("agent dir");
        let worker = Arc::new(Worker::new(
            WorkerConfig {
                socket_path: dir.path().join("worker.sock"),
                supervisor_socket_path: socket,
                token: "token".to_string(),
                worker_instance_id: String::new(),
                active_session_id: "worker-child".to_string(),
                agent_dir: dir.path().join("agent"),
                recovery_journal_path: dir.path().join("recovery.jsonl"),
                script: Some(json!({ "modelId": "faux-1", "responses": ["on it"] })),
            },
            None,
        ));
        let created = worker
            .dispatch(
                "create",
                &json!({
                    "cwd": dir.path(),
                    "sessionDir": dir.path().join("sessions"),
                    "rlmDepth": 1,
                    "rlmMaxDepth": 3,
                    "parentSessionPath": dir.path().join("main-session"),
                    "runtimeMetadata": {
                        "kind": "subagent",
                        "rlmChildId": "sub-0000c0de",
                        "parentActiveSessionId": "main-live",
                        "rlmDepth": 1,
                        "worker": true,
                    },
                }),
            )
            .await;
        assert!(created.success, "create failed: {created:?}");
        // Main paused its tree (`ownRun` on its worker).
        let paused = worker
            .dispatch("pause_workers", &json!({ "ownRun": true }))
            .await;
        assert!(paused.success, "pause failed: {paused:?}");
        assert!(resumes.lock().unwrap().is_empty());

        let prompted = worker
            .dispatch("prompt", &json!({ "message": "go on, please" }))
            .await;
        assert!(prompted.success, "prompt failed: {prompted:?}");
        tokio::time::timeout(Duration::from_secs(20), arrival.notified())
            .await
            .expect("the worker tells main");
        assert_eq!(
            *resumes.lock().unwrap(),
            vec![json!({ "type": "resume_workers", "activeSessionId": "main-live" })]
        );
    }
}
