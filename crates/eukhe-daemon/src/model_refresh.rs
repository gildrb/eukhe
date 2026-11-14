//! `refresh_models`: the explicit model-list refresh a client asks for
//! (`/models refresh`). The worker asks the providers' listing endpoints
//! (`eukhe_core::models::refresh`), the refreshed models join this
//! session's collection, and the answer carries the report, its text lines
//! and the catalog after the refresh (the `get_model_catalog` payload).
//! Nothing else here sends a request.

use std::time::SystemTime;

use eukhe_core::models::refresh::{local_clock, refresh_models, report_lines, ProviderSelection};
use serde_json::{json, Value};

use crate::model_catalog::catalog_snapshot;
use crate::protocol::{response_failure, response_success, DaemonResponse};
use crate::worker::Worker;

const COMMAND: &str = "refresh_models";

/// The providers a `refresh_models` payload names: every signed-in one
/// when it names none.
fn selection(payload: &Value) -> ProviderSelection {
    let named: Vec<String> = payload
        .get("providers")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .filter_map(Value::as_str)
        .map(str::to_owned)
        .collect();
    if named.is_empty() {
        ProviderSelection::SignedIn
    } else {
        ProviderSelection::Named(named)
    }
}

impl Worker {
    /// `refresh_models`: refresh, join the new models into the session,
    /// answer the report and the catalog.
    #[tracing::instrument(skip_all)]
    pub(crate) async fn handle_refresh_models(&self, payload: &Value) -> DaemonResponse {
        let hosted = match self.hosted(COMMAND) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let agent_dir = self.config.agent_dir.clone();
        // A fresh collection: the credentials as they are now.
        let loaded = eukhe_core::durable::create_models(&agent_dir);
        eukhe_core::durable::budget::wrap_models_with_budget(
            &loaded.models,
            &eukhe_core::durable::budget::BudgetGate::daemon(&agent_dir),
        );
        let refreshed = match refresh_models(
            &agent_dir,
            &loaded.models,
            &selection(payload),
            SystemTime::now(),
        )
        .await
        {
            Ok(refreshed) => refreshed,
            Err(error) => return response_failure(None, COMMAND, &format!("{error:#}"), None),
        };
        eukhe_core::durable::join_refreshed_models(&hosted.deps().models, &refreshed.models);
        let lines = report_lines(
            &refreshed.report,
            &local_clock(&refreshed.report.refreshed_at),
        );
        let mut data = catalog_snapshot(&agent_dir);
        if let Value::Object(object) = &mut data {
            object.insert("report".to_owned(), json!(refreshed.report));
            object.insert("lines".to_owned(), json!(lines));
        }
        response_success(None, COMMAND, Some(data))
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;
    use std::sync::Arc;

    use eukhe_types::models_refresh::{
        AddedModel, ModelsRefreshReport, ProviderRefresh, RefreshOutcome,
    };
    use tokio::io::{AsyncReadExt, AsyncWriteExt};
    use tokio::net::TcpListener;

    use super::*;
    use crate::worker::WorkerConfig;

    /// Answers one request with `body` on a local port; returns the root
    /// URL.
    async fn serve_once(body: Value) -> String {
        let listener = TcpListener::bind("127.0.0.1:0").await.expect("bind");
        let root = format!("http://{}", listener.local_addr().expect("address"));
        tokio::spawn(async move {
            let (mut socket, _) = listener.accept().await.expect("accept");
            let mut received = Vec::new();
            let mut buffer = [0_u8; 4096];
            while !received.windows(4).any(|window| window == b"\r\n\r\n") {
                let read = socket.read(&mut buffer).await.expect("read");
                assert!(read > 0, "the client closed before the request head");
                received.extend_from_slice(&buffer[..read]);
            }
            let text = body.to_string();
            let response = format!(
                "HTTP/1.1 200 OK\r\ncontent-type: application/json\r\ncontent-length: {}\r\nconnection: close\r\n\r\n{text}",
                text.len()
            );
            socket.write_all(response.as_bytes()).await.expect("write");
            socket.shutdown().await.ok();
        });
        root
    }

    async fn created_worker(dir: &Path) -> Arc<Worker> {
        let worker = Arc::new(Worker::new(
            WorkerConfig {
                socket_path: dir.join("worker.sock"),
                supervisor_socket_path: std::path::PathBuf::new(),
                token: "token".to_string(),
                worker_instance_id: String::new(),
                active_session_id: "refresh-session".to_string(),
                agent_dir: dir.join("agent"),
                recovery_journal_path: dir.join("recovery.jsonl"),
                script: None,
            },
            None,
        ));
        let created = worker
            .dispatch("create", &json!({ "noSession": true, "cwd": dir }))
            .await;
        assert!(created.success, "create failed: {created:?}");
        worker
    }

    #[tokio::test]
    async fn a_refresh_answers_the_report_and_the_session_selects_the_new_model() {
        let dir = tempfile::tempdir().expect("tempdir");
        let agent = dir.path().join("agent");
        std::fs::create_dir_all(&agent).expect("agent dir");
        let root = serve_once(json!({
            "data": [
                { "id": "claude-haiku-5-5", "display_name": "Claude Haiku 5.5" },
                { "id": "claude-haiku-5-5-daemon", "display_name": "Daemon Listed" }
            ],
            "has_more": false
        }))
        .await;
        std::fs::write(
            agent.join("models.json"),
            json!({ "providers": { "anthropic": { "baseUrl": root, "apiKey": "sk-test" } } })
                .to_string(),
        )
        .expect("models.json");
        let worker = created_worker(dir.path()).await;
        let answer = worker
            .dispatch(COMMAND, &json!({ "providers": ["anthropic"] }))
            .await;
        assert!(answer.success, "refresh failed: {answer:?}");
        let data = answer.data.expect("data");
        let report: ModelsRefreshReport =
            serde_json::from_value(data["report"].clone()).expect("report");
        let lines: Vec<String> = serde_json::from_value(data["lines"].clone()).expect("lines");
        let listed_in_catalog = data["models"].as_array().is_some_and(|models| {
            models.iter().any(|model| {
                model["provider"] == "anthropic" && model["id"] == "claude-haiku-5-5-daemon"
            })
        });
        let session_model = worker
            .hosted(COMMAND)
            .expect("hosted")
            .deps()
            .models
            .get_model("anthropic", "claude-haiku-5-5-daemon")
            .map(|model| model.name);
        assert_eq!(
            (
                report.providers,
                lines.get(1..).map(<[String]>::to_vec),
                listed_in_catalog,
                session_model,
            ),
            (
                vec![ProviderRefresh {
                    provider: "anthropic".to_owned(),
                    outcome: RefreshOutcome::Refreshed {
                        added: vec![AddedModel {
                            id: "claude-haiku-5-5-daemon".to_owned(),
                            name: "Daemon Listed".to_owned(),
                        }],
                        known: 1,
                    },
                }],
                Some(vec![
                    "anthropic: 1 new, 1 already known".to_owned(),
                    "  anthropic/claude-haiku-5-5-daemon  Daemon Listed".to_owned(),
                ]),
                true,
                Some("Daemon Listed".to_owned()),
            )
        );
    }

    #[test]
    fn a_payload_without_providers_selects_the_signed_in_ones() {
        assert_eq!(
            (
                selection(&json!({})),
                selection(&json!({ "providers": ["openai-codex"] }))
            ),
            (
                ProviderSelection::SignedIn,
                ProviderSelection::Named(vec!["openai-codex".to_owned()])
            )
        );
    }
}
