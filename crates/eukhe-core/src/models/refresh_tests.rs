use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use serde_json::{json, Value};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpListener;

use super::*;

/// 2026-11-14T10:00:00.000Z.
fn now() -> SystemTime {
    UNIX_EPOCH + Duration::from_hours(498_514)
}

/// The built-in `anthropic` model the overlays below are built from.
fn haiku() -> Model {
    ModelRegistry::built_in_catalog_models()
        .iter()
        .find(|model| model.provider == "anthropic" && model.id == "claude-haiku-5-5")
        .cloned()
        .expect("claude-haiku-5-5 in the built-in catalog")
}

fn renamed(model: &Model, id: &str, name: &str) -> Model {
    Model {
        id: id.to_owned(),
        name: name.to_owned(),
        ..model.clone()
    }
}

fn write_overlay(dir: &Path, models: Vec<Model>) {
    let overlay = RefreshOverlay {
        refreshed_at: "2026-11-13T09:00:00.000Z".to_owned(),
        providers: BTreeMap::from([("anthropic".to_owned(), models)]),
        offered: BTreeMap::new(),
    };
    std::fs::write(
        dir.join(OVERLAY_FILE_NAME),
        serde_json::to_string(&overlay).expect("json"),
    )
    .expect("write overlay");
}

#[test]
fn the_registry_and_the_session_add_the_overlay_and_keep_the_pinned_entries() {
    let dir = tempfile::tempdir().expect("tempdir");
    let haiku = haiku();
    write_overlay(
        dir.path(),
        vec![
            renamed(&haiku, "claude-haiku-5-5", "Overlay copy"),
            renamed(&haiku, "claude-refresh-test", "Refresh Test"),
        ],
    );
    let registry = ModelRegistry::create(
        AuthStorage::create(dir.path()),
        dir.path().join("models.json"),
    );
    let find = |id: &str| -> Vec<Model> {
        registry
            .get_all()
            .filter(|model| model.provider == "anthropic" && model.id == id)
            .cloned()
            .collect()
    };
    assert_eq!(
        (find("claude-haiku-5-5"), find("claude-refresh-test")),
        (
            vec![haiku.clone()],
            vec![renamed(&haiku, "claude-refresh-test", "Refresh Test")]
        )
    );
    let session = crate::durable::create_models(dir.path());
    assert_eq!(
        (
            session
                .models
                .get_model("anthropic", "claude-refresh-test")
                .map(|model| model.name),
            session
                .models
                .get_model("anthropic", "claude-haiku-5-5")
                .map(|model| model.name),
        ),
        (Some("Refresh Test".to_owned()), Some(haiku.name))
    );
}

#[test]
fn a_damaged_overlay_counts_as_empty() {
    let dir = tempfile::tempdir().expect("tempdir");
    std::fs::write(dir.path().join(OVERLAY_FILE_NAME), "{broken").expect("write");
    assert_eq!(load_overlay(dir.path()), RefreshOverlay::default());
}

#[test]
fn a_running_session_joins_the_refreshed_models() {
    let dir = tempfile::tempdir().expect("tempdir");
    let session = crate::durable::create_models(dir.path());
    let added = renamed(&haiku(), "claude-joined-test", "Joined");
    crate::durable::join_refreshed_models(&session.models, std::slice::from_ref(&added));
    assert_eq!(
        session
            .models
            .get_model("anthropic", "claude-joined-test")
            .map(|model| model.name),
        Some("Joined".to_owned())
    );
}

/// Answers one `GET` with `body` on a local port; returns the root URL
/// and the request line it received.
async fn serve_once(body: Value) -> (String, tokio::task::JoinHandle<String>) {
    let listener = TcpListener::bind("127.0.0.1:0").await.expect("bind");
    let root = format!("http://{}", listener.local_addr().expect("address"));
    let handle = tokio::spawn(async move {
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
        String::from_utf8_lossy(&received)
            .lines()
            .next()
            .unwrap_or_default()
            .to_owned()
    });
    (root, handle)
}

#[tokio::test]
async fn a_refresh_saves_the_new_models_and_reports_each_provider() {
    let dir = tempfile::tempdir().expect("tempdir");
    let (root, server) = serve_once(json!({
        "data": [
            { "id": "claude-haiku-5-5", "display_name": "Claude Haiku 5.5" },
            {
                "id": "claude-haiku-5-5-refresh",
                "display_name": "Claude Refresh New",
                "max_input_tokens": 300_000,
                "max_tokens": 50_000
            }
        ],
        "has_more": false
    }))
    .await;
    std::fs::write(
        dir.path().join("models.json"),
        json!({ "providers": { "anthropic": { "baseUrl": root, "apiKey": "sk-test" } } })
            .to_string(),
    )
    .expect("models.json");
    let session = crate::durable::create_models(dir.path());
    let refreshed = refresh_models(
        dir.path(),
        &session.models,
        &ProviderSelection::Named(vec![
            "anthropic".to_owned(),
            "xai".to_owned(),
            "no-such-provider".to_owned(),
        ]),
        now(),
    )
    .await
    .expect("refresh");
    let added = Model {
        context_window: 300_000,
        max_tokens: 50_000,
        featured: None,
        ..renamed(&haiku(), "claude-haiku-5-5-refresh", "Claude Refresh New")
    };
    assert_eq!(
        refreshed,
        Refreshed {
            report: ModelsRefreshReport {
                refreshed_at: "2026-11-14T10:00:00.000Z".to_owned(),
                providers: vec![
                    ProviderRefresh {
                        provider: "anthropic".to_owned(),
                        outcome: RefreshOutcome::Refreshed {
                            added: vec![AddedModel {
                                id: "claude-haiku-5-5-refresh".to_owned(),
                                name: "Claude Refresh New".to_owned(),
                            }],
                            known: 1,
                        },
                    },
                    ProviderRefresh {
                        provider: "xai".to_owned(),
                        outcome: RefreshOutcome::Skipped {
                            reason: SkipReason::NotSignedIn,
                        },
                    },
                    ProviderRefresh {
                        provider: "no-such-provider".to_owned(),
                        outcome: RefreshOutcome::Skipped {
                            reason: SkipReason::NotInCatalog,
                        },
                    },
                ],
            },
            models: vec![added.clone()],
        }
    );
    assert_eq!(
        (server.await.expect("server"), load_overlay(dir.path())),
        (
            "GET /v1/models?limit=1000 HTTP/1.1".to_owned(),
            RefreshOverlay {
                refreshed_at: "2026-11-14T10:00:00.000Z".to_owned(),
                providers: BTreeMap::from([("anthropic".to_owned(), vec![added])]),
                offered: BTreeMap::from([(
                    "anthropic".to_owned(),
                    BTreeSet::from([
                        "claude-haiku-5-5".to_owned(),
                        "claude-haiku-5-5-refresh".to_owned(),
                    ]),
                )]),
            }
        )
    );
}

#[test]
fn the_report_reads_as_lines() {
    let report = ModelsRefreshReport {
        refreshed_at: "2026-11-14T10:00:00.000Z".to_owned(),
        providers: vec![
            ProviderRefresh {
                provider: "openai-codex".to_owned(),
                outcome: RefreshOutcome::Refreshed {
                    added: vec![AddedModel {
                        id: "gpt-6.2".to_owned(),
                        name: "GPT-6.2".to_owned(),
                    }],
                    known: 9,
                },
            },
            ProviderRefresh {
                provider: "xai".to_owned(),
                outcome: RefreshOutcome::Skipped {
                    reason: SkipReason::NoListingEndpoint,
                },
            },
            ProviderRefresh {
                provider: "nope".to_owned(),
                outcome: RefreshOutcome::Skipped {
                    reason: SkipReason::NotInCatalog,
                },
            },
            ProviderRefresh {
                provider: "google".to_owned(),
                outcome: RefreshOutcome::Failed {
                    error: "Google returned 403".to_owned(),
                },
            },
        ],
    };
    assert_eq!(
        (
            report_lines(&report, "11:00"),
            report_lines(
                &ModelsRefreshReport {
                    providers: Vec::new(),
                    ..report.clone()
                },
                "11:00"
            )
        ),
        (
            vec![
                "Model lists refreshed at 11:00".to_owned(),
                "openai-codex: 1 new, 9 already known".to_owned(),
                "  openai-codex/gpt-6.2  GPT-6.2".to_owned(),
                "xai: skipped: no model-listing endpoint".to_owned(),
                "nope: skipped: unknown provider".to_owned(),
                "google: failed: Google returned 403".to_owned(),
            ],
            vec!["No signed-in provider has a model-listing endpoint.".to_owned()]
        )
    );
}
