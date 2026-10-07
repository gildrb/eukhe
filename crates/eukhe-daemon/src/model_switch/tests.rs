//! The model/thinking switch battery over an in-process worker: a scripted
//! (faux) session for the allowlist and thinking flows, and a models.json
//! session (no script) for the sign-in refusal classes.

use std::path::Path;
use std::sync::Arc;

use serde_json::{json, Value};

use super::*;
use crate::worker::{Worker, WorkerConfig};

fn worker_config(dir: &Path, script: Option<Value>) -> WorkerConfig {
    WorkerConfig {
        socket_path: dir.join("worker.sock"),
        supervisor_socket_path: std::path::PathBuf::new(),
        token: "token".to_string(),
        worker_instance_id: String::new(),
        active_session_id: "switch-session".to_string(),
        agent_dir: dir.join("agent"),
        recovery_journal_path: dir.join("recovery.jsonl"),
        telemetry_disabled: Some(true),
        script,
    }
}

/// A created in-memory session on `dir` (cwd and agent dir under it).
async fn created_worker(dir: &Path, script: Option<Value>) -> Arc<Worker> {
    std::fs::create_dir_all(dir.join("agent")).expect("agent dir");
    let worker = Arc::new(Worker::new(worker_config(dir, script), None));
    let created = worker
        .dispatch("create", &json!({ "noSession": true, "cwd": dir }))
        .await;
    assert!(created.success, "create failed: {created:?}");
    worker
}

fn faux_script(reasoning: bool) -> Value {
    json!({ "modelId": "faux-1", "reasoning": reasoning, "responses": ["ack"] })
}

/// A models.json fixture: one signed-in provider (`apiKey`) with `mock-1`.
fn models_fixture(dir: &Path) {
    std::fs::create_dir_all(dir.join("agent")).expect("agent dir");
    std::fs::write(
        dir.join("agent").join("models.json"),
        json!({
            "providers": {
                "prime-inference": {
                    "api": "openai-completions",
                    "baseUrl": "http://127.0.0.1:9/v1",
                    "apiKey": "sk-test",
                    "models": [
                        { "id": "mock-1", "name": "Mock 1", "api": "openai-completions",
                          "baseUrl": "http://127.0.0.1:9/v1", "contextWindow": 128_000,
                          "maxTokens": 4096 }
                    ]
                }
            }
        })
        .to_string(),
    )
    .expect("write models.json");
}

fn write_settings(dir: &Path, settings: &Value) {
    std::fs::write(
        dir.join("agent").join("settings.json"),
        settings.to_string(),
    )
    .expect("write settings.json");
}

async fn connection_state(worker: &Worker) -> Value {
    let response = worker.dispatch("get_connection_state", &json!({})).await;
    assert!(response.success, "connection state: {response:?}");
    response.data.expect("connection state data")
}

/// The daemon model allowlist enforcement point: `set_model` refuses a
/// resolvable model outside settings `allowedModels` loudly (never a
/// fallback); an allowing allowlist (or none) switches.
#[tokio::test]
async fn set_model_refuses_models_outside_the_allowlist() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created_worker(dir.path(), Some(faux_script(false))).await;
    let provider = connection_state(&worker).await["model"]["provider"]
        .as_str()
        .expect("the scripted model's provider")
        .to_string();
    let set_model = json!({ "provider": provider, "modelId": "faux-1" });

    write_settings(dir.path(), &json!({ "allowedModels": ["anthropic/*"] }));
    let response = worker.dispatch("set_model", &set_model).await;
    assert!(!response.success);
    assert_eq!(response.command, "set_model");
    assert_eq!(
        response.error,
        Some(format!(
            "Model \"{provider}/faux-1\" is blocked by the daemon model allowlist (settings \"allowedModels\"); the daemon never falls back to a different model. Allow it in the settings or pick an allowed model."
        ))
    );

    // A matching glob opens the gate: the switch lands and answers the
    // catalog model.
    write_settings(
        dir.path(),
        &json!({ "allowedModels": [format!("{provider}/*")] }),
    );
    let response = worker.dispatch("set_model", &set_model).await;
    assert!(response.success, "allowed switch: {response:?}");
    assert_eq!(response.data.expect("model")["id"], "faux-1");

    // No allowlist configured: the gate is a no-op (TS parity), and the
    // switch persists the settings default.
    std::fs::remove_file(dir.path().join("agent").join("settings.json")).expect("remove");
    let response = worker.dispatch("set_model", &set_model).await;
    assert!(response.success, "unrestricted switch: {response:?}");
    let settings = SettingsManager::create(dir.path(), dir.path().join("agent"));
    assert_eq!(settings.get_default_provider(), Some(provider.as_str()));
    assert_eq!(settings.get_default_model(), Some("faux-1"));
    assert_eq!(connection_state(&worker).await["model"]["id"], "faux-1");
}

/// The `set_model` refusal for a catalog model whose provider is not
/// signed in carries the typed `errorInfo` (the provider id), so a client
/// offers the provider's sign-in flow; a genuinely absent model keeps the
/// TS refusal without `errorInfo`; a signed-in provider's model switches.
#[tokio::test]
async fn set_model_refuses_an_unsigned_in_provider_with_the_typed_sign_in_error() {
    let dir = tempfile::tempdir().expect("tempdir");
    models_fixture(dir.path());
    let worker = created_worker(dir.path(), None).await;
    let model_id = worker
        .session
        .get()
        .expect("hosted session")
        .deps()
        .models
        .get_models(Some("anthropic"))
        .first()
        .map(|model| model.id.clone())
        .expect("the built-in catalog lists anthropic models");

    let response = worker
        .dispatch(
            "set_model",
            &json!({ "provider": "anthropic", "modelId": model_id }),
        )
        .await;
    assert!(!response.success, "the unsigned provider refuses");
    assert_eq!(
        response.error.as_deref(),
        Some(
            "Provider \"anthropic\" is not signed in. Sign in to the provider (the TUI's /login command), then set the model again."
        )
    );
    assert_eq!(
        response.error_info,
        Some(
            eukhe_types::daemon::DaemonErrorInfo::ModelProviderUnauthenticated {
                provider: "anthropic".to_string(),
            }
        )
    );

    let response = worker
        .dispatch(
            "set_model",
            &json!({ "provider": "anthropic", "modelId": "no-such-model" }),
        )
        .await;
    assert!(!response.success);
    assert_eq!(
        response.error.as_deref(),
        Some("Model not found: anthropic/no-such-model")
    );
    assert_eq!(response.error_info, None);

    let response = worker
        .dispatch(
            "set_model",
            &json!({ "provider": "prime-inference", "modelId": "mock-1" }),
        )
        .await;
    assert!(response.success, "signed-in switch: {response:?}");
    assert_eq!(response.data.expect("model")["id"], "mock-1");

    let response = worker
        .dispatch("set_model", &json!({ "modelId": "mock-1" }))
        .await;
    assert_eq!(
        response.error.as_deref(),
        Some("set_model requires a provider")
    );
}

/// `set_thinking_level` on a reasoning model switches the level, persists
/// the settings default, and rejects values outside the TS vocabulary; a
/// model without reasoning clamps every request to `off`.
#[tokio::test]
async fn set_thinking_level_switches_clamps_and_persists() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created_worker(dir.path(), Some(faux_script(true))).await;
    let response = worker
        .dispatch("set_thinking_level", &json!({ "level": "high" }))
        .await;
    assert!(response.success, "set high: {response:?}");
    assert_eq!(connection_state(&worker).await["thinkingLevel"], "high");
    let settings = SettingsManager::create(dir.path(), dir.path().join("agent"));
    assert!(matches!(
        settings.get_default_thinking_level(),
        Some(ThinkingLevelSetting::High)
    ));

    let response = worker
        .dispatch("set_thinking_level", &json!({ "level": "sideways" }))
        .await;
    assert!(!response.success);
    assert_eq!(
        response.error.as_deref(),
        Some("Invalid thinking level \"sideways\". Valid values: off, minimal, low, medium, high, xhigh, max")
    );

    let plain_dir = tempfile::tempdir().expect("tempdir");
    let plain = created_worker(plain_dir.path(), Some(faux_script(false))).await;
    let response = plain
        .dispatch("set_thinking_level", &json!({ "level": "high" }))
        .await;
    assert!(response.success, "clamped set: {response:?}");
    assert_eq!(connection_state(&plain).await["thinkingLevel"], "off");
}

#[test]
fn thinking_levels_wire_names_match_the_enum() {
    for level in THINKING_LEVELS {
        assert!(
            ModelThinkingLevel::parse(level).is_some(),
            "{level} must parse"
        );
    }
    assert!(ModelThinkingLevel::parse("sideways").is_none());
}
