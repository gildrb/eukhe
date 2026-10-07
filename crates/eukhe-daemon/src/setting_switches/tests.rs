//! The live-settings switch battery over an in-process worker: scripted
//! (faux) sessions for the settings switches, and models.json sessions (no
//! script) for the model cycler's candidate lists.

use std::path::Path;
use std::sync::Arc;
use std::time::Duration;

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

async fn create(worker: &Worker, payload: &Value) {
    let created = worker.dispatch("create", payload).await;
    assert!(created.success, "create failed: {created:?}");
}

/// A created in-memory session on `dir` (cwd and agent dir under it).
async fn created_worker(dir: &Path, script: Option<Value>) -> Arc<Worker> {
    std::fs::create_dir_all(dir.join("agent")).expect("agent dir");
    let worker = Arc::new(Worker::new(worker_config(dir, script), None));
    create(&worker, &json!({ "noSession": true, "cwd": dir })).await;
    worker
}

fn faux_script(reasoning: bool) -> Value {
    json!({ "modelId": "faux-1", "reasoning": reasoning, "responses": ["ack"] })
}

/// A models.json fixture: one signed-in provider with `count` reasoning
/// mock models.
fn models_fixture(dir: &Path, count: usize) {
    std::fs::create_dir_all(dir.join("agent")).expect("agent dir");
    let models: Vec<Value> = (1..=count)
        .map(|index| {
            json!({
                "id": format!("mock-{index}"), "name": format!("Mock {index}"),
                "api": "openai-completions", "baseUrl": "http://127.0.0.1:9/v1",
                "contextWindow": 128_000, "maxTokens": 4096, "reasoning": true,
            })
        })
        .collect();
    std::fs::write(
        dir.join("agent").join("models.json"),
        json!({
            "providers": {
                "prime-inference": {
                    "api": "openai-completions",
                    "baseUrl": "http://127.0.0.1:9/v1",
                    "apiKey": "sk-test",
                    "models": models,
                }
            }
        })
        .to_string(),
    )
    .expect("write models.json");
}

async fn connection_state(worker: &Worker) -> Value {
    let response = worker.dispatch("get_connection_state", &json!({})).await;
    assert!(response.success, "connection state: {response:?}");
    response.data.expect("connection state data")
}

fn settings(dir: &Path) -> SettingsManager {
    SettingsManager::create(dir, dir.join("agent"))
}

/// The connection state carries the settings-seeded switches: the TS
/// default service tier ("default") and the queue modes (steering "all",
/// follow-up "one-at-a-time").
#[tokio::test]
async fn connection_state_seeds_the_settings_switches() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created_worker(dir.path(), Some(faux_script(false))).await;
    let data = connection_state(&worker).await;
    assert_eq!(data["serviceTier"], json!("default"));
    assert_eq!(data["steeringMode"], json!("all"));
    assert_eq!(data["followUpMode"], json!("one-at-a-time"));
    assert_eq!(data["scopedModels"], json!([]));
}

/// `cycle_model` steps through the available catalog (forward, then
/// backward back to the start) and answers the TS cycle shape; a session
/// with a single available model answers `null`.
#[tokio::test]
async fn cycle_model_steps_through_the_available_models() {
    let dir = tempfile::tempdir().expect("tempdir");
    models_fixture(dir.path(), 2);
    let worker = created_worker(dir.path(), None).await;
    let start = connection_state(&worker).await["model"]["id"].clone();
    let response = worker.dispatch("cycle_model", &json!({})).await;
    assert!(response.success, "cycle: {response:?}");
    let data = response.data.expect("cycle data");
    assert_eq!(data["isScoped"], json!(false));
    assert_eq!(data["serviceTier"], json!("default"));
    assert!(data["thinkingLevel"].is_string(), "{data}");
    let next = data["model"]["id"].clone();
    assert_ne!(next, start, "the cycle moved: {data}");
    assert_eq!(connection_state(&worker).await["model"]["id"], next);
    let response = worker
        .dispatch("cycle_model", &json!({ "direction": "backward" }))
        .await;
    assert!(response.success, "backward cycle: {response:?}");
    assert_eq!(connection_state(&worker).await["model"]["id"], start);

    let single_dir = tempfile::tempdir().expect("tempdir");
    let single = created_worker(single_dir.path(), Some(faux_script(false))).await;
    let response = single.dispatch("cycle_model", &json!({})).await;
    assert!(response.success);
    assert_eq!(response.data, Some(Value::Null));
}

/// `cycle_model` answers the daemon model-allowlist refusal with the loud
/// message and never switches. The scoped list pins the cycle to the two
/// fixture models.
#[tokio::test]
async fn cycle_model_refuses_models_outside_the_allowlist() {
    let dir = tempfile::tempdir().expect("tempdir");
    models_fixture(dir.path(), 2);
    let worker = created_worker(dir.path(), None).await;
    let start = connection_state(&worker).await["model"]["id"].clone();
    std::fs::write(
        dir.path().join("agent").join("settings.json"),
        json!({ "allowedModels": ["anthropic/*"] }).to_string(),
    )
    .expect("write settings.json");
    let scoped = worker
        .dispatch(
            "set_scoped_models",
            &json!({
                "scopedModels": [
                    { "model": { "provider": "prime-inference", "id": "mock-1" } },
                    { "model": { "provider": "prime-inference", "id": "mock-2" } }
                ]
            }),
        )
        .await;
    assert!(scoped.success, "scoped fixture: {scoped:?}");
    let response = worker.dispatch("cycle_model", &json!({})).await;
    assert!(!response.success);
    assert_eq!(response.command, "cycle_model");
    let error = response.error.expect("refusal message");
    assert!(
        error.contains("blocked by the daemon model allowlist"),
        "{error}"
    );
    assert_eq!(connection_state(&worker).await["model"]["id"], start);
}

/// A scoped entry's pinned thinking level rides the cycled-to model.
#[tokio::test]
async fn cycle_model_applies_the_scoped_thinking_level() {
    let dir = tempfile::tempdir().expect("tempdir");
    models_fixture(dir.path(), 2);
    let worker = created_worker(dir.path(), None).await;
    let current = connection_state(&worker).await["model"]["id"]
        .as_str()
        .expect("model id")
        .to_string();
    let other = if current == "mock-1" {
        "mock-2"
    } else {
        "mock-1"
    };
    let scoped = worker
        .dispatch(
            "set_scoped_models",
            &json!({
                "scopedModels": [
                    { "model": { "provider": "prime-inference", "id": current } },
                    {
                        "model": { "provider": "prime-inference", "id": other },
                        "thinkingLevel": "high",
                    }
                ]
            }),
        )
        .await;
    assert!(scoped.success, "scoped fixture: {scoped:?}");
    let response = worker.dispatch("cycle_model", &json!({})).await;
    assert!(response.success, "cycle: {response:?}");
    let data = response.data.expect("cycle data");
    assert_eq!(data["isScoped"], json!(true));
    assert_eq!(data["model"]["id"], json!(other));
    assert_eq!(data["thinkingLevel"], json!("high"));
    let state = connection_state(&worker).await;
    assert_eq!(state["thinkingLevel"], json!("high"), "{state}");
}

/// The create's `models` config resolves into the session's scoped list
/// in the request's order, and a create without `models` falls back to
/// the settings `enabledModels`.
#[tokio::test]
async fn create_resolves_the_models_scope_for_the_session() {
    let dir = tempfile::tempdir().expect("tempdir");
    models_fixture(dir.path(), 2);
    let worker = Arc::new(Worker::new(worker_config(dir.path(), None), None));
    create(
        &worker,
        &json!({
            "noSession": true,
            "cwd": dir.path(),
            "models": ["prime-inference/mock-2:high", "prime-inference/mock-1"],
        }),
    )
    .await;
    let data = connection_state(&worker).await;
    let ids: Vec<Value> = data["scopedModels"]
        .as_array()
        .expect("scopedModels")
        .iter()
        .map(|entry| entry["model"]["id"].clone())
        .collect();
    assert_eq!(ids, vec![json!("mock-2"), json!("mock-1")], "{data}");
    assert_eq!(data["scopedModels"][0]["thinkingLevel"], json!("high"));

    std::fs::write(
        dir.path().join("agent").join("settings.json"),
        json!({ "enabledModels": ["prime-inference/mock-1", "prime-inference/mock-2"] })
            .to_string(),
    )
    .expect("write settings.json");
    let fallback = Arc::new(Worker::new(worker_config(dir.path(), None), None));
    create(&fallback, &json!({ "noSession": true, "cwd": dir.path() })).await;
    let data = connection_state(&fallback).await;
    let ids: Vec<Value> = data["scopedModels"]
        .as_array()
        .expect("scopedModels")
        .iter()
        .map(|entry| entry["model"]["id"].clone())
        .collect();
    assert_eq!(ids, vec![json!("mock-1"), json!("mock-2")], "{data}");
}

/// `set_scoped_models` stores the list (visible on the connection state)
/// and rejects malformed entries.
#[tokio::test]
async fn set_scoped_models_stores_and_validates() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created_worker(dir.path(), Some(faux_script(false))).await;
    let scoped = json!([
        { "model": { "provider": "prime-inference", "id": "mock-1" } },
        {
            "model": { "provider": "prime-inference", "id": "mock-2" },
            "thinkingLevel": "high",
        },
    ]);
    let response = worker
        .dispatch("set_scoped_models", &json!({ "scopedModels": scoped }))
        .await;
    assert!(response.success, "failed: {response:?}");
    assert_eq!(connection_state(&worker).await["scopedModels"], scoped);
    for bad in [
        json!({}),
        json!({ "scopedModels": [{}] }),
        json!({
            "scopedModels": [{ "model": { "provider": "p", "id": "m" }, "thinkingLevel": "sideways" }],
        }),
    ] {
        let response = worker.dispatch("set_scoped_models", &bad).await;
        assert!(!response.success, "must reject: {bad}");
    }
}

/// `cycle_thinking_level` without a reasoning model answers `null`; a
/// reasoning model advances to its next supported level.
#[tokio::test]
async fn cycle_thinking_level_cycles_the_supported_levels() {
    let dir = tempfile::tempdir().expect("tempdir");
    let plain = created_worker(dir.path(), Some(faux_script(false))).await;
    let response = plain.dispatch("cycle_thinking_level", &json!({})).await;
    assert!(response.success);
    assert_eq!(response.data, Some(Value::Null));

    let reasoning_dir = tempfile::tempdir().expect("tempdir");
    let worker = created_worker(reasoning_dir.path(), Some(faux_script(true))).await;
    let before = connection_state(&worker).await["thinkingLevel"].clone();
    let response = worker.dispatch("cycle_thinking_level", &json!({})).await;
    assert!(response.success, "cycle: {response:?}");
    let level = response.data.expect("cycle data")["level"].clone();
    assert_ne!(level, before);
    assert_eq!(connection_state(&worker).await["thinkingLevel"], level);
}

/// `set_service_tier` keeps the REQUESTED preference while an unsupported
/// tier clamps the active state to `default` (TS #2144); the settings
/// default persists only for a supported tier; a missing tier fails.
#[tokio::test]
async fn set_service_tier_clamps_the_active_tier() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created_worker(dir.path(), Some(faux_script(false))).await;
    let response = worker
        .dispatch("set_service_tier", &json!({ "serviceTier": "priority" }))
        .await;
    assert!(response.success, "failed: {response:?}");
    assert_eq!(
        connection_state(&worker).await["serviceTier"],
        json!("default")
    );
    {
        let core = worker.core.lock().expect("core");
        assert_eq!(core.service_tier, Some(ServiceTier::Priority));
        assert_eq!(core.active_service_tier, Some(ServiceTier::Default));
    }
    assert_eq!(
        settings(dir.path()).get_default_service_tier(),
        ServiceTier::Default,
        "an unsupported tier never becomes the default"
    );
    let response = worker
        .dispatch("set_service_tier", &json!({ "serviceTier": "flex" }))
        .await;
    assert!(response.success, "failed: {response:?}");
    assert_eq!(
        worker.core.lock().expect("core").service_tier,
        Some(ServiceTier::Flex)
    );
    let response = worker.dispatch("set_service_tier", &json!({})).await;
    assert!(!response.success);
    assert_eq!(
        response.error.as_deref(),
        Some("set_service_tier requires a serviceTier")
    );
}

/// The replacement re-seed takes the settings default preference and
/// re-clamps the active tier against the shown model.
#[tokio::test]
async fn replacement_reseed_restores_the_settings_tier() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created_worker(dir.path(), Some(faux_script(false))).await;
    {
        let mut core = worker.core.lock().expect("core");
        core.service_tier = Some(ServiceTier::Priority);
        core.active_service_tier = Some(ServiceTier::Priority);
    }
    worker.reseed_service_tier_for_replacement();
    let core = worker.core.lock().expect("core");
    assert_eq!(core.service_tier, Some(ServiceTier::Default));
    assert_eq!(core.active_service_tier, Some(ServiceTier::Default));
}

/// `set_transport` persists the settings value; an unknown transport
/// fails the command.
#[tokio::test]
async fn set_transport_persists_the_setting() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created_worker(dir.path(), Some(faux_script(false))).await;
    let response = worker
        .dispatch("set_transport", &json!({ "transport": "websocket" }))
        .await;
    assert!(response.success, "failed: {response:?}");
    assert!(matches!(
        settings(dir.path()).get_transport(),
        TransportSetting::WebSocket
    ));
    let response = worker
        .dispatch("set_transport", &json!({ "transport": "teleport" }))
        .await;
    assert!(!response.success);
}

/// The queue-mode switches persist and show on the connection state, and
/// reject values outside the TS vocabulary.
#[tokio::test]
async fn queue_mode_switches_update_the_state() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created_worker(dir.path(), Some(faux_script(false))).await;
    for (command, field) in [
        ("set_steering_mode", "steeringMode"),
        ("set_follow_up_mode", "followUpMode"),
    ] {
        let response = worker
            .dispatch(command, &json!({ "mode": "one-at-a-time" }))
            .await;
        assert!(response.success, "{command} failed: {response:?}");
        assert_eq!(
            connection_state(&worker).await[field],
            json!("one-at-a-time")
        );
        let response = worker.dispatch(command, &json!({ "mode": "bogus" })).await;
        assert!(!response.success);
        assert_eq!(
            response.error,
            Some(format!(
                "{command} requires mode \"all\" or \"one-at-a-time\""
            ))
        );
        let response = worker.dispatch(command, &json!({ "mode": "all" })).await;
        assert!(response.success);
        assert_eq!(connection_state(&worker).await[field], json!("all"));
    }
}

/// `set_auto_retry` persists the toggle the retry policy reads.
#[tokio::test]
async fn set_auto_retry_persists_the_toggle() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created_worker(dir.path(), Some(faux_script(false))).await;
    let response = worker
        .dispatch("set_auto_retry", &json!({ "enabled": false }))
        .await;
    assert!(response.success, "failed: {response:?}");
    assert!(!settings(dir.path()).get_provider_retry_policy().enabled);
    let response = worker.dispatch("set_auto_retry", &json!({})).await;
    assert!(!response.success);
}

/// `set_auto_compaction` flips the connection-state flag through the
/// persisted setting; a session created afterwards reads it back.
#[tokio::test]
async fn set_auto_compaction_persists_the_toggle() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created_worker(dir.path(), Some(faux_script(false))).await;
    assert_eq!(
        connection_state(&worker).await["autoCompactionEnabled"],
        json!(true)
    );
    let response = worker
        .dispatch("set_auto_compaction", &json!({ "enabled": false }))
        .await;
    assert!(response.success, "failed: {response:?}");
    assert_eq!(
        connection_state(&worker).await["autoCompactionEnabled"],
        json!(false)
    );
    assert!(!settings(dir.path()).get_compaction_enabled());
    let restarted = created_worker(dir.path(), Some(faux_script(false))).await;
    assert_eq!(
        connection_state(&restarted).await["autoCompactionEnabled"],
        json!(false)
    );
}

/// A failed settings write fails the command and flips nothing.
#[tokio::test]
async fn set_auto_compaction_fails_without_flipping_on_a_failed_save() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created_worker(dir.path(), Some(faux_script(false))).await;
    // Replace the agent dir with a file: the settings save cannot create
    // agent/settings.json.
    std::fs::remove_dir_all(dir.path().join("agent")).expect("remove agent dir");
    std::fs::write(dir.path().join("agent"), b"not a directory").expect("agent file");
    let response = worker
        .dispatch("set_auto_compaction", &json!({ "enabled": false }))
        .await;
    assert!(!response.success, "must fail: {response:?}");
    assert_eq!(
        connection_state(&worker).await["autoCompactionEnabled"],
        json!(true)
    );
}

/// `abort_retry` without a retry in progress is a success no-op (TS aborts
/// only an in-flight retry).
#[tokio::test]
async fn abort_retry_without_a_retry_answers_success() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created_worker(dir.path(), Some(faux_script(false))).await;
    let response = worker.dispatch("abort_retry", &json!({})).await;
    assert!(response.success, "failed: {response:?}");
}

/// `abort_retry` during a provider retry stops the run: the scripted
/// provider fails with a retryable error, the retry waits out a long
/// backoff, and the abort ends the run without the retry's answer.
#[tokio::test]
async fn abort_retry_stops_an_in_flight_retry() {
    let dir = tempfile::tempdir().expect("tempdir");
    std::fs::create_dir_all(dir.path().join("agent")).expect("agent dir");
    std::fs::write(
        dir.path().join("agent").join("settings.json"),
        json!({ "retry": { "enabled": true, "maxRetries": 3, "baseDelayMs": 60_000 } }).to_string(),
    )
    .expect("write settings.json");
    let script = json!({
        "modelId": "faux-1",
        "responses": [
            { "stopReason": "error", "errorMessage": "429 rate limit exceeded" },
            "retried answer",
        ],
    });
    let worker = created_worker(dir.path(), Some(script)).await;
    let prompt = worker
        .dispatch("prompt", &json!({ "message": "hello" }))
        .await;
    assert!(prompt.success, "prompt: {prompt:?}");
    let retrying = tokio::time::timeout(Duration::from_secs(10), async {
        loop {
            if connection_state(&worker).await["retryAttempt"]
                .as_u64()
                .is_some_and(|attempt| attempt > 0)
            {
                break;
            }
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
    })
    .await;
    assert!(retrying.is_ok(), "the retry never started");
    let response = worker.dispatch("abort_retry", &json!({})).await;
    assert!(response.success, "abort_retry: {response:?}");
    let idle = tokio::time::timeout(Duration::from_secs(10), async {
        loop {
            if connection_state(&worker).await["isStreaming"] == json!(false) {
                break;
            }
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
    })
    .await;
    assert!(idle.is_ok(), "the run kept going after abort_retry");
    let last = worker.dispatch("get_last_assistant_text", &json!({})).await;
    assert_ne!(
        last.data.expect("last text")["text"],
        json!("retried answer"),
        "the retry never answered"
    );
}
