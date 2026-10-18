//! The live-settings switch battery over an in-process worker: scripted
//! (faux) sessions for the settings switches, and models.json sessions (no
//! script) for the model cycler's candidate lists.

use std::path::Path;
use std::sync::Arc;
use std::time::Duration;

use eukhe_core::settings::TransportSetting;
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

/// The settings of `worker`'s session (its own sets over the config).
fn session_settings(worker: &Worker) -> Arc<eukhe_core::settings::SettingsManager> {
    worker
        .session
        .get()
        .expect("a hosted session")
        .deps()
        .settings
        .manager()
}

/// The global settings documents of `dir`'s agent dir, as another process
/// would read them.
fn global_settings(dir: &Path) -> eukhe_core::settings::SettingsManager {
    eukhe_core::settings::SettingsManager::create(dir, dir.join("agent"))
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

/// `cycle_thinking_level { direction }` steps through the faux reasoning
/// ladder (off, minimal, low, medium, high) both ways and wraps; the
/// connection state shows each applied level.
#[tokio::test]
async fn cycle_thinking_level_steps_both_ways_and_wraps() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created_worker(dir.path(), Some(faux_script(true))).await;
    let mut shown = vec![connection_state(&worker).await["thinkingLevel"].clone()];
    for direction in ["backward", "forward", "forward", "forward", "backward"] {
        let response = worker
            .dispatch("cycle_thinking_level", &json!({ "direction": direction }))
            .await;
        assert!(response.success, "cycle {direction}: {response:?}");
        shown.push(connection_state(&worker).await["thinkingLevel"].clone());
    }
    assert_eq!(
        shown,
        ["medium", "low", "medium", "high", "off", "high"].map(|level| json!(level))
    );
}

/// Regression: an unset thinking level showed as `off` while the request
/// sent no level and the server thought at its own default. The shown
/// conversation without a level now shows `default`, never `off`.
#[tokio::test]
async fn an_unset_thinking_level_shows_as_default() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created_worker(dir.path(), Some(faux_script(true))).await;
    let hosted = worker.session.get().expect("a hosted session");
    hosted
        .main()
        .expect("main")
        .configure(
            eukhe_durable::harness::types::AgentChange {
                thinking_level: eukhe_durable::harness::types::FieldChange::Clear,
                ..eukhe_durable::harness::types::AgentChange::default()
            },
            &BACKGROUND_CONTEXT,
        )
        .await
        .expect("clear the level");
    hosted.events_delivered().await;
    assert_eq!(
        connection_state(&worker).await["thinkingLevel"],
        json!("default")
    );
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
        session_settings(&worker).get_default_service_tier(),
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

/// `set_transport` sets the session's transport; an unknown transport
/// fails the command.
#[tokio::test]
async fn set_transport_sets_the_session_transport() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created_worker(dir.path(), Some(faux_script(false))).await;
    let response = worker
        .dispatch("set_transport", &json!({ "transport": "websocket" }))
        .await;
    assert!(response.success, "failed: {response:?}");
    assert!(matches!(
        session_settings(&worker).get_transport(),
        TransportSetting::WebSocket
    ));
    let response = worker
        .dispatch("set_transport", &json!({ "transport": "teleport" }))
        .await;
    assert!(!response.success);
}

/// The queue-mode switches show on the connection state, and reject
/// values outside the TS vocabulary.
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

/// `set_auto_retry` sets the toggle the session's retry policy reads.
#[tokio::test]
async fn set_auto_retry_sets_the_session_toggle() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created_worker(dir.path(), Some(faux_script(false))).await;
    let response = worker
        .dispatch("set_auto_retry", &json!({ "enabled": false }))
        .await;
    assert!(response.success, "failed: {response:?}");
    assert_eq!(
        session_settings(&worker).cvars().value_of("retry.enabled"),
        Some(json!(false))
    );
    let response = worker.dispatch("set_auto_retry", &json!({})).await;
    assert!(!response.success);
}

/// Regression (S4 scope leak): the switches wrote the global
/// settings.json, so a switch in one session changed every other session
/// over the same agent dir. Now each is a set of a Local cvar in the
/// session's own layer: the session that switched shows it, another
/// session (and the global settings.json) keep their values.
#[tokio::test]
async fn a_switch_changes_only_its_own_session() {
    let dir = tempfile::tempdir().expect("tempdir");
    let switched = created_worker(dir.path(), Some(faux_script(false))).await;
    let other = created_worker(dir.path(), Some(faux_script(false))).await;
    for (command, payload) in [
        ("set_auto_compaction", json!({ "enabled": false })),
        ("set_auto_retry", json!({ "enabled": false })),
        ("set_steering_mode", json!({ "mode": "one-at-a-time" })),
        ("set_follow_up_mode", json!({ "mode": "all" })),
        ("set_transport", json!({ "transport": "sse" })),
    ] {
        let response = switched.dispatch(command, &payload).await;
        assert!(response.success, "{command} failed: {response:?}");
    }
    let shown = |state: &Value| {
        (
            state["autoCompactionEnabled"].clone(),
            state["steeringMode"].clone(),
            state["followUpMode"].clone(),
        )
    };
    assert_eq!(
        shown(&connection_state(&switched).await),
        (json!(false), json!("one-at-a-time"), json!("all"))
    );
    assert_eq!(
        shown(&connection_state(&other).await),
        (json!(true), json!("all"), json!("one-at-a-time"))
    );
    let values = |settings: &eukhe_core::settings::SettingsManager| {
        let cvars = settings.cvars();
        (cvars.value_of("retry.enabled"), cvars.value_of("transport"))
    };
    let unchanged = (Some(json!(true)), Some(json!("auto")));
    assert_eq!(
        values(&session_settings(&switched)),
        (Some(json!(false)), Some(json!("sse")))
    );
    assert_eq!(values(&session_settings(&other)), unchanged);
    assert_eq!(values(&global_settings(dir.path())), unchanged);
}

/// `cvar` runs a line into the session and answers its replicated values;
/// a session set of a Global cvar is rejected with kind `global` and
/// applies nothing of its line.
#[tokio::test]
async fn cvar_rejects_a_global_cvar_from_a_session() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created_worker(dir.path(), Some(faux_script(false))).await;
    let response = worker
        .dispatch(
            "cvar",
            &json!({ "line": "set transport sse; set rlmMaxDepth 3" }),
        )
        .await;
    let message = CvarError::Global {
        id: "rlmMaxDepth".to_string(),
    }
    .to_string();
    assert_eq!(
        response,
        DaemonResponse {
            id: None,
            command: "cvar".to_string(),
            success: false,
            data: Some(json!({ "kind": "global", "id": "rlmMaxDepth", "message": message })),
            error: Some(message.clone()),
            error_info: None,
        }
    );
    // The wire line drops `error` when `data` is present: the message
    // must reach the client in `data` (a TUI showed "unknown error").
    assert_eq!(
        crate::protocol::response_line(&response),
        json!({
            "type": "response",
            "command": "cvar",
            "success": false,
            "data": { "kind": "global", "id": "rlmMaxDepth", "message": message },
        })
    );
    assert!(matches!(
        session_settings(&worker).get_transport(),
        TransportSetting::Auto
    ));

    let response = worker
        .dispatch("cvar", &json!({ "line": "toggle compaction.enabled" }))
        .await;
    assert_eq!(
        response,
        response_success(
            None,
            "cvar",
            Some(json!({
                "values": session_settings(&worker).cvars().replicated(),
                "errors": [],
            }))
        )
    );
    assert_eq!(
        connection_state(&worker).await["autoCompactionEnabled"],
        json!(false)
    );
}

/// `cvar` with `global` writes the global config.cfg: every session over
/// the agent dir reads the value.
#[tokio::test]
async fn a_global_cvar_line_reaches_every_session() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created_worker(dir.path(), Some(faux_script(false))).await;
    let other = created_worker(dir.path(), Some(faux_script(false))).await;
    let response = worker
        .dispatch(
            "cvar",
            &json!({ "line": "set steeringMode one-at-a-time", "global": true }),
        )
        .await;
    assert!(response.success, "failed: {response:?}");
    assert_eq!(
        connection_state(&other).await["steeringMode"],
        json!("one-at-a-time")
    );
}

/// A spawned child (`rlmDepth` > 0) installs the create's `cvarFamily` as
/// its inherited layers: it starts with its parent's Local set,
/// `subagent.cfg` overrides it, and a Global cvar keeps the config's value
/// whatever the profile says.
#[tokio::test]
async fn a_child_inherits_its_parents_family_under_its_profile() {
    let dir = tempfile::tempdir().expect("tempdir");
    std::fs::create_dir_all(dir.path().join("agent")).expect("agent dir");
    let worker = Arc::new(Worker::new(
        worker_config(dir.path(), Some(faux_script(false))),
        None,
    ));
    create(
        &worker,
        &json!({
            "noSession": true,
            "cwd": dir.path(),
            "name": "scout",
            "rlmDepth": 1,
            "rlmMaxDepth": 3,
            "cvarFamily": [
                { "profile": [], "sets": [{ "id": "transport", "value": "sse" }] },
            ],
        }),
    )
    .await;
    let values = || {
        let cvars = session_settings(&worker).cvars().clone();
        (cvars.value_of("transport"), cvars.value_of("rlmMaxDepth"))
    };
    assert_eq!(values(), (Some(json!("sse")), Some(Value::Null)));
    std::fs::write(
        dir.path().join("agent/subagent.cfg"),
        "set transport web-socket\nset rlmMaxDepth 9\n",
    )
    .expect("subagent.cfg");
    assert_eq!(values(), (Some(json!("web-socket")), Some(Value::Null)));
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
