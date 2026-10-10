//! The getter test battery: the TS wire shapes of every `get_*` handler
//! over an in-process worker hosting a scripted (faux) durable session.

use std::path::Path;
use std::sync::Arc;

use serde_json::{json, Value};

use crate::worker::{Worker, WorkerConfig};

fn worker_config(dir: &Path, script: Value) -> WorkerConfig {
    WorkerConfig {
        socket_path: dir.join("worker.sock"),
        supervisor_socket_path: std::path::PathBuf::new(),
        token: "token".to_string(),
        worker_instance_id: String::new(),
        active_session_id: "getter-session".to_string(),
        agent_dir: dir.join("agent"),
        recovery_journal_path: dir.join("recovery.jsonl"),
        telemetry_disabled: Some(true),
        script: Some(script),
    }
}

/// A created, named in-memory session on `dir` running `script`.
async fn created_worker(dir: &Path, script: Value) -> Arc<Worker> {
    std::fs::create_dir_all(dir.join("agent")).expect("agent dir");
    let worker = Arc::new(Worker::new(worker_config(dir, script), None));
    let created = worker
        .dispatch(
            "create",
            &json!({ "noSession": true, "cwd": dir, "name": "getters" }),
        )
        .await;
    assert!(created.success, "create failed: {created:?}");
    worker
}

fn ack_script() -> Value {
    json!({ "modelId": "faux-1", "responses": ["ack"] })
}

async fn get(worker: &Worker, command: &str, payload: &Value) -> Value {
    let response = worker.dispatch(command, payload).await;
    assert!(response.success, "{command} failed: {response:?}");
    response.data.expect("response data")
}

/// `get_connection_state` answers the TS `AgentConnectionState` block
/// with the daemon overlay (`heartbeat` present and null); an uncreated
/// session answers the initializing refusal.
#[tokio::test]
async fn get_connection_state_matches_the_ts_shape() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created_worker(dir.path(), ack_script()).await;
    let data = get(&worker, "get_connection_state", &json!({})).await;
    assert_eq!(data["activeSessionId"], "getter-session");
    assert_eq!(data["cwd"], json!(dir.path()));
    assert_eq!(data["heartbeat"], Value::Null);
    assert_eq!(data["model"]["id"], "faux-1");
    for field in [
        "thinkingLevel",
        "serviceTier",
        "availableThinkingLevels",
        "isStreaming",
        "isCompacting",
        "isBashRunning",
        "retryAttempt",
        "steeringMode",
        "followUpMode",
        "sessionId",
        "autoCompactionEnabled",
        "messageCount",
        "sessionActions",
        "compactionCount",
        "goal",
        "scopedModels",
        "activeToolNames",
    ] {
        assert!(data.get(field).is_some(), "missing {field}: {data}");
    }
    let fresh = Worker::new(worker_config(dir.path(), ack_script()), None);
    let response = fresh.dispatch("get_connection_state", &json!({})).await;
    assert!(!response.success);
    assert_eq!(
        response.error.as_deref(),
        Some("Session is still initializing")
    );
}

/// `get_context_tree`: the root node (label, model, the main
/// conversation's own spend and its per-model breakdown, no children on a
/// childless session); a turn's spend lands in the totals.
#[tokio::test]
async fn get_context_tree_matches_the_ts_root_node() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created_worker(dir.path(), ack_script()).await;
    let tree = get(&worker, "get_context_tree", &json!({})).await;
    assert_eq!(tree["id"], "root");
    assert_eq!(tree["label"], "getters");
    assert_eq!(tree["status"], "active");
    assert_eq!(tree["model"]["id"], "faux-1");
    assert_eq!(tree["children"], json!([]));
    assert_eq!(tree["ownUsage"]["input"], 0);
    assert_eq!(tree["ownUsage"], tree["totalUsage"]);
    assert_eq!(tree["ownUsageByModel"], json!([]));
    assert_eq!(tree["contextUsage"]["tokens"], 0);

    let answered = worker
        .dispatch("prompt_and_wait", &json!({ "message": "hello there" }))
        .await;
    assert!(answered.success, "prompt: {answered:?}");
    let tree = get(&worker, "get_context_tree", &json!({})).await;
    assert_eq!(tree["ownUsage"], tree["totalUsage"]);
    let by_model = tree["ownUsageByModel"].as_array().expect("by model");
    assert_eq!(by_model.len(), 1, "{tree}");
    assert_eq!(by_model[0]["id"], "faux-1");
    assert_eq!(by_model[0]["ownUsage"], tree["ownUsage"]);
    assert!(
        tree["contextUsage"]["tokens"]
            .as_u64()
            .is_some_and(|tokens| tokens > 0),
        "{tree}"
    );
}

/// The attach snapshot's state carries the tray's context usage (TS
/// `createAgentConnectionState`'s `contextUsage`), the same estimate
/// `get_session_stats` serves and `get_context_tree` derives through the
/// Harness, so the client's first frame needs no stats round-trip.
#[tokio::test]
async fn the_attach_state_carries_the_stats_context_usage() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created_worker(dir.path(), ack_script()).await;
    let usage_of = |worker: &Worker| {
        let core = worker
            .core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        serde_json::to_value(worker.connection_state_locked(&core)).expect("state")["contextUsage"]
            .clone()
    };
    let fresh = usage_of(&worker);
    assert_eq!(fresh["tokens"], 0, "{fresh}");
    assert!(fresh["contextWindow"]
        .as_u64()
        .is_some_and(|window| window > 0));

    let answered = worker
        .dispatch("prompt_and_wait", &json!({ "message": "hello there" }))
        .await;
    assert!(answered.success, "prompt: {answered:?}");
    let state_usage = usage_of(&worker);
    assert!(
        state_usage["tokens"]
            .as_u64()
            .is_some_and(|tokens| tokens > 0),
        "{state_usage}"
    );
    let stats = get(&worker, "get_session_stats", &json!({})).await;
    assert_eq!(stats["contextUsage"], state_usage);
    let tree = get(&worker, "get_context_tree", &json!({})).await;
    assert_eq!(tree["contextUsage"], state_usage);
}

/// `get_commands` / `get_resource_snapshot`: the TS loader shapes over the
/// session's loaded resources.
#[tokio::test]
async fn commands_and_resources_match_the_loader_shapes() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created_worker(dir.path(), ack_script()).await;
    let commands = get(&worker, "get_commands", &json!({})).await;
    for command in commands["commands"].as_array().expect("commands") {
        assert!(command["name"].is_string(), "{command}");
        assert!(
            matches!(command["source"].as_str(), Some("prompt" | "skill")),
            "{command}"
        );
    }
    let snapshot = get(&worker, "get_resource_snapshot", &json!({})).await;
    for key in ["contextFiles", "skills", "prompts", "themes"] {
        assert!(snapshot[key].is_array(), "missing {key}: {snapshot}");
    }
    assert!(snapshot["diagnostics"]["skills"].is_array(), "{snapshot}");
    for skill in snapshot["skills"].as_array().expect("skills") {
        assert!(
            skill["artifact"]["id"]
                .as_str()
                .is_some_and(|id| id.starts_with("artifact_")),
            "{skill}"
        );
    }
}

/// `get_session_context`: the main conversation's active context —
/// messages, effective thinking level, service tier, and model selector.
#[tokio::test]
async fn get_session_context_matches_the_ts_context_shape() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created_worker(dir.path(), ack_script()).await;
    let context = get(&worker, "get_session_context", &json!({})).await["context"].clone();
    assert_eq!(context["messages"], json!([]));
    assert_eq!(context["thinkingLevel"], "off");
    assert_eq!(context["serviceTier"], "default");
    assert_eq!(context["model"]["modelId"], "faux-1");
    assert!(context["model"]["provider"].is_string());

    let answered = worker
        .dispatch("prompt_and_wait", &json!({ "message": "hello" }))
        .await;
    assert!(answered.success, "prompt: {answered:?}");
    let context = get(&worker, "get_session_context", &json!({})).await["context"].clone();
    let roles: Vec<&str> = context["messages"]
        .as_array()
        .expect("messages")
        .iter()
        .filter_map(|message| message["role"].as_str())
        .collect();
    assert_eq!(roles, vec!["user", "custom", "assistant"], "{context}");
    assert_eq!(context["messages"][0]["content"], json!("hello"));
}

/// `get_system_prompt` renders exactly the prompt the next request sends:
/// the faux provider's `systemPrompt` entry echoes the request's system
/// prompt as its answer.
#[tokio::test]
async fn get_system_prompt_matches_the_request_prompt() {
    let dir = tempfile::tempdir().expect("tempdir");
    let script = json!({ "modelId": "faux-1", "responses": [{ "systemPrompt": true }] });
    let worker = created_worker(dir.path(), script).await;
    let prompt = get(&worker, "get_system_prompt", &json!({})).await["systemPrompt"]
        .as_str()
        .expect("systemPrompt")
        .to_string();
    assert!(!prompt.is_empty());
    let answered = worker
        .dispatch("prompt_and_wait", &json!({ "message": "echo" }))
        .await;
    assert!(answered.success, "prompt: {answered:?}");
    let echoed = get(&worker, "get_last_assistant_text", &json!({})).await["text"].clone();
    assert_eq!(echoed, json!(prompt));
    // The transcript now shows the sections; the render still agrees.
    let again = get(&worker, "get_system_prompt", &json!({})).await;
    assert_eq!(again["systemPrompt"], json!(prompt));
}

/// `get_tool_definition`: one offered tool's definition; an unknown name
/// omits the key (the TS `undefined`); a missing name fails.
#[tokio::test]
async fn get_tool_definition_matches_the_ts_shapes() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created_worker(dir.path(), ack_script()).await;
    let tool = worker
        .session
        .get()
        .expect("hosted")
        .main()
        .expect("main")
        .agent(&eukhe_chord::context::BACKGROUND_CONTEXT)
        .await
        .expect("agent")
        .tools
        .first()
        .map(|tool| (tool.name.clone(), tool.description.clone()))
        .expect("the session offers tools");
    let data = get(&worker, "get_tool_definition", &json!({ "name": tool.0 })).await;
    let definition = &data["toolDefinition"];
    assert_eq!(definition["name"], json!(tool.0));
    assert_eq!(definition["label"], json!(tool.0));
    assert_eq!(definition["description"], json!(tool.1));
    assert!(definition["parameters"].is_object(), "{definition}");

    let data = get(
        &worker,
        "get_tool_definition",
        &json!({ "name": "no-such-tool" }),
    )
    .await;
    assert_eq!(data, json!({}));
    let response = worker.dispatch("get_tool_definition", &json!({})).await;
    assert!(!response.success);
    assert_eq!(
        response.error.as_deref(),
        Some("get_tool_definition requires a name")
    );
}

/// `get_chat_view`: a scripted session keeps no chat memory.
#[tokio::test]
async fn chat_view_is_null_without_chat_memory() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created_worker(dir.path(), ack_script()).await;
    let data = get(&worker, "get_chat_view", &json!({})).await;
    assert_eq!(data, json!({ "view": null }));
}

/// `get_available_models`: the session's models with credentials (the
/// scripted provider's model).
#[tokio::test]
async fn available_models_list_the_session_models() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created_worker(dir.path(), ack_script()).await;
    let data = get(&worker, "get_available_models", &json!({})).await;
    let models = data["models"].as_array().expect("models");
    assert!(
        models.iter().any(|model| model["id"] == json!("faux-1")),
        "{data}"
    );
}
