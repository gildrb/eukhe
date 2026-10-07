use std::sync::Arc;

use serde_json::json;

use crate::worker::Worker;

async fn created_worker() -> (tempfile::TempDir, Arc<Worker>) {
    let dir = tempfile::tempdir().unwrap();
    let config = crate::worker::WorkerConfig {
        socket_path: dir.path().join("worker.sock"),
        supervisor_socket_path: std::path::PathBuf::new(),
        token: "token".to_owned(),
        worker_instance_id: String::new(),
        active_session_id: "rlm-session".to_owned(),
        agent_dir: dir.path().join("agent"),
        recovery_journal_path: dir.path().join("recovery.jsonl"),
        telemetry_disabled: None,
        script: Some(json!({ "responses": ["ack"] })),
    };
    let worker = Arc::new(Worker::new(config, None));
    let created = worker
        .dispatch(
            "create",
            &json!({ "cwd": dir.path().to_string_lossy(), "name": "rlm-surface" }),
        )
        .await;
    assert!(created.success, "create failed: {created:?}");
    (dir, worker)
}

/// `get_rlm_children` on a session without children: an empty roster and
/// the event sequence.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn get_rlm_children_answers_an_empty_roster() {
    let (_dir, worker) = created_worker().await;
    let response = worker
        .dispatch(
            "get_rlm_children",
            &json!({ "activeSessionId": "rlm-session" }),
        )
        .await;
    assert!(response.success, "{response:?}");
    let data = response.data.unwrap();
    assert_eq!(data["children"], json!([]));
    assert!(data["eventSequence"].is_u64());
}

/// Wire shape: `cancel_rlm_child` answers `{ cancelled }` - false for an
/// unknown child (TS `cancelRlmChildRun` on an unmatched id).
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn cancel_rlm_child_answers_the_ts_cancelled_shape() {
    let (_dir, worker) = created_worker().await;
    let response = worker
        .dispatch(
            "cancel_rlm_child",
            &json!({ "activeSessionId": "rlm-session", "childId": "ghost-child" }),
        )
        .await;
    assert!(response.success, "{response:?}");
    assert_eq!(response.data, Some(json!({ "cancelled": false })));
}

/// Wire shape: `delete_rlm_subagent` answers `{ deleted: false }` for an
/// unknown child (TS `deleteInactiveRlmSubagent` -> "`not_found`").
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn delete_rlm_subagent_answers_the_ts_not_found_shape() {
    let (_dir, worker) = created_worker().await;
    let response = worker
        .dispatch(
            "delete_rlm_subagent",
            &json!({ "activeSessionId": "rlm-session", "childId": "ghost-child" }),
        )
        .await;
    assert!(response.success, "{response:?}");
    assert_eq!(response.data, Some(json!({ "deleted": false })));
}

/// `set_rlm_max_depth` answers the TS `SetRlmMaxDepthResult`, the status
/// reads it back as the chat bound, and a global request writes the
/// settings default.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn set_rlm_max_depth_persists_the_chat_bound() {
    let (dir, worker) = created_worker().await;
    let status = worker
        .dispatch(
            "get_rlm_max_depth_status",
            &json!({ "activeSessionId": "rlm-session" }),
        )
        .await;
    assert!(status.success, "{status:?}");
    assert_eq!(status.data.unwrap()["source"], "default");

    let response = worker
        .dispatch(
            "set_rlm_max_depth",
            &json!({ "activeSessionId": "rlm-session", "maxDepth": 3 }),
        )
        .await;
    assert!(response.success, "{response:?}");
    assert_eq!(
        response.data,
        Some(json!({ "maxDepth": 3, "source": "chat", "globalSaved": false }))
    );
    let status = worker
        .dispatch(
            "get_rlm_max_depth_status",
            &json!({ "activeSessionId": "rlm-session" }),
        )
        .await;
    assert_eq!(
        status.data,
        Some(json!({ "maxDepth": 3, "source": "chat" }))
    );

    let response = worker
        .dispatch(
            "set_rlm_max_depth",
            &json!({ "activeSessionId": "rlm-session", "maxDepth": 4, "global": true }),
        )
        .await;
    assert!(response.success, "{response:?}");
    assert_eq!(
        response.data,
        Some(json!({ "maxDepth": 4, "source": "chat", "globalSaved": true }))
    );
    let settings = std::fs::read_to_string(dir.path().join("agent/settings.json")).unwrap();
    assert!(settings.contains("\"rlmMaxDepth\": 4") || settings.contains("\"rlmMaxDepth\":4"));
}

/// Wire shape: a missing `childId`/`maxDepth` fails the command (the TS
/// parse of the required wire field).
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn missing_required_fields_fail() {
    let (_dir, worker) = created_worker().await;
    for command_type in ["cancel_rlm_child", "delete_rlm_subagent"] {
        let response = worker
            .dispatch(command_type, &json!({ "activeSessionId": "rlm-session" }))
            .await;
        assert!(
            !response.success,
            "{command_type} must fail without childId"
        );
    }
    let response = worker
        .dispatch(
            "set_rlm_max_depth",
            &json!({ "activeSessionId": "rlm-session" }),
        )
        .await;
    assert!(!response.success);
    assert_eq!(
        response.error.as_deref(),
        Some("RLM max depth must be a non-negative integer.")
    );
}
