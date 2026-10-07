use serde_json::{json, Value};

use crate::durable_test_support::{created_worker, wait_busy, worker_inbox};
use crate::worker::Worker;

const SESSION: &str = "ami-session";

/// A worker whose first run holds the model request (so later inputs queue
/// in the inbox), then answers.
async fn busy_worker() -> (tempfile::TempDir, std::sync::Arc<Worker>) {
    let (dir, worker) = created_worker(
        SESSION,
        json!([{ "text": "held", "delayMs": 600_000 }, "ack"]),
    )
    .await;
    let prompt = worker
        .dispatch(
            "prompt",
            &json!({ "activeSessionId": SESSION, "message": "work" }),
        )
        .await;
    assert!(prompt.success, "{prompt:?}");
    wait_busy(&worker, true).await;
    (dir, worker)
}

async fn deliver(
    worker: &Worker,
    message: &str,
    mode: Option<&str>,
) -> crate::protocol::DaemonResponse {
    let mut payload = json!({
        "targetActiveSessionId": SESSION,
        "message": message,
        "sender": { "activeSessionId": "peer-1" },
    });
    if let Some(mode) = mode {
        payload["deliveryMode"] = json!(mode);
    }
    worker.dispatch("worker_deliver_message", &payload).await
}

async fn finish(worker: &Worker) {
    let aborted = worker
        .dispatch(
            "abort_and_clear_queue",
            &json!({ "activeSessionId": SESSION }),
        )
        .await;
    assert!(aborted.success, "{aborted:?}");
}

/// The safety status answers the TS five-field shape with the TS
/// constants; a pause withdraws the queued agent message (prompt and card)
/// but keeps client-queued prompts, a paused delivery answers the TS gate
/// error, and resume flips the flag back.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn status_pause_resume_and_clear_match_ts_shapes() {
    let (_dir, worker) = busy_worker().await;

    let status = worker.dispatch("agent_messages_status", &json!({})).await;
    assert!(status.success);
    assert_eq!(
        status.data,
        Some(json!({
            "paused": false,
            "maxMessageChars": 16384,
            "maxPendingPerSession": 20,
            "rateLimitCapacity": 3,
            "rateLimitRefillMs": 1000,
        }))
    );

    let delivered = deliver(&worker, "from a peer", None).await;
    assert!(delivered.success, "delivery failed: {delivered:?}");
    assert_eq!(
        delivered.data.as_ref().unwrap()["deliveryStatus"],
        json!("queued")
    );
    let steered = worker
        .dispatch(
            "steer",
            &json!({ "activeSessionId": SESSION, "message": "client text" }),
        )
        .await;
    assert!(steered.success, "{steered:?}");
    let inbox = worker_inbox(&worker).await;
    assert_eq!(inbox.len(), 3, "card, prompt, client steer: {inbox:?}");

    let paused = worker.dispatch("agent_messages_pause", &json!({})).await;
    assert!(paused.success, "{paused:?}");
    assert_eq!(paused.data.as_ref().unwrap()["paused"], json!(true));
    assert_eq!(
        worker_inbox(&worker).await,
        vec![("steer".to_owned(), "client text".to_owned())]
    );

    let refused = deliver(&worker, "while paused", None).await;
    assert!(!refused.success);
    assert_eq!(refused.error.as_deref(), Some("Agent messaging is paused"));

    let resumed = worker.dispatch("agent_messages_resume", &json!({})).await;
    assert_eq!(resumed.data.as_ref().unwrap()["paused"], json!(false));

    // Only agent messages go: nothing left to clear, the client prompt stays.
    let cleared = worker.dispatch("agent_messages_clear", &json!({})).await;
    assert!(cleared.success);
    assert_eq!(
        cleared.data,
        Some(json!({ "steering": [], "followUp": [] }))
    );
    assert_eq!(
        worker_inbox(&worker).await,
        vec![("steer".to_owned(), "client text".to_owned())]
    );
    finish(&worker).await;
}

/// A follow-up delivery is cleared from the follow-up lane with its prompt
/// text (TS reports `payload.text`, the created agent-message prompt).
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn clear_reports_the_follow_up_lane() {
    let (_dir, worker) = busy_worker().await;
    let delivered = deliver(&worker, "queued for later", Some("follow_up")).await;
    assert!(delivered.success, "delivery failed: {delivered:?}");
    let cleared = worker.dispatch("agent_messages_clear", &json!({})).await;
    assert_eq!(
        cleared.data,
        Some(json!({
            "steering": [],
            "followUp": ["[agent-message from peer-1]\n\nqueued for later"],
        }))
    );
    assert_eq!(worker_inbox(&worker).await, Vec::<(String, String)>::new());
    finish(&worker).await;
}

/// The arms answer the created-session gate before a session exists.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn arms_refuse_before_create() {
    let dir = tempfile::tempdir().expect("tempdir");
    let config = crate::worker::WorkerConfig {
        socket_path: dir.path().join("worker.sock"),
        supervisor_socket_path: std::path::PathBuf::new(),
        token: "token".to_owned(),
        worker_instance_id: String::new(),
        active_session_id: SESSION.to_owned(),
        agent_dir: dir.path().join("agent"),
        recovery_journal_path: dir.path().join("recovery.jsonl"),
        telemetry_disabled: None,
        script: None,
    };
    let worker = Worker::new(config, None);
    for command in [
        "agent_messages_status",
        "agent_messages_pause",
        "agent_messages_clear",
    ] {
        let response = worker.dispatch(command, &Value::Null).await;
        assert_eq!(
            response.error.as_deref(),
            Some("Session is still initializing"),
            "{command}"
        );
    }
}
