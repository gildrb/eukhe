//! In-process worker battery on the durable host: a faux-scripted session
//! driven through `dispatch`, observed on the worker's event pump.

use std::path::Path;
use std::sync::Arc;
use std::time::{Duration, Instant};

use eukhe_chord::context::BACKGROUND_CONTEXT;
use serde_json::{json, Value};
use tokio::sync::broadcast;

use super::{OutboundFrame, Worker, WorkerConfig};
use crate::durable_test_support::wait_busy;
use crate::journal::{WorkerRecoveryJournal, WorkerRecoveryRecord};

const DEADLINE: Duration = Duration::from_secs(20);

fn worker(dir: &Path, journal: &str, script: Value) -> Arc<Worker> {
    std::fs::create_dir_all(dir.join("agent")).expect("agent dir");
    std::fs::create_dir_all(dir.join("work")).expect("cwd");
    let config = WorkerConfig {
        socket_path: dir.join("worker.sock"),
        supervisor_socket_path: std::path::PathBuf::new(),
        token: "token".to_owned(),
        worker_instance_id: String::new(),
        active_session_id: "worker-test".to_owned(),
        agent_dir: dir.join("agent"),
        recovery_journal_path: dir.join(journal),
        telemetry_disabled: Some(true),
        script: Some(script),
    };
    let worker = Worker::new(config, None);
    // `serve` opens the journal; the in-process worker opens it here.
    *worker.recovery.lock().unwrap() =
        Some(WorkerRecoveryJournal::open(&dir.join(journal)).expect("journal"));
    Arc::new(worker)
}

async fn create(worker: &Worker, payload: Value) {
    let created = worker.dispatch("create", &payload).await;
    assert!(created.success, "create failed: {created:?}");
}

/// A created worker on an in-memory session.
async fn created(dir: &Path, script: Value) -> Arc<Worker> {
    let worker = worker(dir, "recovery.jsonl", script);
    let cwd = dir.join("work");
    create(&worker, json!({ "noSession": true, "cwd": cwd })).await;
    worker
}

/// The session event of one outbound frame.
fn session_event(frame: &OutboundFrame) -> Option<Value> {
    if frame.outbound_type != "session_event" {
        return None;
    }
    let mut payload: Value = serde_json::from_slice(&frame.payload).ok()?;
    Some(payload.get_mut("event")?.take())
}

/// Every session event already on `events`.
fn drain(events: &mut broadcast::Receiver<Arc<OutboundFrame>>) -> Vec<Value> {
    let mut out = Vec::new();
    while let Ok(frame) = events.try_recv() {
        out.extend(session_event(&frame));
    }
    out
}

/// Receive session events until one matches `stop` (returned last).
async fn until(
    events: &mut broadcast::Receiver<Arc<OutboundFrame>>,
    stop: impl Fn(&Value) -> bool,
) -> Vec<Value> {
    let mut out = Vec::new();
    loop {
        let frame = tokio::time::timeout(DEADLINE, events.recv())
            .await
            .expect("the awaited event never came")
            .expect("event pump");
        if let Some(event) = session_event(&frame) {
            let done = stop(&event);
            out.push(event);
            if done {
                return out;
            }
        }
    }
}

fn kind(event: &Value) -> &str {
    event["type"].as_str().unwrap_or_default()
}

fn role(event: &Value) -> &str {
    event["message"]["role"].as_str().unwrap_or_default()
}

/// The text of a wire message (string content or text parts).
fn text(message: &Value) -> String {
    match &message["content"] {
        Value::String(text) => text.clone(),
        Value::Array(parts) => parts
            .iter()
            .filter_map(|part| part["text"].as_str())
            .collect(),
        _ => String::new(),
    }
}

async fn messages(worker: &Worker) -> Vec<Value> {
    let response = worker.dispatch("get_messages", &json!({})).await;
    assert!(response.success, "get_messages: {response:?}");
    response.data.expect("messages")["messages"]
        .as_array()
        .cloned()
        .unwrap_or_default()
}

fn texts_of(messages: &[Value], wanted: &str) -> Vec<String> {
    messages
        .iter()
        .filter(|message| message["role"] == wanted)
        .map(text)
        .collect()
}

/// Poll the transcript until it satisfies `done`.
async fn wait_messages(worker: &Worker, done: impl Fn(&[Value]) -> bool) -> Vec<Value> {
    let deadline = Instant::now() + DEADLINE;
    loop {
        let messages = messages(worker).await;
        if done(&messages) {
            return messages;
        }
        assert!(Instant::now() < deadline, "transcript never settled: {messages:?}");
        tokio::time::sleep(Duration::from_millis(20)).await;
    }
}

fn latest_record(dir: &Path, journal: &str) -> WorkerRecoveryRecord {
    let mut records = WorkerRecoveryJournal::read_latest(&dir.join(journal)).expect("journal");
    assert_eq!(records.len(), 1, "one session in the journal: {records:?}");
    records.remove(0)
}

/// A prompt streams the TS frame order: the run opens before its user
/// message, the assistant streams, and `agent_end` carries the run's
/// messages.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_prompt_streams_session_events_and_answers() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created(dir.path(), json!({ "responses": ["the answer"] })).await;
    let mut events = worker.events.subscribe();
    let response = worker
        .dispatch("prompt_and_wait", &json!({ "message": "hello" }))
        .await;
    assert!(response.success, "prompt: {response:?}");
    // `prompt_and_wait` answers once the run settled and its frames are out.
    let events = drain(&mut events);
    let position = |pred: &dyn Fn(&Value) -> bool| {
        events
            .iter()
            .position(pred)
            .unwrap_or_else(|| panic!("missing event in {events:?}"))
    };
    let agent_start = position(&|event| kind(event) == "agent_start");
    let turn_start = position(&|event| kind(event) == "turn_start");
    let user_start = position(&|event| kind(event) == "message_start" && role(event) == "user");
    let user_end = position(&|event| kind(event) == "message_end" && role(event) == "user");
    let assistant_start =
        position(&|event| kind(event) == "message_start" && role(event) == "assistant");
    let update = position(&|event| kind(event) == "message_update");
    let assistant_end =
        position(&|event| kind(event) == "message_end" && role(event) == "assistant");
    let agent_end = position(&|event| kind(event) == "agent_end");
    assert!(
        agent_start < turn_start
            && turn_start < user_start
            && user_start < user_end
            && user_end < assistant_start
            && assistant_start < update
            && update < assistant_end
            && assistant_end < agent_end,
        "frame order: {events:?}"
    );
    let run_messages = events[agent_end]["messages"].as_array().expect("messages");
    assert_eq!(
        run_messages.iter().map(|m| m["role"].clone()).collect::<Vec<_>>(),
        [json!("user"), json!("assistant")]
    );
    assert_eq!(text(&events[assistant_end]["message"]), "the answer");
    let transcript = messages(&worker).await;
    assert_eq!(texts_of(&transcript, "user"), ["hello"]);
    assert_eq!(texts_of(&transcript, "assistant"), ["the answer"]);
}

/// An attach while the assistant streams shows the in-flight partial.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn attach_mid_stream_shows_the_partial() {
    let full = "alpha beta gamma delta epsilon zeta eta theta iota kappa lambda mu nu xi omicron pi rho sigma tau upsilon";
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created(
        dir.path(),
        json!({ "tokensPerSecond": 10, "responses": [full] }),
    )
    .await;
    let mut events = worker.events.subscribe();
    let response = worker.dispatch("prompt", &json!({ "message": "stream" })).await;
    assert!(response.success, "prompt: {response:?}");
    until(&mut events, |event| kind(event) == "message_update").await;
    let attached = worker
        .dispatch("attach", &json!({ "clientId": "watcher" }))
        .await;
    assert!(attached.success, "attach: {attached:?}");
    let snapshot = attached.data.expect("attach result")["snapshot"]["messages"].clone();
    let last = snapshot
        .as_array()
        .and_then(|messages| messages.last())
        .expect("attach messages");
    assert_eq!(last["role"], "assistant", "the partial: {snapshot}");
    let partial = text(last);
    assert!(
        !partial.is_empty() && partial.len() < full.len() && full.starts_with(&partial),
        "a strict prefix of the answer: {partial:?}"
    );
    until(&mut events, |event| kind(event) == "agent_end").await;
    wait_busy(&worker, false).await;
}

/// Steering joins the run at the post-tools boundary, ahead of an earlier
/// follow-up, which waits for the final boundary.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn steer_lands_before_an_earlier_follow_up() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created(
        dir.path(),
        json!({ "responses": [
            {
                "content": [{ "type": "toolCall", "name": "missing_tool", "arguments": {}, "id": "call-1" }],
                "delayMs": 500,
            },
            "second",
            "third",
        ] }),
    )
    .await;
    let response = worker.dispatch("prompt", &json!({ "message": "go" })).await;
    assert!(response.success, "prompt: {response:?}");
    wait_busy(&worker, true).await;
    let queued = worker.dispatch("follow_up", &json!({ "message": "F" })).await;
    assert!(queued.success, "follow_up: {queued:?}");
    let queued = worker.dispatch("steer", &json!({ "message": "S" })).await;
    assert!(queued.success, "steer: {queued:?}");
    let transcript = wait_messages(&worker, |messages| {
        texts_of(messages, "assistant").contains(&"third".to_owned())
    })
    .await;
    let order: Vec<String> = transcript
        .iter()
        .filter(|message| message["role"] != "toolResult")
        .map(|message| format!("{}:{}", message["role"].as_str().unwrap_or_default(), text(message)))
        .collect();
    assert_eq!(
        order,
        ["user:go", "assistant:", "user:S", "assistant:second", "user:F", "assistant:third"]
    );
}

/// `abort` ends the run and suspends the queued input; `resume_queue`
/// sends it.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn abort_suspends_the_queue_and_resume_sends_it() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created(
        dir.path(),
        json!({ "responses": [{ "text": "never", "delayMs": 30_000 }, "resumed"] }),
    )
    .await;
    let response = worker.dispatch("prompt", &json!({ "message": "go" })).await;
    assert!(response.success, "prompt: {response:?}");
    wait_busy(&worker, true).await;
    let queued = worker.dispatch("follow_up", &json!({ "message": "later" })).await;
    assert!(queued.success, "follow_up: {queued:?}");
    let aborted = worker.dispatch("abort", &json!({})).await;
    assert!(aborted.success, "abort: {aborted:?}");
    wait_busy(&worker, false).await;
    let suspended: Vec<String> = worker
        .core
        .lock()
        .unwrap()
        .suspended
        .iter()
        .map(|input| input.text.clone())
        .collect();
    assert_eq!(suspended, ["later"]);
    assert!(!texts_of(&messages(&worker).await, "assistant").contains(&"never".to_owned()));

    let resumed = worker.dispatch("resume_queue", &json!({})).await;
    assert!(resumed.success, "resume_queue: {resumed:?}");
    let transcript = wait_messages(&worker, |messages| {
        texts_of(messages, "assistant").contains(&"resumed".to_owned())
    })
    .await;
    assert_eq!(texts_of(&transcript, "user"), ["go", "later"]);
    assert!(worker.core.lock().unwrap().suspended.is_empty());
}

/// A worker that dies mid-run (after a tool round, while the follow-up
/// generation is in flight) is replaced by a fresh worker whose `create`
/// reopens the storage: the run resumes to completion, and the journal's
/// busy verdict goes `create` (busy) -> `run_ended` (idle).
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_crashed_run_resumes_on_the_next_create() {
    let dir = tempfile::tempdir().expect("tempdir");
    let sessions = dir.path().join("sessions");
    let cwd = dir.path().join("work");
    let first = worker(
        dir.path(),
        "first.recovery.jsonl",
        json!({ "responses": [
            { "content": [{ "type": "toolCall", "name": "missing_tool", "arguments": {}, "id": "call-1" }] },
            { "text": "lost", "delayMs": 60_000 },
        ] }),
    );
    create(&first, json!({ "cwd": cwd, "sessionDir": sessions })).await;
    let storage = first
        .session
        .get()
        .and_then(|hosted| hosted.storage_dir().map(Path::to_path_buf))
        .expect("a stored session");
    let response = first.dispatch("prompt", &json!({ "message": "go" })).await;
    assert!(response.success, "prompt: {response:?}");
    wait_messages(&first, |messages| {
        messages.iter().any(|message| message["role"] == "toolResult")
    })
    .await;
    assert!(first.core.lock().unwrap().is_busy());
    crash(&first).await;
    drop(first);

    let second = worker(
        dir.path(),
        "second.recovery.jsonl",
        json!({ "responses": ["done"] }),
    );
    create(&second, json!({ "cwd": cwd, "sessionPath": storage })).await;
    let created = latest_record(dir.path(), "second.recovery.jsonl");
    assert!(created.busy, "the resumed run is live work: {created:?}");
    assert_eq!(created.operation, "create");
    let transcript = wait_messages(&second, |messages| {
        texts_of(messages, "assistant").contains(&"done".to_owned())
    })
    .await;
    assert_eq!(texts_of(&transcript, "user"), ["go"]);
    wait_busy(&second, false).await;
    let ended = latest_record(dir.path(), "second.recovery.jsonl");
    assert!(!ended.busy, "the run settled: {ended:?}");
    assert_eq!(ended.operation, "run_ended");
}

/// The test-only crash: the hosted session goes away with its run in
/// flight (no abort, no settle), leaving the storage to the next open.
async fn crash(worker: &Worker) {
    let hosted = worker.session.take().expect("a hosted session");
    hosted.close(&BACKGROUND_CONTEXT).await.expect("close");
}
