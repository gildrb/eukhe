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
        assert!(
            Instant::now() < deadline,
            "transcript never settled: {messages:?}"
        );
        tokio::time::sleep(Duration::from_millis(20)).await;
    }
}

/// Poll until the worker's script served `count` model requests: the
/// provider takes the script's next response the moment a request starts.
async fn wait_requests(worker: &Worker, count: u64) {
    let deadline = Instant::now() + DEADLINE;
    loop {
        let served = worker
            .scripted_models
            .get()
            .expect("a scripted worker")
            .requests();
        if served >= count {
            return;
        }
        assert!(
            Instant::now() < deadline,
            "the script served {served} of {count} model requests"
        );
        tokio::time::sleep(Duration::from_millis(10)).await;
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
    const ANSWER: &str = "the answer arrives in several streamed pieces";
    let dir = tempfile::tempdir().expect("tempdir");
    // Streamed: an instant answer commits before any partial publishes.
    let worker = created(
        dir.path(),
        json!({ "tokensPerSecond": 20, "responses": [ANSWER] }),
    )
    .await;
    let mut events = worker.events.subscribe();
    let response = worker
        .dispatch("prompt_and_wait", &json!({ "message": "hello" }))
        .await;
    assert!(response.success, "prompt: {response:?}");
    // `prompt_and_wait` answers once the run settled and its frames are out.
    let events = drain(&mut events);
    let position = |name: &str, pred: &dyn Fn(&Value) -> bool| {
        events.iter().position(pred).unwrap_or_else(|| {
            let kinds: Vec<String> = events
                .iter()
                .map(|event| {
                    event["type"].as_str().unwrap_or_default().to_owned()
                        + "/"
                        + event["message"]["role"].as_str().unwrap_or_default()
                })
                .collect();
            panic!("missing {name} in {kinds:?}")
        })
    };
    let agent_start_at = position("agent_start", &|event| kind(event) == "agent_start");
    let turn_start_at = position("turn_start", &|event| kind(event) == "turn_start");
    let user_start_at = position("user_start", &|event| {
        kind(event) == "message_start" && role(event) == "user"
    });
    let user_end_at = position("user_end", &|event| {
        kind(event) == "message_end" && role(event) == "user"
    });
    let assistant_start_at = position("assistant_start", &|event| {
        kind(event) == "message_start" && role(event) == "assistant"
    });
    let update_at = position("update", &|event| kind(event) == "message_update");
    let assistant_end_at = position("assistant_end", &|event| {
        kind(event) == "message_end" && role(event) == "assistant"
    });
    let agent_end_at = position("agent_end", &|event| kind(event) == "agent_end");
    assert!(
        agent_start_at < turn_start_at
            && turn_start_at < user_start_at
            && user_start_at < user_end_at
            && user_end_at < assistant_start_at
            && assistant_start_at < update_at
            && update_at < assistant_end_at
            && assistant_end_at < agent_end_at,
        "frame order: {events:?}"
    );
    let run_messages = events[agent_end_at]["messages"]
        .as_array()
        .expect("messages");
    assert_eq!(
        run_messages
            .iter()
            .map(|m| m["role"].clone())
            .collect::<Vec<_>>(),
        [json!("user"), json!("custom"), json!("assistant")]
    );
    assert_eq!(text(&events[assistant_end_at]["message"]), ANSWER);
    let transcript = messages(&worker).await;
    assert_eq!(texts_of(&transcript, "user"), ["hello"]);
    assert_eq!(texts_of(&transcript, "assistant"), [ANSWER]);
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
    let response = worker
        .dispatch("prompt", &json!({ "message": "stream" }))
        .await;
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
    let queued = worker
        .dispatch("follow_up", &json!({ "message": "F" }))
        .await;
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
        .map(|message| match message["role"].as_str() {
            Some("custom") => format!(
                "custom:{}",
                message["customType"].as_str().unwrap_or_default()
            ),
            role => format!("{}:{}", role.unwrap_or_default(), text(message)),
        })
        .collect();
    assert_eq!(
        order,
        [
            "user:go",
            "custom:harness_digest",
            "assistant:",
            "user:S",
            "assistant:second",
            "user:F",
            "assistant:third"
        ]
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
    // The abort must land on the held `never` request: one landing before
    // the generation asked the model (it asks after committing the digest)
    // would leave `never` queued for the resume.
    wait_requests(&worker, 1).await;
    let queued = worker
        .dispatch("follow_up", &json!({ "message": "later" }))
        .await;
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

/// `abort`'s suspended inputs are durable (`eukhe.daemon.suspended`): a
/// fresh worker over the same storage still shows them in its queue
/// strip, and `resume_queue` there sends them (the document persists
/// the queue).
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn suspended_inputs_survive_a_worker_restart() {
    let dir = tempfile::tempdir().expect("tempdir");
    let sessions = dir.path().join("sessions");
    let cwd = dir.path().join("work");
    let first = worker(
        dir.path(),
        "first.recovery.jsonl",
        json!({ "responses": [{ "text": "never", "delayMs": 30_000 }, "resumed"] }),
    );
    create(&first, json!({ "cwd": cwd, "sessionDir": sessions })).await;
    let storage = first
        .session
        .get()
        .and_then(|hosted| hosted.storage_dir().map(Path::to_path_buf))
        .expect("a stored session");
    let response = first.dispatch("prompt", &json!({ "message": "go" })).await;
    assert!(response.success, "prompt: {response:?}");
    wait_busy(&first, true).await;
    let queued = first
        .dispatch("follow_up", &json!({ "message": "later" }))
        .await;
    assert!(queued.success, "follow_up: {queued:?}");
    let aborted = first.dispatch("abort", &json!({})).await;
    assert!(aborted.success, "abort: {aborted:?}");
    wait_busy(&first, false).await;
    crash(&first).await;
    drop(first);

    let second = worker(
        dir.path(),
        "second.recovery.jsonl",
        json!({ "responses": ["resumed"] }),
    );
    create(
        &second,
        json!({ "cwd": dir.path().join("work"), "sessionPath": storage }),
    )
    .await;
    // The restarted worker's queue strip shows the suspended input: the
    // durable document seeded the cache.
    let snapshot = {
        let core = second
            .core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        super::session_snapshot(&core)
    };
    let texts = |items: &[eukhe_types::daemon::QueuedItem]| {
        items
            .iter()
            .map(|item| item.text.clone())
            .collect::<Vec<_>>()
    };
    assert_eq!(
        texts(&snapshot.follow_ups),
        ["later"],
        "the strip: {snapshot:?}"
    );
    assert_eq!(snapshot.queued_count, 1);

    let resumed = second.dispatch("resume_queue", &json!({})).await;
    assert!(resumed.success, "resume_queue: {resumed:?}");
    let transcript = wait_messages(&second, |messages| {
        texts_of(messages, "assistant").contains(&"resumed".to_owned())
    })
    .await;
    assert_eq!(texts_of(&transcript, "user"), ["go", "later"]);
}

/// An input-pause lease holds admissions: a prompt while paused never
/// reaches the model, `prompt_and_wait` answers the pause error, and the
/// release delivers the held input (the admission gate).
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn an_input_pause_lease_holds_admissions_until_released() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created(dir.path(), json!({ "responses": ["after the release"] })).await;
    let acquired = worker
        .dispatch(
            "acquire_session_input_pause",
            &json!({
                "activeSessionId": "worker-test",
                "leaseKey": "[\"conn\",\"owner\",\"lease\"]",
                "clientId": "conn",
            }),
        )
        .await;
    assert!(acquired.success, "{acquired:?}");

    // A waiting prompt answers the pause error; the input stays held.
    let waiting = worker
        .dispatch("prompt_and_wait", &json!({ "message": "held" }))
        .await;
    assert!(!waiting.success, "{waiting:?}");
    assert_eq!(waiting.error.as_deref(), Some("Session input is paused"));
    let snapshot = {
        let core = worker
            .core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        super::session_snapshot(&core)
    };
    assert_eq!(
        snapshot.follow_ups,
        [eukhe_types::daemon::QueuedItem {
            text: "held".to_owned(),
            origin: eukhe_types::input_origin::InputOrigin::User,
        }],
        "the held strip: {snapshot:?}"
    );
    assert!(
        messages(&worker).await.is_empty(),
        "nothing reached the model"
    );

    // The release delivers the held input.
    let pause_id = acquired.data.expect("pauseId data")["pauseId"]
        .as_str()
        .expect("a pause id")
        .to_string();
    let released = worker
        .dispatch(
            "release_session_input_pause",
            &json!({
                "activeSessionId": "worker-test",
                "pauseId": pause_id,
                "clientId": "conn",
            }),
        )
        .await;
    assert!(released.success, "{released:?}");
    let transcript = wait_messages(&worker, |messages| {
        texts_of(messages, "assistant").contains(&"after the release".to_owned())
    })
    .await;
    assert_eq!(texts_of(&transcript, "user"), ["held"]);
    let snapshot = {
        let core = worker
            .core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        super::session_snapshot(&core)
    };
    assert!(
        snapshot.follow_ups.is_empty(),
        "the drained strip: {snapshot:?}"
    );
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
        messages
            .iter()
            .any(|message| message["role"] == "toolResult")
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

/// A Storage failure mid-run (the session's files turn unwritable, so the
/// next commit fails and the Harness fails its Session) does not leave the
/// session busy: busy derives from the durable Harness, not from the event
/// mirror (which never hears a run end). The worker retires with a typed
/// failure in its journal, and a revived worker reopens the storage,
/// resumes the run, and drains the steer queued before the failure.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_failed_harness_retires_the_worker_and_the_revival_drains_the_steer() {
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
        messages
            .iter()
            .any(|message| message["role"] == "toolResult")
    })
    .await;
    let queued = first.dispatch("steer", &json!({ "message": "S" })).await;
    assert!(queued.success, "steer: {queued:?}");
    assert!(first.core.lock().unwrap().is_busy());

    // The disk refuses writes: the next commit fails the Harness.
    set_writable(&storage, false);
    let refused = first
        .dispatch("follow_up", &json!({ "message": "refused" }))
        .await;
    assert!(!refused.success, "the failing commit answers: {refused:?}");
    wait_busy(&first, false).await;
    set_writable(&storage, true);
    let failure = tokio::time::timeout(DEADLINE, first.retire_failed_harness())
        .await
        .expect("the worker retires its failed session");
    assert!(
        matches!(
            &failure,
            crate::journal::WorkerFailure::HarnessFailed { .. }
        ),
        "{failure:?}"
    );
    let failed = latest_record(dir.path(), "first.recovery.jsonl");
    assert!(
        failed.busy,
        "the interrupted session is revival work: {failed:?}"
    );
    assert_eq!(failed.failure, Some(failure));
    assert!(first.session.get().is_none(), "the failed session closed");
    drop(first);

    let second = worker(
        dir.path(),
        "second.recovery.jsonl",
        json!({ "responses": ["done"], "repeatLastResponse": true }),
    );
    create(&second, json!({ "cwd": cwd, "sessionPath": storage })).await;
    // The steer joins the resumed run at its next boundary and is answered.
    let transcript = wait_messages(&second, |messages| {
        messages
            .iter()
            .position(|message| message["role"] == "user" && text(message) == "S")
            .is_some_and(|steer| {
                messages[steer..]
                    .iter()
                    .any(|message| message["role"] == "assistant")
            })
    })
    .await;
    assert_eq!(texts_of(&transcript, "user"), ["go", "S"]);
    wait_busy(&second, false).await;
}

/// Make `dir`'s tree unwritable (or writable again).
fn set_writable(dir: &Path, writable: bool) {
    use std::os::unix::fs::PermissionsExt;
    let (dir_mode, file_mode) = if writable {
        (0o755, 0o644)
    } else {
        (0o555, 0o444)
    };
    for entry in std::fs::read_dir(dir).expect("storage dir") {
        let path = entry.expect("storage entry").path();
        if path.is_dir() {
            set_writable(&path, writable);
        } else {
            std::fs::set_permissions(&path, std::fs::Permissions::from_mode(file_mode))
                .expect("file mode");
        }
    }
    std::fs::set_permissions(dir, std::fs::Permissions::from_mode(dir_mode)).expect("dir mode");
}

/// The test-only crash: the hosted session goes away with its run in
/// flight (no abort, no settle), leaving the storage to the next open.
async fn crash(worker: &Worker) {
    let hosted = worker.session.take().expect("a hosted session");
    hosted.close(&BACKGROUND_CONTEXT).await.expect("close");
}

/// The journal record an orphan exit leaves for `worker`'s session.
fn orphan_exit_record(
    worker: &Worker,
    busy: bool,
    operation: &str,
    recorded_at: String,
) -> WorkerRecoveryRecord {
    let core = worker.core.lock().unwrap();
    WorkerRecoveryRecord {
        active_session_id: core.active_session_id.clone(),
        session_id: core.session_id.clone(),
        session_file: core.session_file(),
        busy,
        operation: operation.to_owned(),
        recorded_at,
        failure: None,
    }
}

/// An orphan exit with a run in flight hands the run over: the journal
/// keeps busy revival evidence, the run is not aborted, and the session
/// is not closed (the next supervisor resumes it from storage).
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn an_orphan_exit_with_ongoing_work_hands_the_run_over() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created(
        dir.path(),
        json!({ "responses": [{ "text": "never", "delayMs": 30_000 }] }),
    )
    .await;
    let response = worker.dispatch("prompt", &json!({ "message": "go" })).await;
    assert!(response.success, "prompt: {response:?}");
    wait_busy(&worker, true).await;
    // No `serve` runs here: the stored permit stands in for the accept
    // loop's listener-closed confirmation.
    worker.listener_closed.notify_one();

    let exit = crate::supervisor_lost::leave_orphaned(&worker).await;

    assert_eq!(exit, crate::work_gate::OrphanExit::Handover);
    let record = latest_record(dir.path(), "recovery.jsonl");
    let expected = orphan_exit_record(&worker, true, "orphaned", record.recorded_at.clone());
    assert_eq!(record, expected);
    assert!(
        worker.core.lock().unwrap().is_busy(),
        "the run was not aborted"
    );
    assert!(worker.session.get().is_some(), "the session was not closed");
}

/// An orphan exit without work closes the session and records it idle.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn an_idle_orphan_exit_closes_the_session() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created(dir.path(), json!({ "responses": [] })).await;
    worker.listener_closed.notify_one();

    let exit = crate::supervisor_lost::leave_orphaned(&worker).await;

    assert_eq!(exit, crate::work_gate::OrphanExit::Close);
    let record = latest_record(dir.path(), "recovery.jsonl");
    let expected = orphan_exit_record(&worker, false, "shutdown", record.recorded_at.clone());
    assert_eq!(record, expected);
    assert!(worker.session.get().is_none(), "the session closed");
}

/// Regression (`laws/worker_lifecycle.bend` F1): the orphan exit read only
/// the core's work (a run, a compaction, a view inbox input), so a worker
/// whose only work was background work (here a user bash; a kernel job,
/// an unsettled child or workflow run likewise) closed its session and
/// recorded it idle, and no boot resumed it. It now hands the work over.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn an_orphan_exit_with_background_work_hands_it_over() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created(dir.path(), json!({ "responses": [] })).await;
    let _bash = worker.user_bash.begin_awaited();
    worker.listener_closed.notify_one();

    let exit = crate::supervisor_lost::leave_orphaned(&worker).await;

    assert_eq!(exit, crate::work_gate::OrphanExit::Handover);
    let record = latest_record(dir.path(), "recovery.jsonl");
    let expected = orphan_exit_record(&worker, true, "orphaned", record.recorded_at.clone());
    assert_eq!(record, expected);
    assert!(worker.session.get().is_some(), "the session was not closed");
}

/// Regression (`laws/worker_lifecycle.bend` F2, user decision Q3): the busy
/// refresh only re-stamped a record that was already busy, so work that
/// started after the run's end record (an auto-compaction, a queued input,
/// a background job) was never recorded busy and a double crash lost it.
/// A refresh tick now records the session busy whatever its latest record
/// said.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_refresh_tick_records_an_idle_session_with_work_busy() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created(dir.path(), json!({ "responses": [] })).await;
    worker
        .record_recovery(false, "run_ended")
        .expect("idle record");
    assert!(!latest_record(dir.path(), "recovery.jsonl").busy);

    crate::worker::refresh_busy_tick(&worker.recovery, &worker.core);

    let record = latest_record(dir.path(), "recovery.jsonl");
    let expected = orphan_exit_record(&worker, true, "refresh", record.recorded_at.clone());
    assert_eq!(record, expected);
}
