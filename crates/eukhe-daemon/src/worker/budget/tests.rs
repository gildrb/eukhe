//! The budget commands over an in-process worker that hosts a scripted
//! (faux) session: its budget set, added to, read and audited through
//! `dispatch`, and its changes read from the worker's event pump.

use std::path::Path;
use std::sync::Arc;
use std::time::Duration;

use serde_json::{json, Value};
use tokio::sync::broadcast;

use crate::worker::{OutboundFrame, Worker, WorkerConfig};

const DEADLINE: Duration = Duration::from_secs(20);

fn worker(dir: &Path) -> Arc<Worker> {
    std::fs::create_dir_all(dir.join("agent")).expect("agent dir");
    Arc::new(Worker::new(
        WorkerConfig {
            socket_path: dir.join("worker.sock"),
            supervisor_socket_path: std::path::PathBuf::new(),
            token: "token".to_string(),
            worker_instance_id: String::new(),
            active_session_id: "budget-session".to_string(),
            agent_dir: dir.join("agent"),
            recovery_journal_path: dir.join("recovery.jsonl"),
            script: Some(json!({ "modelId": "faux-1", "responses": ["ack"] })),
        },
        None,
    ))
}

/// A created in-memory session on `dir`, without a budget.
async fn created(dir: &Path) -> Arc<Worker> {
    let worker = worker(dir);
    let created = worker
        .dispatch("create", &json!({ "noSession": true, "cwd": dir }))
        .await;
    assert!(created.success, "create failed: {created:?}");
    worker
}

fn session_id(worker: &Worker) -> String {
    worker
        .core
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .session_id
        .clone()
}

/// The response data of a command that must succeed.
async fn data(worker: &Worker, command: &str, payload: &Value) -> Value {
    let response = worker.dispatch(command, payload).await;
    assert!(response.success, "{command} failed: {response:?}");
    response.data.expect("response data")
}

/// The answer of a command that must be refused: no data, and its error.
async fn refusal(worker: &Worker, command: &str, payload: &Value) -> (bool, Option<Value>, String) {
    let response = worker.dispatch(command, payload).await;
    (
        response.success,
        response.data,
        response.error.unwrap_or_default(),
    )
}

fn amounts(cost_micros: u64, tokens: u64, tool_calls: u64) -> Value {
    json!({ "costMicros": cost_micros, "tokens": tokens, "timeMs": 0, "toolCalls": tool_calls, "requests": 0 })
}

/// The wire report of a budget of `limits` that nothing was spent from,
/// as its owner sees it: `free` is all of it.
fn untouched(session_id: &str, limits: &Value, free: &Value) -> Value {
    let zero = amounts(0, 0, 0);
    json!({
        "sessionId": session_id,
        "agentSessionId": session_id,
        "limits": limits,
        "free": free,
        "held": zero,
        "spent": zero,
        "lent": zero,
        "over": zero,
        "phase": "working",
    })
}

/// The next `budget_update` session event on `events`.
async fn next_budget_update(events: &mut broadcast::Receiver<Arc<OutboundFrame>>) -> Value {
    loop {
        let frame = tokio::time::timeout(DEADLINE, events.recv())
            .await
            .expect("no budget_update came")
            .expect("event pump");
        if frame.outbound_type == "session_event" {
            let mut payload: Value = serde_json::from_slice(&frame.payload).expect("a JSON frame");
            let event = payload["event"].take();
            if event["type"] == "budget_update" {
                return event;
            }
        }
    }
}

/// A session has no budget until one is set; a set budget reads back with
/// its limits free and every other amount zero (B1, B8).
#[tokio::test]
async fn a_set_budget_reads_back_with_its_limits_free() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created(dir.path()).await;
    let before = data(&worker, "get_budget", &json!({})).await;
    let limits = json!({ "costMicros": 5_000_000, "toolCalls": 40 });
    let set = data(&worker, "set_budget", &json!({ "limits": limits })).await;
    let after = data(&worker, "get_budget", &json!({})).await;
    let report = untouched(&session_id(&worker), &limits, &amounts(5_000_000, 0, 40));
    assert_eq!(
        (before, set, after),
        (
            json!({ "budget": null }),
            json!({ "budget": report }),
            json!({ "budget": report }),
        )
    );
}

/// A session that has a budget refuses a second `set_budget` with the
/// ledger's message and keeps its budget; a `set_budget` without limits
/// is refused before the ledger is asked.
#[tokio::test]
async fn a_second_set_budget_is_refused_with_the_ledgers_message() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created(dir.path()).await;
    let id = session_id(&worker);
    let unnamed = refusal(&worker, "set_budget", &json!({})).await;
    let limits = json!({ "tokens": 100_000 });
    let set = data(&worker, "set_budget", &json!({ "limits": limits })).await;
    let again = refusal(&worker, "set_budget", &json!({ "limits": { "tokens": 7 } })).await;
    let kept = data(&worker, "get_budget", &json!({})).await;
    let report = untouched(&id, &limits, &amounts(0, 100_000, 0));
    assert_eq!(
        (unnamed, set, again, kept),
        (
            (false, None, "limits is required".to_string()),
            json!({ "budget": report }),
            (false, None, format!("session {id} already has a budget")),
            json!({ "budget": report }),
        )
    );
}

/// `add_budget` on a session without a budget sets the amounts as its
/// budget; on a session with one it raises the limits and what is free,
/// and limits a dimension that had no limit (B6).
#[tokio::test]
async fn add_budget_sets_a_budget_then_raises_it() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created(dir.path()).await;
    let id = session_id(&worker);
    let first = data(
        &worker,
        "add_budget",
        &json!({ "amounts": { "tokens": 50_000 } }),
    )
    .await;
    let second = data(
        &worker,
        "add_budget",
        &json!({ "amounts": { "costMicros": 2_000_000, "tokens": 10_000 } }),
    )
    .await;
    assert_eq!(
        (first, second),
        (
            json!({
                "budget": untouched(&id, &json!({ "tokens": 50_000 }), &amounts(0, 50_000, 0)),
            }),
            json!({
                "budget": untouched(
                    &id,
                    &json!({ "costMicros": 2_000_000, "tokens": 60_000 }),
                    &amounts(2_000_000, 60_000, 0),
                ),
            }),
        )
    );
}

/// `set_budget` sends one `budget_update` with the new report, and the
/// attach snapshot's state carries the same report from then on (B8).
#[tokio::test]
async fn a_set_budget_sends_a_budget_update_and_fills_the_attach_state() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created(dir.path()).await;
    let state_budget = |worker: &Worker| {
        let core = worker
            .core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        serde_json::to_value(worker.connection_state_locked(&core)).expect("state")["budget"]
            .clone()
    };
    let before = state_budget(&worker);
    let mut events = worker.events.subscribe();
    let limits = json!({ "tokens": 100_000 });
    let set = data(&worker, "set_budget", &json!({ "limits": limits })).await;
    let event = next_budget_update(&mut events).await;
    let after = state_budget(&worker);
    let report = untouched(&session_id(&worker), &limits, &amounts(0, 100_000, 0));
    assert_eq!(
        (before, set, event, after),
        (
            Value::Null,
            json!({ "budget": report }),
            json!({ "type": "budget_update", "budget": report }),
            report,
        )
    );
}

/// A session without a budget has no ledger to audit; a fresh budget's
/// ledger holds its one record and replays exactly (B9).
#[tokio::test]
async fn an_audit_replays_the_ledger_of_a_session_that_has_a_budget() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created(dir.path()).await;
    let id = session_id(&worker);
    let without = refusal(&worker, "audit_budget", &json!({})).await;
    data(
        &worker,
        "set_budget",
        &json!({ "limits": { "costMicros": 1_000_000 } }),
    )
    .await;
    let audit = data(&worker, "audit_budget", &json!({})).await;
    assert_eq!(
        (without, audit),
        (
            (false, None, format!("session {id} has no budget")),
            json!({
                "audit": {
                    "records": 1,
                    "settled": amounts(0, 0, 0),
                    "spent": amounts(0, 0, 0),
                    "exact": true,
                    "firstMismatch": null,
                },
            }),
        )
    );
}

/// The create config's `budget` is the new session's budget before its
/// first turn; a later create of the same session that names another
/// budget succeeds and keeps the one the session has (B1).
#[tokio::test]
async fn a_create_budget_is_set_once_for_a_session() {
    let dir = tempfile::tempdir().expect("tempdir");
    let sessions = dir.path().join("sessions");
    let id = "0192a000-0000-7000-8000-00000000b0d9";
    let first = worker(dir.path());
    let created = first
        .dispatch(
            "create",
            &json!({
                "cwd": dir.path(),
                "sessionDir": sessions,
                "sessionId": id,
                "budget": { "toolCalls": 12 },
            }),
        )
        .await;
    assert!(created.success, "create failed: {created:?}");
    let set = data(&first, "get_budget", &json!({})).await;
    let stopped = first.dispatch("kill", &json!({})).await;
    assert!(stopped.success, "kill failed: {stopped:?}");

    let second = worker(dir.path());
    let reopened = second
        .dispatch(
            "create",
            &json!({
                "sessionPath": sessions.join(id),
                "cwd": dir.path(),
                "budget": { "toolCalls": 99 },
            }),
        )
        .await;
    assert!(reopened.success, "reopen failed: {reopened:?}");
    let kept = data(&second, "get_budget", &json!({})).await;
    let report = untouched(id, &json!({ "toolCalls": 12 }), &amounts(0, 0, 12));
    assert_eq!(
        (set, kept),
        (json!({ "budget": report }), json!({ "budget": report }))
    );
}

/// An idempotent re-create of a created session that names a budget gives
/// a session without one that budget (B1).
#[tokio::test]
async fn a_re_create_sets_the_budget_it_names() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created(dir.path()).await;
    let again = worker
        .dispatch(
            "create",
            &json!({ "noSession": true, "cwd": dir.path(), "budget": { "toolCalls": 5 } }),
        )
        .await;
    assert!(again.success, "re-create failed: {again:?}");
    let budget = data(&worker, "get_budget", &json!({})).await;
    assert_eq!(
        budget,
        json!({
            "budget": untouched(&session_id(&worker), &json!({ "toolCalls": 5 }), &amounts(0, 0, 5)),
        })
    );
}

/// A fork of a persisted session that has a budget replaces it with a
/// session that draws from the same account: the budget reads the same,
/// spent included, as the fork's agent sees it (no budget is lost to the
/// replacement, B7).
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_fork_draws_from_the_budget_of_the_session_it_forks() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = worker(dir.path());
    let created = worker
        .dispatch(
            "create",
            &json!({
                "cwd": dir.path(),
                "sessionDir": dir.path().join("sessions"),
                "budget": { "tokens": 1_000_000, "requests": 10 },
            }),
        )
        .await;
    assert!(created.success, "create failed: {created:?}");
    let prompted = worker
        .dispatch(
            "prompt_and_wait",
            &json!({ "activeSessionId": "budget-session", "message": "first" }),
        )
        .await;
    assert!(prompted.success, "prompt failed: {prompted:?}");
    let source_id = session_id(&worker);
    let source = data(&worker, "get_budget", &json!({})).await;
    let tree = data(
        &worker,
        "get_session_tree",
        &json!({ "activeSessionId": "budget-session" }),
    )
    .await;
    let answer = tree["flatNodes"][1]["entry"]["id"].clone();
    let forked = worker
        .dispatch(
            "fork",
            &json!({ "activeSessionId": "budget-session", "entryId": answer, "position": "at" }),
        )
        .await;
    assert!(forked.success, "fork failed: {forked:?}");
    let fork_id = session_id(&worker);
    let forked = data(&worker, "get_budget", &json!({})).await;

    let mut expected = source.clone();
    expected["budget"]["agentSessionId"] = json!(fork_id);
    assert_eq!(
        (
            fork_id == source_id,
            source["budget"]["spent"]["requests"].clone(),
            forked
        ),
        (false, json!(1), expected)
    );
}
