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
            script: Some(json!({ "modelId": "faux-1", "responses": ["ack", "ack"] })),
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

/// The wire report of an interactive run whose `limits` the principal set
/// (the other dimensions until finished) and that nothing was spent from,
/// as its owner sees it: `free` is all of it.
fn untouched(session_id: &str, limits: &Value, free: &Value) -> Value {
    let zero = amounts(0, 0, 0);
    let source = |key: &str| match limits.get(key) {
        Some(_) => json!({ "source": "set" }),
        None => json!({ "source": "until_finished" }),
    };
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
        "kind": "interactive",
        "sources": {
            "costMicros": source("costMicros"),
            "tokens": source("tokens"),
            "timeMs": source("timeMs"),
            "toolCalls": source("toolCalls"),
            "requests": source("requests"),
        },
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

/// The report of a session without a budget yet that shows only what its
/// next run starts with (`next`).
fn next_only(session_id: &str, next: &Value) -> Value {
    let zero = amounts(0, 0, 0);
    json!({
        "sessionId": session_id,
        "agentSessionId": session_id,
        "limits": {},
        "free": zero,
        "held": zero,
        "spent": zero,
        "lent": zero,
        "over": zero,
        "phase": "working",
        "next": next,
    })
}

/// B15: a session has no budget until one is set; limits set while it
/// runs nothing are its next run's: they read back as such, the next task
/// runs capped by them, and they are then used up.
#[tokio::test]
async fn a_budget_set_while_idle_caps_the_next_task() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created(dir.path()).await;
    let id = session_id(&worker);
    let before = data(&worker, "get_budget", &json!({})).await;
    let limits = json!({ "costMicros": 5_000_000, "toolCalls": 40 });
    let set = data(&worker, "set_budget", &json!({ "limits": limits })).await;
    let pending = data(&worker, "get_budget", &json!({})).await;
    let prompted = worker
        .dispatch(
            "prompt_and_wait",
            &json!({ "activeSessionId": "budget-session", "message": "the task" }),
        )
        .await;
    assert!(prompted.success, "prompt failed: {prompted:?}");
    let ran = data(&worker, "get_budget", &json!({})).await;
    let shown = next_only(&id, &json!({ "limits": limits }));
    assert_eq!(
        (
            before,
            set,
            pending,
            ran["budget"]["limits"].clone(),
            ran["budget"]["sources"]["costMicros"].clone(),
            ran["budget"]["spent"]["requests"].clone(),
            ran["budget"].get("next").cloned(),
        ),
        (
            json!({ "budget": null }),
            json!({ "budget": shown }),
            json!({ "budget": shown }),
            limits,
            json!({ "source": "set" }),
            json!(1),
            None,
        )
    );
}

/// A second `set_budget` while idle goes over the first for the next run;
/// a `set_budget` without limits is refused before the ledger is asked.
#[tokio::test]
async fn a_second_set_budget_while_idle_goes_over_the_first() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created(dir.path()).await;
    let id = session_id(&worker);
    let unnamed = refusal(&worker, "set_budget", &json!({})).await;
    data(
        &worker,
        "set_budget",
        &json!({ "limits": { "tokens": 100_000, "requests": 9 } }),
    )
    .await;
    let again = data(&worker, "set_budget", &json!({ "limits": { "tokens": 7 } })).await;
    assert_eq!(
        (unnamed, again),
        (
            (false, None, "limits is required".to_string()),
            json!({
                "budget": next_only(&id, &json!({ "limits": { "tokens": 7, "requests": 9 } })),
            }),
        )
    );
}

/// `add_budget` while idle adds up for the next run.
#[tokio::test]
async fn add_budget_while_idle_adds_up_for_the_next_run() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created(dir.path()).await;
    let id = session_id(&worker);
    data(
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
        second,
        json!({
            "budget": next_only(
                &id,
                &json!({ "added": amounts(2_000_000, 60_000, 0) }),
            ),
        })
    );
}

/// `set_budget` sends one `budget_update` with the report it answers, and
/// the attach snapshot's state carries the same report from then on (B8).
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
    let report = next_only(&session_id(&worker), &json!({ "limits": limits }));
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

/// A session without a budget has no ledger to audit; the ledger of a run
/// replays exactly (B9).
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
    let prompted = worker
        .dispatch(
            "prompt_and_wait",
            &json!({ "activeSessionId": "budget-session", "message": "the task" }),
        )
        .await;
    assert!(prompted.success, "prompt failed: {prompted:?}");
    let audit = data(&worker, "audit_budget", &json!({})).await;
    assert_eq!(
        (
            without,
            audit["audit"]["exact"].clone(),
            audit["audit"]["firstMismatch"].clone(),
            audit["audit"]["settled"] == audit["audit"]["spent"],
        ),
        (
            (false, None, format!("session {id} has no budget")),
            json!(true),
            Value::Null,
            true,
        )
    );
}

/// The create config's `budget` is the new session's budget before its
/// first turn; a later create of the same session that names another
/// budget sets that one, as the principal's limits for its runs (B15,
/// B19).
#[tokio::test]
async fn a_later_create_sets_the_budget_it_names() {
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
    let reset = data(&second, "get_budget", &json!({})).await;
    assert_eq!(
        (set, reset),
        (
            json!({ "budget": untouched(id, &json!({ "toolCalls": 12 }), &amounts(0, 0, 12)) }),
            json!({ "budget": untouched(id, &json!({ "toolCalls": 99 }), &amounts(0, 0, 99)) }),
        )
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

/// A message sent while the session is idle starts a fresh interactive
/// run: its `/b` prefix fills that run only, and the next message's run
/// goes until finished again with limits off (B15, B20). A prefix that
/// does not read is refused by its word, marked a prefix refusal, and
/// nothing is sent.
#[tokio::test]
async fn each_idle_message_starts_its_own_run() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created(dir.path()).await;
    let refused = worker
        .dispatch(
            "prompt_and_wait",
            &json!({ "activeSessionId": "budget-session", "message": "/b cost=abc first" }),
        )
        .await;
    assert_eq!(
        (
            refused.success,
            refused.error.as_deref(),
            refused.error_info.as_ref()
        ),
        (
            false,
            Some("cost \"abc\": expected dollars, like 1.50 or $1.50"),
            Some(&eukhe_types::daemon::DaemonErrorInfo::PrefixRefused)
        ),
        "{refused:?}"
    );
    let prompted = worker
        .dispatch(
            "prompt_and_wait",
            &json!({
                "activeSessionId": "budget-session",
                "message": "/b quick calls=9 first",
            }),
        )
        .await;
    assert!(prompted.success, "prompt failed: {prompted:?}");
    let first = data(&worker, "get_budget", &json!({})).await;
    let prompted = worker
        .dispatch(
            "prompt_and_wait",
            &json!({ "activeSessionId": "budget-session", "message": "second" }),
        )
        .await;
    assert!(prompted.success, "prompt failed: {prompted:?}");
    let second = data(&worker, "get_budget", &json!({})).await;
    let pick = |budget: &Value| {
        (
            budget["budget"]["kind"].clone(),
            budget["budget"]["limits"].clone(),
            budget["budget"]["sources"].clone(),
            budget["budget"]["spent"]["requests"].clone(),
        )
    };
    assert_eq!(
        (pick(&first), pick(&second)),
        (
            (
                json!("interactive"),
                json!({ "timeMs": 3_600_000, "toolCalls": 9, "requests": 800 }),
                json!({
                    "costMicros": { "source": "until_finished" },
                    "tokens": { "source": "until_finished" },
                    "timeMs": { "source": "preset", "name": "quick" },
                    "toolCalls": { "source": "set" },
                    "requests": { "source": "preset", "name": "quick" },
                }),
                json!(1),
            ),
            (json!("interactive"), json!({}), Value::Null, json!(1)),
        )
    );
}
