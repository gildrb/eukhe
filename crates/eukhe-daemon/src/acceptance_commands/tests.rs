//! The acceptance commands over an in-process worker (a scripted faux
//! session).

use std::path::Path;
use std::sync::Arc;

use eukhe_types::acceptance::{AcceptanceLabel, AcceptanceState, CheckSpec};
use serde_json::{json, Value};

use crate::protocol::DaemonResponse;
use crate::worker::{Worker, WorkerConfig};

fn worker_config(dir: &Path) -> WorkerConfig {
    WorkerConfig {
        socket_path: dir.join("worker.sock"),
        supervisor_socket_path: std::path::PathBuf::new(),
        token: "token".to_string(),
        worker_instance_id: String::new(),
        active_session_id: "acceptance-session".to_string(),
        agent_dir: dir.join("agent"),
        recovery_journal_path: dir.join("recovery.jsonl"),
        script: Some(json!({ "modelId": "faux-1", "responses": ["ack"] })),
    }
}

/// A created in-memory session on `dir` (cwd and agent dir under it).
async fn created_worker(dir: &Path) -> Arc<Worker> {
    std::fs::create_dir_all(dir.join("agent")).expect("agent dir");
    let worker = Arc::new(Worker::new(worker_config(dir), None));
    let created = worker
        .dispatch("create", &json!({ "noSession": true, "cwd": dir }))
        .await;
    assert!(created.success, "create failed: {created:?}");
    worker
}

fn state_of(response: DaemonResponse) -> AcceptanceState {
    assert!(response.success, "{}: {response:?}", response.command);
    serde_json::from_value(response.data.expect("the acceptance")).expect("an acceptance state")
}

fn specs_of(state: &AcceptanceState) -> Vec<CheckSpec> {
    state
        .checks
        .iter()
        .map(|check| check.spec.clone())
        .collect()
}

fn command_check(command: &str) -> CheckSpec {
    CheckSpec::Command {
        command: command.to_owned(),
        expect: 0,
        timeout_ms: None,
        protect: Vec::new(),
    }
}

/// `set_acceptance` sets the checks as the task's owner: the explicit
/// checks, then the intent check unless `intent` is false; every check
/// starts unjudged and the revision grows. `get_acceptance` reads the
/// same state. A check with no command and more checks than a task may
/// carry answer as the command's error and change nothing.
#[tokio::test]
async fn set_acceptance_command_sets_the_checks_as_the_owner() {
    let dir = tempfile::tempdir().expect("tempdir");
    let worker = created_worker(dir.path()).await;

    let set = state_of(
        worker
            .dispatch(
                "set_acceptance",
                &json!({
                    "checks": [{ "kind": "command", "command": "true" }],
                    "maxReturns": 2,
                }),
            )
            .await,
    );
    assert_eq!(
        specs_of(&set),
        vec![command_check("true"), CheckSpec::intent()]
    );
    assert_eq!(set.max_returns, 2);
    assert_eq!(set.label, AcceptanceLabel::Unverified);
    assert!(!set.claimed);
    assert!(set.checks.iter().all(|check| check.result.is_none()));

    let read = state_of(worker.dispatch("get_acceptance", &json!({})).await);
    assert_eq!(read.checks, set.checks);
    assert_eq!(read.revision, set.revision);

    let judge = json!({ "kind": "judge", "condition": "the README says how to run it" });
    let replaced = state_of(
        worker
            .dispatch(
                "set_acceptance",
                &json!({ "checks": [judge.clone()], "intent": false }),
            )
            .await,
    );
    let judge: CheckSpec = serde_json::from_value(judge).expect("a judge check");
    assert_eq!(specs_of(&replaced), vec![judge]);
    assert!(replaced.revision > set.revision);
    assert_eq!(
        replaced.max_returns, 2,
        "an absent cap keeps the current one"
    );

    let blank = worker
        .dispatch(
            "set_acceptance",
            &json!({ "checks": [{ "kind": "command", "command": "  " }] }),
        )
        .await;
    assert!(!blank.success);
    assert_eq!(blank.command, "set_acceptance");
    let error = blank.error.unwrap_or_default();
    assert!(error.contains("needs a command"), "{error}");

    let many: Vec<Value> = (0..65)
        .map(|_| json!({ "kind": "command", "command": "true" }))
        .collect();
    let too_many = worker
        .dispatch(
            "set_acceptance",
            &json!({ "checks": many, "intent": false }),
        )
        .await;
    assert!(!too_many.success);
    let error = too_many.error.unwrap_or_default();
    assert!(error.contains("at most 64 checks"), "{error}");

    let kept = state_of(worker.dispatch("get_acceptance", &json!({})).await);
    assert_eq!(kept.checks, replaced.checks);
    assert_eq!(kept.revision, replaced.revision);
}
