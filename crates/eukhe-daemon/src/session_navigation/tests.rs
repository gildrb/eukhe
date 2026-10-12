use std::path::Path;
use std::sync::Arc;

use serde_json::{json, Value};

use crate::protocol::DaemonErrorInfo;
use crate::worker::Worker;

const SESSION: &str = "nav-session";

async fn created_worker(dir: &Path, cwd: &Path) -> Arc<Worker> {
    let config = crate::worker::WorkerConfig {
        socket_path: dir.join("worker.sock"),
        supervisor_socket_path: std::path::PathBuf::new(),
        token: "token".to_owned(),
        worker_instance_id: String::new(),
        active_session_id: SESSION.to_owned(),
        agent_dir: dir.join("agent"),
        recovery_journal_path: dir.join("recovery.jsonl"),
        script: Some(json!({ "responses": ["one", "two", "three"] })),
    };
    let worker = Arc::new(Worker::new(config, None));
    let created = worker
        .dispatch("create", &json!({ "cwd": cwd.to_string_lossy() }))
        .await;
    assert!(created.success, "create failed: {created:?}");
    worker
}

async fn dispatch(worker: &Worker, name: &str, payload: Value) -> crate::protocol::DaemonResponse {
    let mut payload = payload;
    payload["activeSessionId"] = json!(SESSION);
    worker.dispatch(name, &payload).await
}

async fn state(worker: &Worker) -> Value {
    let response = dispatch(worker, "get_state", json!({})).await;
    assert!(response.success, "{response:?}");
    response.data.unwrap()
}

/// The shown entries the hosted session's storage holds (read from the
/// storage, so no event delivery race).
async fn message_count(worker: &Worker) -> usize {
    let response = dispatch(worker, "get_session_tree", json!({})).await;
    response.data.unwrap()["flatNodes"]
        .as_array()
        .unwrap()
        .len()
}

/// A legacy session file recording `cwd`.
fn legacy_session(path: &Path, id: &str, cwd: &Path) {
    std::fs::write(
        path,
        format!(
            "{}\n",
            json!({
                "type": "session",
                "id": id,
                "timestamp": "2026-09-21T00:00:00.000Z",
                "cwd": cwd.to_string_lossy(),
            })
        ),
    )
    .unwrap();
}

/// `new_session` answers `{ cancelled: false }`, moves onto a fresh
/// session in the live cwd, and the old session reopens by
/// `switch_session` with its history (its storage lease was released).
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn new_session_then_switch_back() {
    let dir = tempfile::tempdir().unwrap();
    let worker = created_worker(dir.path(), dir.path()).await;
    let prompted = dispatch(&worker, "prompt_and_wait", json!({ "message": "hello" })).await;
    assert!(prompted.success, "{prompted:?}");
    let before = state(&worker).await;
    assert_eq!(message_count(&worker).await, 3, "user, digest, assistant");

    let fresh = dispatch(&worker, "new_session", json!({})).await;
    assert_eq!(fresh.data, Some(json!({ "cancelled": false })), "{fresh:?}");
    let after = state(&worker).await;
    assert_ne!(after["sessionId"], before["sessionId"]);
    assert_eq!(after["cwd"], before["cwd"]);
    assert_eq!(message_count(&worker).await, 0);

    let switched = dispatch(
        &worker,
        "switch_session",
        json!({ "sessionPath": before["sessionFile"] }),
    )
    .await;
    assert!(switched.success, "{switched:?}");
    assert_eq!(state(&worker).await["sessionId"], before["sessionId"]);
    assert_eq!(message_count(&worker).await, 3, "user, digest, assistant");

    // Switching to the live session itself reopens it.
    let same = dispatch(
        &worker,
        "switch_session",
        json!({ "sessionPath": before["sessionFile"] }),
    )
    .await;
    assert!(same.success, "{same:?}");
    assert_eq!(message_count(&worker).await, 3, "user, digest, assistant");
}

/// A missing switch target fails before anything is retired.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn switch_session_fails_on_missing_targets() {
    let dir = tempfile::tempdir().unwrap();
    let worker = created_worker(dir.path(), dir.path()).await;
    let before = state(&worker).await;
    let missing = dir.path().join("definitely-missing.jsonl");
    let response = dispatch(
        &worker,
        "switch_session",
        json!({ "sessionPath": missing.to_string_lossy() }),
    )
    .await;
    assert!(!response.success, "{response:?}");
    assert!(
        response
            .error
            .as_deref()
            .unwrap_or_default()
            .contains(&*missing.to_string_lossy()),
        "{response:?}"
    );
    assert_eq!(state(&worker).await["sessionId"], before["sessionId"]);
}

/// The switch cwd rebind: the worker moves onto the target's recorded
/// cwd; a target whose stored cwd is gone fails at the prepare with the
/// TS `MissingSessionCwdError` text, leaving the live session; a
/// `cwdOverride` wins over the stored cwd.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn switch_session_rebinds_the_cwd() {
    let dir = tempfile::tempdir().unwrap();
    let worker = created_worker(dir.path(), dir.path()).await;
    let sessions = dir.path().join("elsewhere");
    std::fs::create_dir_all(&sessions).unwrap();
    let target_cwd = tempfile::tempdir().unwrap();
    let target = sessions.join("0192a000-0000-7000-8000-00000000aa01.jsonl");
    legacy_session(
        &target,
        "0192a000-0000-7000-8000-00000000aa01",
        target_cwd.path(),
    );
    let switched = dispatch(
        &worker,
        "switch_session",
        json!({ "sessionPath": target.to_string_lossy() }),
    )
    .await;
    assert!(switched.success, "{switched:?}");
    let target_cwd_text = target_cwd.path().to_string_lossy().to_string();
    assert_eq!(state(&worker).await["cwd"], json!(target_cwd_text));

    let gone_cwd = dir.path().join("missing-cwd");
    let gone = sessions.join("0192a000-0000-7000-8000-00000000aa02.jsonl");
    legacy_session(&gone, "0192a000-0000-7000-8000-00000000aa02", &gone_cwd);
    let failed = dispatch(
        &worker,
        "switch_session",
        json!({ "sessionPath": gone.to_string_lossy() }),
    )
    .await;
    assert!(
        failed
            .error
            .as_deref()
            .unwrap_or_default()
            .starts_with("Stored session working directory does not exist:"),
        "{failed:?}"
    );
    assert_eq!(state(&worker).await["cwd"], json!(target_cwd_text));

    let overridden = dispatch(
        &worker,
        "switch_session",
        json!({
            "sessionPath": gone.to_string_lossy(),
            "cwdOverride": dir.path().to_string_lossy(),
        }),
    )
    .await;
    assert!(overridden.success, "{overridden:?}");
    assert_eq!(
        state(&worker).await["cwd"],
        json!(dir.path().to_string_lossy())
    );
}

/// `import_jsonl` answers the TS import error for a missing input file.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn import_jsonl_answers_file_not_found() {
    let dir = tempfile::tempdir().unwrap();
    let worker = created_worker(dir.path(), dir.path()).await;
    let missing = dir.path().join("no-such-import.jsonl");
    let response = dispatch(
        &worker,
        "import_jsonl",
        json!({ "inputPath": missing.to_string_lossy() }),
    )
    .await;
    assert_eq!(
        response.error.as_deref(),
        Some(format!("File not found: {}", missing.display()).as_str())
    );
    assert_eq!(
        response.error_info,
        Some(DaemonErrorInfo::SessionImportFileNotFound {
            file_path: missing.display().to_string()
        })
    );
}

/// `import_jsonl`: a stored cwd that is gone answers the TS text plus the
/// typed error info (the fallback is the live cwd); a good file is copied
/// into the sessions dir and opened.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn import_jsonl_imports_and_checks_the_cwd() {
    let dir = tempfile::tempdir().unwrap();
    let worker = created_worker(dir.path(), dir.path()).await;
    let inputs = tempfile::tempdir().unwrap();
    let gone_cwd = inputs.path().join("gone-cwd");
    let gone = inputs
        .path()
        .join("0192a000-0000-7000-8000-00000000bb01.jsonl");
    legacy_session(&gone, "0192a000-0000-7000-8000-00000000bb01", &gone_cwd);
    let response = dispatch(
        &worker,
        "import_jsonl",
        json!({ "inputPath": gone.to_string_lossy() }),
    )
    .await;
    match response.error_info {
        Some(DaemonErrorInfo::MissingSessionCwd { issue }) => {
            assert_eq!(issue["sessionCwd"], json!(gone_cwd.to_string_lossy()));
            assert_eq!(issue["fallbackCwd"], json!(dir.path().to_string_lossy()));
        }
        other => panic!("expected the typed missing-cwd error info, got {other:?}"),
    }

    let good = inputs
        .path()
        .join("0192a000-0000-7000-8000-00000000bb02.jsonl");
    legacy_session(&good, "0192a000-0000-7000-8000-00000000bb02", inputs.path());
    let imported = dispatch(
        &worker,
        "import_jsonl",
        json!({ "inputPath": good.to_string_lossy() }),
    )
    .await;
    assert_eq!(
        imported.data,
        Some(json!({ "cancelled": false })),
        "{imported:?}"
    );
    let state = state(&worker).await;
    assert_eq!(state["sessionId"], "0192a000-0000-7000-8000-00000000bb02");
    assert_eq!(state["cwd"], json!(inputs.path().to_string_lossy()));
}

/// `import_jsonl` never overwrites a different session file already at
/// the copy's destination: the import fails naming the path, and the
/// existing file and the live session stay as they were.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn import_jsonl_refuses_to_overwrite_a_different_session_file() {
    let dir = tempfile::tempdir().unwrap();
    let worker = created_worker(dir.path(), dir.path()).await;
    let before = state(&worker).await;
    let sessions = Path::new(before["sessionFile"].as_str().unwrap())
        .parent()
        .unwrap()
        .to_path_buf();
    let id = "0192a000-0000-7000-8000-00000000bb03";
    let existing = sessions.join(format!("{id}.jsonl"));
    legacy_session(&existing, id, dir.path());
    let existing_bytes = std::fs::read(&existing).unwrap();
    let inputs = tempfile::tempdir().unwrap();
    let input = inputs.path().join(format!("{id}.jsonl"));
    legacy_session(&input, id, inputs.path());

    let response = dispatch(
        &worker,
        "import_jsonl",
        json!({ "inputPath": input.to_string_lossy() }),
    )
    .await;
    assert_eq!(
        response.error,
        Some(format!(
            "session file {} already exists",
            existing.display()
        )),
        "{response:?}"
    );
    assert_eq!(std::fs::read(&existing).unwrap(), existing_bytes);
    assert_eq!(state(&worker).await["sessionId"], before["sessionId"]);
}

/// The import copy publishes the source's bytes and leaves no temp file;
/// republishing the same bytes (an import retried after its cwd check)
/// keeps the published copy.
#[test]
fn import_copy_publishes_without_leaving_a_temp_file() {
    let inputs = tempfile::tempdir().unwrap();
    let source = inputs.path().join("input.jsonl");
    std::fs::write(&source, "{\"type\":\"session\"}\n").unwrap();
    let sessions = tempfile::tempdir().unwrap();
    let destination = sessions.path().join("copied.jsonl");
    let entries = || {
        std::fs::read_dir(sessions.path())
            .unwrap()
            .map(|entry| entry.unwrap().file_name())
            .collect::<Vec<_>>()
    };
    for _ in 0..2 {
        super::publish_import_copy(&source, &destination).unwrap();
        assert_eq!(entries(), vec![std::ffi::OsString::from("copied.jsonl")]);
        assert_eq!(
            std::fs::read(&destination).unwrap(),
            std::fs::read(&source).unwrap()
        );
    }
}
