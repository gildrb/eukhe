use std::sync::Arc;

use serde_json::{json, Value};

use crate::worker::Worker;

const SESSION: &str = "tree-session";

async fn created_worker(responses: &[&str]) -> (tempfile::TempDir, Arc<Worker>) {
    let dir = tempfile::tempdir().unwrap();
    let config = crate::worker::WorkerConfig {
        socket_path: dir.path().join("worker.sock"),
        supervisor_socket_path: std::path::PathBuf::new(),
        token: "token".to_owned(),
        worker_instance_id: String::new(),
        active_session_id: SESSION.to_owned(),
        agent_dir: dir.path().join("agent"),
        recovery_journal_path: dir.path().join("recovery.jsonl"),
        telemetry_disabled: None,
        script: Some(json!({ "responses": responses })),
    };
    let worker = Arc::new(Worker::new(config, None));
    let created = worker
        .dispatch("create", &json!({ "cwd": dir.path().to_string_lossy() }))
        .await;
    assert!(created.success, "create failed: {created:?}");
    (dir, worker)
}

async fn command(worker: &Worker, name: &str, payload: Value) -> Value {
    let mut payload = payload;
    payload["activeSessionId"] = json!(SESSION);
    let response = worker.dispatch(name, &payload).await;
    assert!(response.success, "{name} failed: {response:?}");
    response.data.unwrap_or(Value::Null)
}

async fn prompt(worker: &Worker, text: &str) {
    command(worker, "prompt_and_wait", json!({ "message": text })).await;
}

/// `(type, role or "", id, parentId)` of every flat node.
fn shape(tree: &Value) -> Vec<(String, String, String, Option<String>)> {
    tree["flatNodes"]
        .as_array()
        .expect("flatNodes")
        .iter()
        .map(|node| {
            let entry = &node["entry"];
            (
                entry["type"].as_str().unwrap().to_owned(),
                entry["message"]["role"]
                    .as_str()
                    .unwrap_or_default()
                    .to_owned(),
                entry["id"].as_str().unwrap().to_owned(),
                entry["parentId"].as_str().map(str::to_owned),
            )
        })
        .collect()
}

/// Two answered prompts: the harness-digest row rides the first turn only
/// (the digest is fresh afterwards), so the ids are
/// user/digest/assistant/user/assistant (the durable tree shows every
/// stored entry, the old `flat_tree` included display rows too).
async fn two_turns(worker: &Worker) -> [String; 5] {
    prompt(worker, "first").await;
    prompt(worker, "second").await;
    let tree = command(worker, "get_session_tree", json!({})).await;
    let ids: Vec<String> = shape(&tree).into_iter().map(|node| node.2).collect();
    assert_eq!(ids.len(), 5, "{tree}");
    [
        ids[0].clone(),
        ids[1].clone(),
        ids[2].clone(),
        ids[3].clone(),
        ids[4].clone(),
    ]
}

async fn message_roles(worker: &Worker) -> Vec<String> {
    command(worker, "get_messages", json!({})).await["messages"]
        .as_array()
        .unwrap()
        .iter()
        .map(|message| message["role"].as_str().unwrap().to_owned())
        .collect()
}

/// `get_session_tree`: the shown entries chained by `parentId`, TS-typed
/// (they parse as session entries), and the leaf at the newest one.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn session_tree_chains_the_transcript() {
    let (_dir, worker) = created_worker(&["one", "two"]).await;
    let [user1, digest1, assistant1, user2, assistant2] = two_turns(&worker).await;
    let tree = command(&worker, "get_session_tree", json!({})).await;
    assert_eq!(
        shape(&tree),
        vec![
            ("message".into(), "user".into(), user1.clone(), None),
            (
                "custom_message".into(),
                String::new(),
                digest1.clone(),
                Some(user1)
            ),
            (
                "message".into(),
                "assistant".into(),
                assistant1.clone(),
                Some(digest1)
            ),
            (
                "message".into(),
                "user".into(),
                user2.clone(),
                Some(assistant1)
            ),
            (
                "message".into(),
                "assistant".into(),
                assistant2.clone(),
                Some(user2)
            ),
        ]
    );
    assert_eq!(tree["leafId"], json!(assistant2));
    for node in tree["flatNodes"].as_array().unwrap() {
        let entry: eukhe_types::session::FileEntry =
            serde_json::from_value(node["entry"].clone()).unwrap();
        assert!(
            !matches!(entry, eukhe_types::session::FileEntry::Unknown { .. }),
            "{node}"
        );
    }
}

/// `get_user_messages_for_forking`: the user messages with their text.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn user_messages_for_forking_lists_the_prompts() {
    let (_dir, worker) = created_worker(&["one", "two"]).await;
    let [user1, _, _, user2, _] = two_turns(&worker).await;
    let data = command(&worker, "get_user_messages_for_forking", json!({})).await;
    assert_eq!(
        data,
        json!({ "messages": [
            { "entryId": user1, "text": "first" },
            { "entryId": user2, "text": "second" },
        ] })
    );
}

/// `set_session_entry_label`: the label shows on its node; a null label
/// clears it; an unknown entry answers the TS error.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn labels_set_and_clear() {
    let (_dir, worker) = created_worker(&["one", "two"]).await;
    let [user1, ..] = two_turns(&worker).await;
    command(
        &worker,
        "set_session_entry_label",
        json!({ "entryId": user1, "label": "start" }),
    )
    .await;
    let tree = command(&worker, "get_session_tree", json!({})).await;
    let node = &tree["flatNodes"][0];
    assert_eq!(node["label"], "start");
    assert!(node["labelTimestamp"]
        .as_str()
        .is_some_and(|stamp| !stamp.is_empty()));
    command(
        &worker,
        "set_session_entry_label",
        json!({ "entryId": user1, "label": null }),
    )
    .await;
    let tree = command(&worker, "get_session_tree", json!({})).await;
    assert!(tree["flatNodes"][0].get("label").is_none(), "{tree}");
    let missing = worker
        .dispatch(
            "set_session_entry_label",
            &json!({ "activeSessionId": SESSION, "entryId": "999999", "label": "x" }),
        )
        .await;
    assert_eq!(missing.error.as_deref(), Some("Entry 999999 not found"));
}

/// `navigate_tree` onto a user message: the leaf moves before it and its
/// text returns for the editor; navigating back to the old leaf restores
/// the branch (the conversation that already ends there).
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn navigate_tree_moves_the_leaf_and_back() {
    let (_dir, worker) = created_worker(&["one", "two"]).await;
    let [_, _, assistant1, user2, assistant2] = two_turns(&worker).await;
    let moved = command(&worker, "navigate_tree", json!({ "targetId": user2 })).await;
    assert_eq!(moved, json!({ "cancelled": false, "editorText": "second" }));
    let tree = command(&worker, "get_session_tree", json!({})).await;
    assert_eq!(tree["leafId"], json!(assistant1));
    assert_eq!(
        message_roles(&worker).await,
        ["user", "custom", "assistant"]
    );

    // Already there: a no-op.
    let again = command(&worker, "navigate_tree", json!({ "targetId": assistant1 })).await;
    assert_eq!(again, json!({ "cancelled": false }));

    let back = command(&worker, "navigate_tree", json!({ "targetId": assistant2 })).await;
    assert_eq!(back, json!({ "cancelled": false }));
    let tree = command(&worker, "get_session_tree", json!({})).await;
    assert_eq!(tree["leafId"], json!(assistant2));
    assert_eq!(shape(&tree).len(), 5, "no duplicate branch: {tree}");
    assert_eq!(
        message_roles(&worker).await,
        ["user", "custom", "assistant", "user", "assistant"]
    );

    let missing = worker
        .dispatch(
            "navigate_tree",
            &json!({ "activeSessionId": SESSION, "targetId": "424242" }),
        )
        .await;
    assert_eq!(missing.error.as_deref(), Some("Entry 424242 not found"));
}

/// `navigate_tree` with `summarize`: the abandoned branch's summary lands
/// in the moved-to conversation as a `branch_summary` entry parented on
/// the target, the label goes on it, and the next turn sees it.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn navigate_tree_writes_the_branch_summary() {
    let (_dir, worker) = created_worker(&["one", "two", "branch notes"]).await;
    let [_, _, assistant1, ..] = two_turns(&worker).await;
    let moved = command(
        &worker,
        "navigate_tree",
        json!({ "targetId": assistant1, "summarize": true, "label": "explored" }),
    )
    .await;
    assert_eq!(moved["cancelled"], false, "{moved}");
    let summary = &moved["summaryEntry"];
    assert_eq!(summary["type"], "branch_summary", "{moved}");
    assert_eq!(summary["parentId"], json!(assistant1));
    assert_eq!(summary["fromId"], json!(assistant1));
    let text = summary["summary"].as_str().unwrap();
    assert!(text.contains("branch notes"), "{text}");
    let tree = command(&worker, "get_session_tree", json!({})).await;
    assert_eq!(tree["leafId"], summary["id"]);
    let node = tree["flatNodes"]
        .as_array()
        .unwrap()
        .iter()
        .find(|node| node["entry"]["id"] == summary["id"])
        .expect("summary node");
    assert_eq!(node["label"], "explored");
    assert_eq!(
        message_roles(&worker).await,
        ["user", "custom", "assistant", "branchSummary"]
    );
}

/// `fork`: `position: "at"` keeps the history through the entry; the
/// default forks before a user message and answers its text; a non-user
/// entry is not a fork point. A persisted session forks into a new storage
/// (a new session id) that replaces the live session; the fork inherits the
/// entries (and their ids) through the fork point.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn fork_continues_on_a_fork() {
    let (_dir, worker) = created_worker(&["one", "two", "three"]).await;
    let [_, _, assistant1, _, _] = two_turns(&worker).await;
    let state_before = command(&worker, "get_state", json!({})).await;

    let at = command(
        &worker,
        "fork",
        json!({ "entryId": assistant1, "position": "at" }),
    )
    .await;
    assert_eq!(at, json!({ "cancelled": false }));
    let tree = command(&worker, "get_session_tree", json!({})).await;
    assert_eq!(tree["leafId"], json!(assistant1));
    // A new storage, a new session id.
    let state_after = command(&worker, "get_state", json!({})).await;
    assert_ne!(state_after["sessionId"], state_before["sessionId"]);

    // A turn on the fork, then a fork before its user message.
    prompt(&worker, "third").await;
    let tree = command(&worker, "get_session_tree", json!({})).await;
    let user3 = shape(&tree)
        .into_iter()
        .rev()
        .find(|node| node.1 == "user")
        .expect("the fork's user message")
        .2;
    let before = command(&worker, "fork", json!({ "entryId": user3 })).await;
    assert_eq!(
        before,
        json!({ "cancelled": false, "selectedText": "third" })
    );
    let tree = command(&worker, "get_session_tree", json!({})).await;
    assert_eq!(tree["leafId"], json!(assistant1));

    let invalid = worker
        .dispatch(
            "fork",
            &json!({ "activeSessionId": SESSION, "entryId": assistant1 }),
        )
        .await;
    assert_eq!(
        invalid.error.as_deref(),
        Some("Invalid entry ID for forking")
    );
}
