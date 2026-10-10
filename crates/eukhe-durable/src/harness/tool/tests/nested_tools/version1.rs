//! `describe("tool task version 1 records")`.

use std::path::{Path, PathBuf};
use std::sync::atomic::Ordering;

use eukhe_chord::json::{to_json, JsonValue};
use eukhe_types::pi_ai::Message;
use serde_json::json;

use super::super::nested_support::{
    call_with, echo_tool, open_sqlite, plain, results, sqlite, sqlite_path,
};
use super::super::support::result_text;
use super::setup;
use crate::entries::ASSISTANT_ENTRY;
use crate::harness::tests::chat_support::{all_entries, ChatSetup};
use crate::harness::tests::support::{add_tool, context};
use crate::harness::tool::{ToolTaskInput, TOOL_TASK};
use crate::types::{StorageWrite, TaskId, TaskOptions, TaskOwnership, TaskState, TypedEntryDraft};

/// TS `storeVersion1(setup, checkpoint)`: store a live tool task for call
/// `c1` of an assistant entry, close, and rewrite its record as version 1
/// stored it: `{ assistant, callId }` input at version 1, with `checkpoint`.
/// Returns the storage directory, its path, and the task ID.
async fn store_version1(
    setup: &ChatSetup,
    checkpoint: &str,
) -> (tempfile::TempDir, PathBuf, TaskId) {
    let (directory, path) = sqlite_path("pi-durable-tool-v1-");
    // No submission, so the Harness never starts scheduling and the task stays pending.
    let chat = open_sqlite(&path, setup).await;
    let root_id = chat.root.id();
    let tool = TOOL_TASK.as_definition_ref();
    let id = chat
        .root
        .commit(
            move |tx| async move {
                let message = call_with("echo", json!({ "text": "old" }), "c1");
                let entry = tx
                    .append_typed_entry(
                        &ASSISTANT_ENTRY,
                        root_id,
                        TypedEntryDraft {
                            model: Some(vec![Message::Assistant(message)]),
                            ..TypedEntryDraft::default()
                        },
                    )
                    .await?;
                let input = ToolTaskInput::Model {
                    assistant: entry.entry().id,
                    call_id: "c1".to_owned(),
                };
                tx.create_task(
                    tool,
                    to_json(&input)?,
                    TaskOptions {
                        ownership: TaskOwnership::Conversation,
                        conversation_id: None,
                        background: None,
                        abandon_on_restart: None,
                    },
                )
                .await
            },
            context(),
        )
        .await
        .unwrap();
    chat.harness.close(context()).await.unwrap();
    rewrite_as_version1(&path, id, checkpoint).await;
    (directory, path, id)
}

async fn rewrite_as_version1(path: &Path, id: TaskId, checkpoint: &str) {
    let storage = sqlite(path).await;
    let mut record = storage.task(id, context()).await.unwrap().unwrap();
    let mut input = plain(&record.input);
    input.as_object_mut().unwrap().remove("kind");
    record.version = 1;
    record.input = to_json(&input).unwrap();
    let checkpoint = JsonValue::parse(checkpoint).unwrap();
    record.state = match record.state {
        TaskState::Pending { .. } => TaskState::Pending { checkpoint },
        other => panic!("a stored tool task is pending: {other:?}"),
    };
    storage
        .commit(&[StorageWrite::Task { value: record }], context())
        .await
        .unwrap();
    storage.close(context()).await.unwrap();
}

#[tokio::test]
async fn migrates_a_pending_version_1_task_and_runs_it_as_a_model_issued_call() {
    let setup = setup();
    let (echo, runs) = echo_tool(|_| {});
    add_tool(&setup.registry, echo, None).unwrap();
    let (_directory, path, id) = store_version1(&setup, r#"{"phase":"call"}"#).await;
    let chat = open_sqlite(&path, &setup).await;
    assert_eq!(
        chat.harness
            .get_task(id, context())
            .await
            .unwrap()
            .unwrap()
            .version,
        1
    );
    chat.harness.resume().unwrap();
    let settled = chat.harness.wait_for_task(id, context()).await.unwrap();
    assert_eq!(settled.version, 2);
    let input = plain(&settled.input);
    assert_eq!(
        (&input["kind"], &input["callId"]),
        (&json!("model"), &json!("c1"))
    );
    let outcome = plain(&settled.outcome);
    assert_eq!(
        (&outcome["status"], &outcome["result"]["kind"]),
        (&json!("completed"), &json!("model"))
    );
    assert_eq!(runs.load(Ordering::SeqCst), 1);
    let entries = all_entries(&chat.root, context()).await.unwrap();
    let result = &results(&entries)[0];
    assert_eq!(
        (result.tool_call_id.as_str(), result_text(result).as_str()),
        ("c1", "echo old")
    );
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn migrates_a_version_1_task_interrupted_after_intent_and_settles_it_interrupted() {
    let setup = setup();
    let (echo, runs) = echo_tool(|_| {});
    add_tool(&setup.registry, echo, None).unwrap();
    let intent = r#"{"phase":"execute","arguments":{"text":"old"},"replay":"unsafe"}"#;
    let (_directory, path, id) = store_version1(&setup, intent).await;
    let chat = open_sqlite(&path, &setup).await;
    chat.harness.resume().unwrap();
    let settled = chat.harness.wait_for_task(id, context()).await.unwrap();
    assert_eq!(settled.version, 2);
    let outcome = plain(&settled.outcome);
    assert_eq!(
        (&outcome["status"], &outcome["result"]["kind"]),
        (&json!("failed"), &json!("model"))
    );
    assert_eq!(runs.load(Ordering::SeqCst), 0);
    let entries = all_entries(&chat.root, context()).await.unwrap();
    let result = &results(&entries)[0];
    assert_eq!(
        (result.tool_call_id.as_str(), result.is_error),
        ("c1", true)
    );
    assert!(
        result_text(result).contains("Tool echo was interrupted"),
        "{}",
        result_text(result)
    );
    chat.harness.close(context()).await.unwrap();
}
