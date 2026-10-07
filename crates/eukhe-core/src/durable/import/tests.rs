//! Legacy session import: fixtures with branches, compactions, custom rows,
//! and tool results; the reopened Harness's model context must equal the
//! old engine's active context.

use std::path::{Path, PathBuf};
use std::sync::Arc;

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_chord::json::to_json;
use eukhe_durable::entries::{CompactionData, COMPACTION_ENTRY, TOOL_RESULT_ENTRY};
use eukhe_durable::harness::types::{CompactionReason, ModelRef};
use eukhe_durable::harness::{Conversation, ConversationEntryQuery, Harness};
use eukhe_durable::storage::jsonl::{open_native_jsonl_storage, JsonlStorageOptions};
use eukhe_durable::types::{EntryRecord, ROOT_CONVERSATION_ID};
use eukhe_types::pi_ai::{Message, ModelThinkingLevel};
use eukhe_types::session::FileEntry;
use serde_json::{json, Value};

use super::plan::{plan_import, PlannedHead};
use super::{harness_options, import_legacy_session, ImportError, ImportReport};
use crate::durable::goals::goal_state;
use crate::session::tree::SessionTree;
use crate::session::{build_session_context, migrate_to_current_version, parse_session_entries};
use crate::session_engine::headless::HARNESS_DIGEST_CUSTOM_TYPE;
use crate::session_engine::messages::{convert_to_llm, COMPACTION_OUTCOME_CUSTOM_TYPE};
use eukhe_types::goal::GoalStatus;

fn cx() -> Context {
    BACKGROUND_CONTEXT.clone()
}

const SESSION_ID: &str = "0190f0a2-0000-7000-8000-000000000001";

fn header() -> Value {
    json!({"type": "session", "version": 3, "id": SESSION_ID,
        "timestamp": "2024-01-01T00:00:00.000Z", "cwd": "/work"})
}

fn ts(second: u32) -> String {
    format!("2024-01-01T00:00:{second:02}.000Z")
}

fn base(row: Value, id: &str, parent: Option<&str>, second: u32) -> Value {
    let mut row = row;
    row["id"] = json!(id);
    row["parentId"] = json!(parent);
    row["timestamp"] = json!(ts(second));
    row
}

fn user(id: &str, parent: Option<&str>, text: &str, second: u32) -> Value {
    base(
        json!({"type": "message", "message": {"role": "user",
            "content": [{"type": "text", "text": text}], "timestamp": u64::from(second) * 1000}}),
        id,
        parent,
        second,
    )
}

fn assistant_message(content: &Value, stop_reason: &str, second: u32) -> Value {
    json!({"role": "assistant", "content": content, "api": "anthropic-messages",
        "provider": "anthropic", "model": "claude-x",
        "usage": {"input": 10, "output": 2, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 12,
            "cost": {"input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0}},
        "stopReason": stop_reason, "timestamp": u64::from(second) * 1000})
}

fn assistant(id: &str, parent: Option<&str>, text: &str, second: u32) -> Value {
    base(
        json!({"type": "message",
            "message": assistant_message(&json!([{"type": "text", "text": text}]), "stop", second)}),
        id,
        parent,
        second,
    )
}

fn tool_call(id: &str, parent: Option<&str>, call_id: &str, second: u32) -> Value {
    base(
        json!({"type": "message", "message": assistant_message(
            &json!([{"type": "toolCall", "id": call_id, "name": "ipython",
                "arguments": {"code": "1 + 1"}}]),
            "toolUse",
            second,
        )}),
        id,
        parent,
        second,
    )
}

fn tool_result(id: &str, parent: Option<&str>, call_id: &str, second: u32) -> Value {
    base(
        json!({"type": "message", "message": {"role": "toolResult", "toolCallId": call_id,
            "toolName": "ipython", "content": [{"type": "text", "text": "2"}],
            "details": {"cell": 1}, "isError": false, "timestamp": u64::from(second) * 1000}}),
        id,
        parent,
        second,
    )
}

fn row(kind: &str, id: &str, parent: Option<&str>, second: u32, fields: Value) -> Value {
    let mut value = fields;
    value["type"] = json!(kind);
    base(value, id, parent, second)
}

fn custom_message(id: &str, parent: &str, custom_type: &str, text: &str, second: u32) -> Value {
    row(
        "custom_message",
        id,
        Some(parent),
        second,
        json!({"customType": custom_type, "content": text, "display": true,
            "details": {"source": id}}),
    )
}

fn jsonl(rows: &[Value]) -> String {
    let mut out = String::new();
    for row in rows {
        out.push_str(&row.to_string());
        out.push('\n');
    }
    out
}

/// The old engine's model context for `content`: the default leaf's
/// session context through `convert_to_llm`, in pi-ai shapes.
fn old_context(content: &str) -> Vec<Message> {
    let mut entries = parse_session_entries(content);
    migrate_to_current_version(&mut entries);
    let leaf = SessionTree::build(&entries).default_leaf(&entries);
    let session_context = build_session_context(&entries, leaf.as_deref());
    convert_to_llm(&session_context.messages)
        .iter()
        .map(|message| serde_json::from_value(serde_json::to_value(message).unwrap()).unwrap())
        .collect()
}

struct Imported {
    _dir: tempfile::TempDir,
    legacy: PathBuf,
    storage: PathBuf,
    report: ImportReport,
}

async fn import(content: &str) -> Imported {
    let dir = tempfile::tempdir().unwrap();
    let legacy = dir.path().join(format!("{SESSION_ID}.jsonl"));
    std::fs::write(&legacy, content).unwrap();
    let storage = dir.path().join(SESSION_ID);
    let report = import_legacy_session(&legacy, &storage, &cx())
        .await
        .unwrap();
    assert_eq!(std::fs::read_to_string(&legacy).unwrap(), content);
    assert_only_storage_and_legacy(dir.path());
    Imported {
        _dir: dir,
        legacy,
        storage,
        report,
    }
}

/// No staging directory survives an import.
fn assert_only_storage_and_legacy(dir: &Path) {
    let mut names: Vec<String> = std::fs::read_dir(dir)
        .unwrap()
        .map(|entry| entry.unwrap().file_name().to_string_lossy().into_owned())
        .filter(|name| name.starts_with('.'))
        .collect();
    names.sort();
    assert_eq!(names, Vec::<String>::new());
}

async fn reopen(storage: &Path) -> (Harness, Conversation) {
    let storage = open_native_jsonl_storage(
        storage.to_str().unwrap(),
        &cx(),
        JsonlStorageOptions { fsync: true },
    )
    .await
    .unwrap();
    let harness = Harness::open(Arc::new(storage), harness_options(), &cx())
        .await
        .unwrap();
    let root = harness
        .conversation(ROOT_CONVERSATION_ID, &cx())
        .await
        .unwrap()
        .expect("root conversation imported");
    (harness, root)
}

/// Every entry of the conversation, oldest first.
async fn all_entries(root: &Conversation) -> Vec<EntryRecord> {
    let mut entries = root
        .entries(ConversationEntryQuery::default(), 10_000, None, &cx())
        .await
        .unwrap()
        .items;
    entries.reverse();
    entries
}

fn kinds(entries: &[EntryRecord]) -> Vec<&str> {
    entries.iter().map(|entry| entry.kind.as_str()).collect()
}

async fn assert_context_matches(content: &str, imported: &Imported) -> (Harness, Conversation) {
    let (harness, root) = reopen(&imported.storage).await;
    let view = root.context(&cx()).await.unwrap();
    assert_eq!(view.messages, old_context(content));
    (harness, root)
}

fn branching_session() -> String {
    jsonl(&[
        header(),
        row(
            "model_change",
            "m1",
            None,
            1,
            json!({"provider": "anthropic", "modelId": "claude-x"}),
        ),
        row(
            "thinking_level_change",
            "t1",
            Some("m1"),
            2,
            json!({"thinkingLevel": "high"}),
        ),
        user("u1", Some("t1"), "hello", 3),
        tool_call("a1", Some("u1"), "call-1", 4),
        tool_result("r1", Some("a1"), "call-1", 5),
        assistant("a2", Some("r1"), "two", 6),
        // An abandoned branch.
        user("u2", Some("a2"), "branch A", 7),
        assistant("a3", Some("u2"), "answer A", 8),
        // The active branch: the file's last row is its leaf.
        user("u3", Some("a2"), "branch B", 9),
        row(
            "label",
            "l1",
            Some("u3"),
            10,
            json!({"targetId": "u3", "label": "b"}),
        ),
        row(
            "model_change",
            "m2",
            Some("l1"),
            11,
            json!({"provider": "openai", "modelId": "gpt-x"}),
        ),
        assistant("a4", Some("m2"), "answer B", 12),
    ])
}

#[tokio::test(flavor = "multi_thread")]
async fn imports_the_active_branch_with_tool_results_and_agent_state() {
    let content = branching_session();
    let imported = import(&content).await;
    assert_eq!(
        imported.report,
        ImportReport {
            session_id: SESSION_ID.to_owned(),
            cwd: "/work".to_owned(),
            model: Some(ModelRef {
                provider: "openai".to_owned(),
                model_id: "gpt-x".to_owned(),
            }),
            thinking_level: Some(ModelThinkingLevel::High),
            leaf_id: Some("a4".to_owned()),
            entries: 6,
            skipped_rows: 1,
        }
    );
    let (harness, root) = assert_context_matches(&content, &imported).await;
    let entries = all_entries(&root).await;
    assert_eq!(
        kinds(&entries),
        [
            "pi.user",
            "pi.assistant",
            "pi.tool-result",
            "pi.assistant",
            "pi.user",
            "pi.assistant"
        ]
    );
    let result = TOOL_RESULT_ENTRY
        .narrow(entries[2].clone())
        .unwrap()
        .unwrap();
    assert_eq!(
        to_json(result.data()).unwrap(),
        to_json(&json!({"diagnostics": []})).unwrap()
    );
    let agent = root.agent(&cx()).await.unwrap();
    assert_eq!(agent.model, imported.report.model);
    assert_eq!(agent.thinking_level, ModelThinkingLevel::High);
    assert_eq!(agent.cwd.as_deref(), Some("/work"));
    harness.close(&cx()).await.unwrap();
    assert!(imported.legacy.exists());
}

/// A tool result row without `toolName` (foreign tool, older build).
fn nameless_tool_result(id: &str, parent: &str, call_id: &str, second: u32) -> Value {
    let mut row = tool_result(id, Some(parent), call_id, second);
    row["message"].as_object_mut().unwrap().remove("toolName");
    row
}

#[tokio::test(flavor = "multi_thread")]
async fn a_tool_result_without_a_tool_name_takes_its_calls_name() {
    let content = jsonl(&[
        header(),
        user("u1", None, "hi", 1),
        tool_call("a1", Some("u1"), "call-1", 2),
        nameless_tool_result("r1", "a1", "call-1", 3),
        // No assistant call answers this one: the old engine sent "".
        nameless_tool_result("r2", "r1", "call-orphan", 4),
        assistant("a2", Some("r2"), "done", 5),
    ]);
    let imported = import(&content).await;
    assert_eq!(imported.report.entries, 5);
    let (harness, root) = reopen(&imported.storage).await;
    // The stored entries carry what the old engine sent for each row (the
    // context view leaves the orphan result out).
    let names: Vec<String> = all_entries(&root)
        .await
        .into_iter()
        .filter_map(|entry| match entry.model?.into_iter().next()? {
            Message::ToolResult(result) => Some(result.tool_name),
            _ => None,
        })
        .collect();
    assert_eq!(names, ["ipython", ""]);
    harness.close(&cx()).await.unwrap();
}

fn compacted_session() -> String {
    jsonl(&[
        header(),
        user("u1", None, "first", 1),
        assistant("a1", Some("u1"), "one", 2),
        user("u2", Some("a1"), "second", 3),
        tool_call("a2", Some("u2"), "call-1", 4),
        tool_result("r2", Some("a2"), "call-1", 5),
        assistant("a3", Some("r2"), "three", 6),
        row(
            "compaction",
            "c1",
            Some("a3"),
            7,
            json!({"summary": "the story so far", "firstKeptEntryId": "u2", "tokensBefore": 1234}),
        ),
        user("u3", Some("c1"), "third", 8),
        assistant("a4", Some("u3"), "four", 9),
    ])
}

#[tokio::test(flavor = "multi_thread")]
async fn imports_a_compaction_as_a_head_at_the_first_kept_entry() {
    let content = compacted_session();
    let imported = import(&content).await;
    let (harness, root) = assert_context_matches(&content, &imported).await;
    let entries = all_entries(&root).await;
    assert_eq!(
        kinds(&entries),
        [
            "pi.user",
            "pi.assistant",
            "pi.user",
            "pi.assistant",
            "pi.tool-result",
            "pi.assistant",
            "pi.compaction",
            "pi.user",
            "pi.assistant",
        ]
    );
    let compaction = COMPACTION_ENTRY
        .narrow(entries[6].clone())
        .unwrap()
        .unwrap();
    assert_eq!(compaction.head, Some(entries[2].id));
    assert_eq!(
        *compaction.data(),
        CompactionData {
            reason: CompactionReason::Threshold
        }
    );
    let view = root.context(&cx()).await.unwrap();
    assert_eq!(view.head.map(|head| head.id), Some(entries[6].id));
    assert_eq!(view.messages.len(), 7);
    harness.close(&cx()).await.unwrap();
}

#[test]
fn compaction_head_starts_at_the_first_imported_entry_from_first_kept() {
    let content = jsonl(&[
        header(),
        user("u1", None, "first", 1),
        row(
            "label",
            "l1",
            Some("u1"),
            2,
            json!({"targetId": "u1", "label": "x"}),
        ),
        assistant("a1", Some("l1"), "one", 3),
        row(
            "compaction",
            "c1",
            Some("a1"),
            4,
            json!({"summary": "s1", "firstKeptEntryId": "l1", "tokensBefore": 1,
                "customInstructions": "focus"}),
        ),
        user("u2", Some("c1"), "second", 5),
        row(
            "compaction",
            "c2",
            Some("u2"),
            6,
            json!({"summary": "s2", "firstKeptEntryId": "gone", "tokensBefore": 2}),
        ),
    ]);
    let plan = plan_import(&content).unwrap();
    let heads: Vec<PlannedHead> = plan.entries.iter().map(|entry| entry.head).collect();
    // u1, a1, c1 (from the label: a1), u2, c2 (first kept missing: itself).
    assert_eq!(
        heads,
        [
            PlannedHead::None,
            PlannedHead::None,
            PlannedHead::Planned(1),
            PlannedHead::None,
            PlannedHead::SelfEntry,
        ]
    );
    assert_eq!(
        plan.entries[2].draft.data,
        Some(
            to_json(&CompactionData {
                reason: CompactionReason::Manual
            })
            .unwrap()
        )
    );
}

#[tokio::test(flavor = "multi_thread")]
async fn imports_a_compaction_whose_first_kept_entry_is_missing() {
    let content = jsonl(&[
        header(),
        user("u1", None, "first", 1),
        assistant("a1", Some("u1"), "one", 2),
        row(
            "compaction",
            "c1",
            Some("a1"),
            3,
            json!({"summary": "everything", "firstKeptEntryId": "gone", "tokensBefore": 9}),
        ),
        user("u2", Some("c1"), "second", 4),
    ]);
    let imported = import(&content).await;
    let (harness, _root) = assert_context_matches(&content, &imported).await;
    harness.close(&cx()).await.unwrap();
}

fn goal_row() -> Value {
    json!({"active": false, "status": "paused", "objective": "ship", "tokensUsed": 5,
        "timeUsedSeconds": 1, "continuationsUsed": 0})
}

fn custom_rows_session() -> String {
    jsonl(&[
        header(),
        user("u1", None, "hi", 1),
        custom_message("d1", "u1", HARNESS_DIGEST_CUSTOM_TYPE, "digest one", 2),
        assistant("a1", Some("d1"), "one", 3),
        custom_message(
            "n1",
            "a1",
            "agent_message",
            "[agent-message from x] hello",
            4,
        ),
        custom_message(
            "o1",
            "n1",
            COMPACTION_OUTCOME_CUSTOM_TYPE,
            "compaction failed",
            5,
        ),
        base(
            json!({"type": "message", "message": {"role": "bashExecution", "command": "ls",
                "output": "a\nb", "exitCode": 0, "cancelled": false, "truncated": false,
                "timestamp": 6000}}),
            "b1",
            Some("o1"),
            6,
        ),
        base(
            json!({"type": "message", "message": {"role": "bashExecution", "command": "secret",
                "output": "", "exitCode": 0, "cancelled": false, "truncated": false,
                "timestamp": 7000, "excludeFromContext": true}}),
            "b2",
            Some("b1"),
            7,
        ),
        base(
            json!({"type": "message", "message": {"role": "custom", "customType": "heartbeat_prompt",
                "content": [{"type": "text", "text": "[heartbeat: 1m] tick"}], "display": true,
                "timestamp": 8000}}),
            "h1",
            Some("b2"),
            8,
        ),
        row(
            "branch_summary",
            "s1",
            Some("h1"),
            9,
            json!({"fromId": "zz", "summary": "explored a dead end"}),
        ),
        row(
            "custom",
            "g1",
            Some("s1"),
            10,
            json!({"customType": "thread_goal_state", "data": goal_row()}),
        ),
        custom_message("d2", "g1", HARNESS_DIGEST_CUSTOM_TYPE, "digest two", 11),
        user("u2", Some("d2"), "next", 12),
        assistant("a2", Some("u2"), "two", 13),
    ])
}

#[tokio::test(flavor = "multi_thread")]
async fn imports_custom_rows_bash_runs_and_branch_summaries() {
    let content = custom_rows_session();
    let imported = import(&content).await;
    assert_eq!(imported.report.entries, 13);
    assert_eq!(imported.report.skipped_rows, 0);
    let (harness, root) = assert_context_matches(&content, &imported).await;
    let entries = all_entries(&root).await;
    assert_eq!(
        kinds(&entries),
        [
            "pi.user",
            "eukhe.custom",
            "pi.assistant",
            "eukhe.custom",
            "eukhe.custom",
            "eukhe.bash",
            "eukhe.bash",
            "eukhe.custom",
            "eukhe.branch-summary",
            "eukhe.custom-state",
            "eukhe.custom",
            "pi.user",
            "pi.assistant",
        ]
    );
    let has_model: Vec<bool> = entries.iter().map(|entry| entry.model.is_some()).collect();
    assert_eq!(
        has_model,
        // The older digest, the display-only outcome, the excluded bash
        // run, and the state row never reach the model.
        [true, false, true, true, false, true, false, true, true, false, true, true, true]
    );
    let data: Vec<Option<Value>> = entries
        .iter()
        .map(|entry| entry.data.as_ref().map(serde_json::Value::from))
        .collect();
    assert_eq!(
        data[3],
        Some(json!({"customType": "agent_message", "display": true,
            "details": {"source": "n1"}}))
    );
    // Display-only rows and dropped digests keep their content in data.
    assert_eq!(
        data[4],
        Some(json!({"customType": COMPACTION_OUTCOME_CUSTOM_TYPE,
            "content": "compaction failed", "display": true, "details": {"source": "o1"}}))
    );
    assert_eq!(
        data[1],
        Some(json!({"customType": HARNESS_DIGEST_CUSTOM_TYPE,
            "content": "digest one", "display": true, "details": {"source": "d1"}}))
    );
    assert_eq!(
        data[5],
        Some(
            json!({"command": "ls", "output": "a\nb", "exitCode": 0, "cancelled": false,
            "truncated": false})
        )
    );
    assert_eq!(
        data[8],
        Some(json!({"summary": "explored a dead end", "fromId": "zz",
            "timestamp": 1_704_067_209_000_u64}))
    );
    assert_eq!(
        data[9],
        Some(json!({"customType": "thread_goal_state", "data": goal_row()}))
    );
    let goal = goal_state(&harness, root.id(), &cx()).await.unwrap();
    assert_eq!(goal.objective.as_deref(), Some("ship"));
    assert_eq!(goal.status, GoalStatus::Paused);
    harness.close(&cx()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread")]
async fn a_compaction_snapshot_outranks_older_digests() {
    let content = jsonl(&[
        header(),
        user("u1", None, "hi", 1),
        custom_message("d1", "u1", HARNESS_DIGEST_CUSTOM_TYPE, "digest one", 2),
        assistant("a1", Some("d1"), "one", 3),
        row(
            "compaction",
            "c1",
            Some("a1"),
            4,
            json!({"summary": "s", "firstKeptEntryId": "u1", "tokensBefore": 5,
                "harnessDigest": "snapshot", "harnessStateFingerprint": "fp"}),
        ),
        user("u2", Some("c1"), "next", 5),
    ]);
    let imported = import(&content).await;
    let (harness, _root) = assert_context_matches(&content, &imported).await;
    harness.close(&cx()).await.unwrap();

    // A digest after the compaction takes the summary's snapshot's place.
    let content = jsonl(&[
        header(),
        user("u1", None, "hi", 1),
        assistant("a1", Some("u1"), "one", 2),
        row(
            "compaction",
            "c1",
            Some("a1"),
            3,
            json!({"summary": "s", "firstKeptEntryId": "a1", "tokensBefore": 5,
                "harnessDigest": "snapshot"}),
        ),
        custom_message("d2", "c1", HARNESS_DIGEST_CUSTOM_TYPE, "digest two", 4),
        user("u2", Some("d2"), "next", 5),
    ]);
    let imported = import(&content).await;
    let (harness, _root) = assert_context_matches(&content, &imported).await;
    harness.close(&cx()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread")]
async fn imports_a_header_only_session_as_an_empty_root() {
    let content = jsonl(&[header()]);
    let imported = import(&content).await;
    assert_eq!(imported.report.entries, 0);
    assert_eq!(imported.report.leaf_id, None);
    let (harness, root) = reopen(&imported.storage).await;
    assert_eq!(all_entries(&root).await.len(), 0);
    assert_eq!(
        root.agent(&cx()).await.unwrap().cwd.as_deref(),
        Some("/work")
    );
    harness.close(&cx()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread")]
async fn an_existing_storage_is_never_overwritten() {
    let dir = tempfile::tempdir().unwrap();
    let legacy = dir.path().join("legacy.jsonl");
    std::fs::write(&legacy, branching_session()).unwrap();
    let storage = dir.path().join("existing");
    std::fs::create_dir(&storage).unwrap();
    std::fs::write(storage.join("keep"), "x").unwrap();
    let error = import_legacy_session(&legacy, &storage, &cx())
        .await
        .unwrap_err();
    assert!(matches!(error, ImportError::AlreadyExists { path } if path == storage));
    assert_eq!(std::fs::read_to_string(storage.join("keep")).unwrap(), "x");
    assert_only_storage_and_legacy(dir.path());
}

#[tokio::test(flavor = "multi_thread")]
async fn a_failed_import_leaves_nothing_behind() {
    let dir = tempfile::tempdir().unwrap();
    let legacy = dir.path().join("legacy.jsonl");
    let content = jsonl(&[
        header(),
        row(
            "thinking_level_change",
            "t1",
            None,
            1,
            json!({"thinkingLevel": "extreme"}),
        ),
    ]);
    std::fs::write(&legacy, &content).unwrap();
    let storage = dir.path().join("new");
    let error = import_legacy_session(&legacy, &storage, &cx())
        .await
        .unwrap_err();
    assert!(matches!(error, ImportError::ThinkingLevel { level } if level == "extreme"));
    assert!(!storage.exists());
    assert_only_storage_and_legacy(dir.path());

    let headless = jsonl(&[user("u1", None, "hi", 1)]);
    std::fs::write(&legacy, &headless).unwrap();
    let error = import_legacy_session(&legacy, &storage, &cx())
        .await
        .unwrap_err();
    assert!(matches!(error, ImportError::MissingHeader));
    assert!(!storage.exists());
    assert_eq!(std::fs::read_to_string(&legacy).unwrap(), headless);
}

#[test]
fn a_parent_cycle_ends_the_branch_walk() {
    let content = jsonl(&[
        header(),
        user("u1", Some("a1"), "hi", 1),
        assistant("a1", Some("u1"), "one", 2),
    ]);
    let plan = plan_import(&content).unwrap();
    assert_eq!(plan.entries.len(), 2);
    assert!(matches!(
        plan.branch.first(),
        Some(FileEntry::Message { .. })
    ));
}
