//! The guard that keeps the template's data types in step with the
//! exporters: one session holding every entry kind and message role,
//! exported by each producer (the legacy file, the durable storage it
//! imports into, and the daemon's live export, which adds the system prompt
//! and tools), is written to `assets/export-html/fixtures.ts` as
//! `SessionExportData` values. `make embedded-js-check` type-checks that file
//! against `session-data.d.ts`, and the template's tests render it; this
//! test fails when the committed file differs from what the exporters write
//! now. `EUKHE_UPDATE_EXPORT_FIXTURES=1` rewrites it.

use std::collections::HashMap;
use std::path::Path;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_types::pi_ai::Tool;
use eukhe_types::session::FileEntry;
use serde_json::{json, Value};

use super::session_data_from_file;
use crate::durable::{import_legacy_session, read_export_data, SessionLocation};
use crate::session::CURRENT_SESSION_VERSION;

const FIXTURES: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/assets/export-html/fixtures.ts"
);

/// A usage block with `total` tokens, `input` of them read.
fn usage(input: u64, total: u64) -> Value {
    json!({
        "input": input, "output": total - input, "cacheRead": 0, "cacheWrite": 0,
        "totalTokens": total,
        "cost": { "input": 0.001, "output": 0.002, "cacheRead": 0, "cacheWrite": 0, "total": 0.003 },
    })
}

/// An assistant message with `content`, stopping for `stop_reason`.
fn assistant(content: &Value, stop_reason: &str, timestamp: u64) -> Value {
    json!({
        "role": "assistant", "content": content, "api": "anthropic-messages",
        "provider": "anthropic", "model": "claude-sonnet-4-5", "usage": usage(1000, 1200),
        "stopReason": stop_reason, "timestamp": timestamp,
    })
}

/// A tool result for `id`.
fn tool_result(
    id: &str,
    name: &str,
    content: &Value,
    details: Option<Value>,
    is_error: bool,
) -> Value {
    let mut message = json!({
        "role": "toolResult", "toolCallId": id, "toolName": name, "content": content,
        "isError": is_error, "timestamp": 1_767_225_605_000_u64,
    });
    if let Some(details) = details {
        message["details"] = details;
    }
    message
}

/// The session's entries after its header: every `FileEntry` kind and
/// every `AgentMessage` role, the tool calls each template card renders
/// (with arguments a model got wrong too), and one branch.
fn rows() -> Vec<Value> {
    let text = |text: &str| json!({ "type": "text", "text": text });
    let image = json!({ "type": "image", "data": "iVBORw0KGgo=", "mimeType": "image/png" });
    let call = |id: &str, name: &str, arguments: Value| json!({ "type": "toolCall", "id": id, "name": name, "arguments": arguments });
    let bash = |command: &str, exit_code: Option<i64>, cancelled: bool| {
        let mut message = json!({
            "role": "bashExecution", "command": command, "output": "out\n",
            "cancelled": cancelled, "timestamp": 1_767_225_606_000_u64,
        });
        if let Some(code) = exit_code {
            message["exitCode"] = json!(code);
        }
        json!({ "type": "message", "message": message })
    };
    let message = |message: Value| json!({ "type": "message", "message": message });
    vec![
        json!({ "type": "model_change", "provider": "anthropic", "modelId": "claude-sonnet-4-5" }),
        json!({ "type": "thinking_level_change", "thinkingLevel": "high" }),
        json!({ "type": "service_tier_change", "serviceTier": "priority" }),
        json!({ "type": "service_tier_change", "serviceTier": null }),
        json!({ "type": "session_info", "name": "Fixture session" }),
        json!({ "type": "session_state", "state": { "status": "active" } }),
        json!({ "type": "git_state", "git": { "repoUrl": "https://example.com/repo.git", "commit": "abc1234", "branch": "main" } }),
        message(json!({
            "role": "user", "content": [text("Read the file, please."), image],
            "timestamp": 1_767_225_601_000_u64,
        })),
        message(json!({
            "role": "assistant",
            "content": [
                { "type": "thinking", "thinking": "Reading it first." },
                text("Reading it."),
                call("call-read", "read", json!({ "path": "/home/user/project/src/main.rs", "offset": 10, "limit": 5 })),
                call("call-write", "write", json!({ "path": "src/new.rs", "content": "fn main() {}\n" })),
                call("call-edit", "edit", json!({ "path": "src/main.rs", "edits": [] })),
                call("call-bash", "bash", json!({ "command": "cargo test" })),
                call("call-grep", "grep", json!({ "pattern": "fn main", "path": "src" })),
                call("call-find", "find", json!({ "pattern": "*.rs" })),
                call("call-ls", "ls", json!({ "path": "src", "limit": 20 })),
                call("call-custom", "my_tool", json!({ "query": "anything" })),
            ],
            "api": "anthropic-messages", "provider": "anthropic", "model": "claude-sonnet-4-5",
            "usage": usage(1000, 1200), "stopReason": "toolUse", "timestamp": 1_767_225_602_000_u64,
        })),
        message(tool_result(
            "call-read",
            "read",
            &json!([text("fn main() {}")]),
            None,
            false,
        )),
        message(tool_result(
            "call-write",
            "write",
            &json!([text("Wrote src/new.rs")]),
            None,
            false,
        )),
        message(tool_result(
            "call-edit",
            "edit",
            &json!([text("Edited src/main.rs")]),
            Some(json!({ "diff": "-1 fn old() {}\n+1 fn main() {}" })),
            false,
        )),
        message(tool_result(
            "call-bash",
            "bash",
            &json!([text("test result: ok")]),
            None,
            false,
        )),
        message(tool_result(
            "call-grep",
            "grep",
            &json!([text("src/main.rs:1:fn main() {}")]),
            None,
            false,
        )),
        message(tool_result(
            "call-find",
            "find",
            &json!([text("src/main.rs")]),
            None,
            false,
        )),
        message(tool_result(
            "call-ls",
            "ls",
            &json!([text("main.rs")]),
            None,
            false,
        )),
        message(tool_result(
            "call-custom",
            "my_tool",
            &json!([text("custom output"), image]),
            None,
            false,
        )),
        message(assistant(
            &json!([text("All read.")]),
            "stop",
            1_767_225_603_000,
        )),
        bash("ls", Some(0), false),
        bash("false", Some(1), false),
        bash("sleep 100", None, true),
        bash("kill -9 $$", None, false),
        message(json!({
            "role": "custom", "customType": "reminder", "content": "Remember the tests.",
            "display": true, "timestamp": 1_767_225_607_000_u64,
        })),
        message(json!({
            "role": "branchSummary", "summary": "Tried another approach.", "fromId": "e8",
            "timestamp": 1_767_225_608_000_u64,
        })),
        message(json!({
            "role": "compactionSummary", "summary": "Earlier work, summarized.",
            "tokensBefore": 54_321, "timestamp": 1_767_225_609_000_u64,
        })),
        json!({
            "type": "compaction", "summary": "The session so far.", "firstKeptEntryId": "e9",
            "tokensBefore": 12_345, "details": { "readFiles": ["src/main.rs"] },
            "fromHook": false, "customInstructions": "Keep the file list.", "usage": usage(100, 150),
        }),
        json!({
            "type": "branch_summary", "fromId": "e9", "summary": "The other branch.",
            "details": { "modifiedFiles": [] }, "fromHook": false, "usage": usage(50, 60),
        }),
        json!({ "type": "custom", "customType": "state", "data": { "step": 2 } }),
        json!({
            "type": "child_usage_attributed", "targetId": "e9",
            "childUsage": usage(10, 12), "aggregateUsage": usage(1010, 1212), "origin": "spawn_task",
        }),
        json!({ "type": "label", "targetId": "e8", "label": "start" }),
        json!({
            "type": "custom_message", "customType": "note", "content": "A note in **markdown**.",
            "display": true,
        }),
        json!({
            "type": "custom_message", "customType": "blocks",
            "content": [text("A note in blocks.")], "details": { "source": "hook" }, "display": true,
        }),
        json!({ "type": "custom_message", "customType": "hidden", "content": "Not shown.", "display": false }),
        message(json!({
            "role": "assistant", "content": [], "api": "anthropic-messages", "provider": "anthropic",
            "model": "claude-sonnet-4-5", "usage": usage(1000, 1000), "stopReason": "error",
            "errorMessage": "Overloaded", "timestamp": 1_767_225_611_000_u64,
        })),
        message(assistant(&json!([]), "aborted", 1_767_225_612_000)),
        message(
            json!({ "role": "user", "content": "Try again.", "timestamp": 1_767_225_610_000_u64 }),
        ),
    ]
}

/// The legacy session file: a header, then `rows()` chained by `parentId`
/// (`e1`, `e2`, …), but for a branch from `e8`: the two rows before the last
/// (an error and an aborted reply). The last row, the leaf, continues the
/// main chain.
fn write_session(path: &Path) {
    let header = json!({
        "type": "session", "version": CURRENT_SESSION_VERSION, "id": "fixture",
        "timestamp": "2026-01-01T00:00:00.000Z", "cwd": "/home/user/project",
        "parentSession": "parent", "rlmDepth": 1,
        "git": { "repoUrl": "https://example.com/repo.git", "commit": "abc1234", "branch": "main" },
    });
    let rows = rows();
    let last = rows.len();
    let mut lines = vec![header.to_string()];
    for (index, mut row) in rows.into_iter().enumerate() {
        let number = index + 1;
        let parent = match number {
            1 => Value::Null,
            n if n == last - 2 => json!("e8"),
            n if n == last => json!(format!("e{}", last - 3)),
            n => json!(format!("e{}", n - 1)),
        };
        let fields = row.as_object_mut().expect("row object");
        let kind = fields.shift_remove("type").expect("row type");
        let mut line = serde_json::Map::new();
        line.insert("type".to_owned(), kind);
        line.insert("id".to_owned(), json!(format!("e{number}")));
        line.insert("parentId".to_owned(), parent);
        line.insert(
            "timestamp".to_owned(),
            json!(format!("2026-01-01T00:00:{number:02}.000Z")),
        );
        line.extend(std::mem::take(fields));
        let line = Value::Object(line);
        let entry: FileEntry = serde_json::from_value(line.clone()).expect("file entry");
        assert!(
            !matches!(entry, FileEntry::Unknown { .. }),
            "the fixture row is not a valid entry: {line}"
        );
        lines.push(line.to_string());
    }
    std::fs::write(path, lines.join("\n") + "\n").expect("write the fixture session");
}

/// `data` with the durable entry ids (random) renamed `d1`, `d2`, … in
/// entry order wherever they appear, and the export time fixed.
fn stable(mut data: Value) -> Value {
    fn rename(value: &mut Value, ids: &HashMap<String, String>) {
        match value {
            Value::Object(map) => map.values_mut().for_each(|value| rename(value, ids)),
            Value::Array(items) => items.iter_mut().for_each(|item| rename(item, ids)),
            Value::String(text) => {
                if let Some(id) = ids.get(text.as_str()) {
                    id.clone_into(text);
                }
            }
            _ => {}
        }
    }
    let ids: HashMap<String, String> = data["entries"]
        .as_array()
        .expect("entries")
        .iter()
        .enumerate()
        .map(|(index, entry)| {
            let id = entry["id"].as_str().expect("entry id").to_owned();
            (id, format!("d{}", index + 1))
        })
        .collect();
    rename(&mut data, &ids);
    data["header"]["timestamp"] = json!("2026-01-01T00:00:00.000Z");
    data
}

/// The `tools` the daemon's live export writes (`name`, `description`,
/// `parameters` of each current tool).
fn live_tools() -> Vec<Value> {
    let tools: Vec<Tool> = serde_json::from_value(json!([
        {
            "name": "read", "description": "Read a file.",
            "parameters": {
                "type": "object",
                "properties": {
                    "path": { "type": "string", "description": "The file." },
                    "offset": { "type": "integer", "description": "First line." },
                },
                "required": ["path"],
            },
        },
        { "name": "my_tool", "description": "A tool without parameters.", "parameters": { "type": "object" } },
    ]))
    .expect("tools");
    tools
        .iter()
        .map(|tool| json!({ "name": tool.name, "description": tool.description, "parameters": tool.parameters }))
        .collect()
}

fn typescript(name: &str, data: &Value) -> String {
    let json = serde_json::to_string_pretty(data).expect("serialize");
    format!("export const {name}: SessionExportData = {json};\n")
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn export_fixtures_are_current() {
    let dir = tempfile::tempdir().expect("tempdir");
    let session = dir.path().join("fixture.jsonl");
    write_session(&session);

    let legacy = serde_json::to_value(session_data_from_file(&session).expect("legacy export"))
        .expect("serialize");

    let storage = dir.path().join("fixture");
    import_legacy_session(&session, &storage, &BACKGROUND_CONTEXT)
        .await
        .expect("import");
    let durable = read_export_data(&SessionLocation::from_path(storage), &BACKGROUND_CONTEXT)
        .await
        .expect("durable export")
        .expect("a durable storage");
    let durable = stable(serde_json::to_value(&durable).expect("serialize"));
    let mut live = durable.clone();
    live["systemPrompt"] = json!("You are a coding agent.");
    live["tools"] = json!(live_tools());

    let generated = [
        "// Generated by the eukhe-core test export_html::fixtures from what the exporters write: do",
        "// not edit (EUKHE_UPDATE_EXPORT_FIXTURES=1 rewrites it). One session with every entry kind",
        "// and message role, as each producer exports it; make embedded-js-check type-checks it",
        "// against session-data.d.ts, and the template's tests render it.",
        "",
        &typescript("legacy", &legacy),
        &typescript("durable", &durable),
        &typescript("live", &live),
    ]
    .join("\n");
    if std::env::var_os("EUKHE_UPDATE_EXPORT_FIXTURES").is_some() {
        std::fs::write(FIXTURES, &generated).expect("write fixtures.ts");
        return;
    }
    let committed = std::fs::read_to_string(FIXTURES).unwrap_or_default();
    assert!(
        committed == generated,
        "assets/export-html/fixtures.ts is stale: the exporters write other data now. Rerun this \
         test with EUKHE_UPDATE_EXPORT_FIXTURES=1, then make embedded-js-check (the template's \
         types must still accept it)"
    );
}
