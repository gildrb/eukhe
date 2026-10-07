use serde_json::{json, Value};

use super::*;

fn record(kind: &str, model: Option<Value>, data: Option<Value>) -> EntryRecord {
    let mut entry = json!({ "kind": kind, "id": 1, "conversationId": 1 });
    if let Some(model) = model {
        entry["model"] = Value::Array(vec![model]);
    }
    if let Some(data) = data {
        entry["data"] = data;
    }
    serde_json::from_value(entry).unwrap()
}

fn assistant(total: u64, stop_reason: &str) -> Value {
    json!({
        "role": "assistant", "content": [{ "type": "text", "text": "hi" }],
        "api": "faux", "provider": "faux", "model": "m",
        "usage": {
            "input": total, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": total,
            "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
        },
        "stopReason": stop_reason, "timestamp": 4,
    })
}

fn compaction(summary: &str) -> EntryRecord {
    let text = format!("{SUMMARY_PREFIX}{summary}{SUMMARY_SUFFIX}");
    record(
        "pi.compaction",
        Some(
            json!({ "role": "user", "content": [{ "type": "text", "text": text }], "timestamp": 9 }),
        ),
        Some(json!({ "reason": "manual" })),
    )
}

#[test]
fn model_messages_pass_through() {
    let user = json!({ "role": "user", "content": "hello", "timestamp": 2 });
    assert_eq!(
        entry_wire_message(&record("pi.user", Some(user.clone()), None)),
        Some(user)
    );
    let result = json!({
        "role": "toolResult", "toolCallId": "c1", "toolName": "bash",
        "content": [{ "type": "text", "text": "out" }], "isError": false, "timestamp": 3,
    });
    assert_eq!(
        entry_wire_message(&record("pi.tool-result", Some(result.clone()), None)),
        Some(result)
    );
    let answer = assistant(5, "stop");
    assert_eq!(
        entry_wire_message(&record("pi.assistant", Some(answer.clone()), None)),
        Some(answer)
    );
}

#[test]
fn assistant_stop_reasons_the_tui_does_not_know_show_as_stop() {
    let mut message: AssistantMessage = serde_json::from_value(assistant(1, "deferred")).unwrap();
    assert_eq!(assistant_wire_message(&message)["stopReason"], "stop");
    message.raw_stop_reason = Some("content_filter".to_owned());
    let wire = assistant_wire_message(&message);
    assert_eq!(wire["rawStopReason"], "content_filter");
    assert_eq!(wire["stopReasonRaw"], "content_filter");
}

#[test]
fn eukhe_rows_rebuild_their_roles() {
    let bash = record(
        "eukhe.bash",
        Some(json!({ "role": "user", "content": "Ran `ls`", "timestamp": 6 })),
        Some(
            json!({ "command": "ls", "output": "a", "exitCode": 0, "cancelled": false,
                     "truncated": false }),
        ),
    );
    assert_eq!(
        entry_wire_message(&bash),
        Some(json!({
            "role": "bashExecution", "command": "ls", "output": "a", "exitCode": 0,
            "cancelled": false, "truncated": false, "timestamp": 6,
        }))
    );
    let excluded = record(
        "eukhe.bash",
        None,
        Some(
            json!({ "command": "ls", "output": "", "cancelled": true, "truncated": true,
                     "fullOutputPath": "/tmp/o", "excludeFromContext": true }),
        ),
    );
    assert_eq!(
        entry_wire_message(&excluded),
        Some(json!({
            "role": "bashExecution", "command": "ls", "output": "", "cancelled": true,
            "truncated": true, "fullOutputPath": "/tmp/o", "excludeFromContext": true,
            "timestamp": 0,
        }))
    );
    let branch = record(
        "eukhe.branch-summary",
        None,
        Some(json!({ "summary": "left", "fromId": "e9", "timestamp": 12 })),
    );
    assert_eq!(
        entry_wire_message(&branch),
        Some(
            json!({ "role": "branchSummary", "summary": "left", "fromId": "e9", "timestamp": 12 })
        )
    );
    let custom = record(
        "eukhe.custom",
        None,
        Some(json!({ "customType": "refinement_notice", "display": false })),
    );
    assert_eq!(
        entry_wire_message(&custom),
        Some(json!({
            "role": "custom", "customType": "refinement_notice", "content": "",
            "display": false, "timestamp": 0,
        }))
    );
}

#[test]
fn hidden_kinds_map_to_nothing() {
    let system = json!({ "role": "system", "content": "", "timestamp": 1 });
    for entry in [
        record("pi.system", Some(system), None),
        record("pi.reset", None, None),
        record(
            "eukhe.custom-state",
            None,
            Some(json!({ "customType": "x" })),
        ),
        record("app.docs", None, Some(json!({}))),
    ] {
        assert_eq!(entry_wire_message(&entry), None, "{}", entry.kind);
    }
}

#[test]
fn compaction_summaries_show_the_bare_summary() {
    let entry = compaction("SUMMARY");
    assert_eq!(compaction_summary_text(&entry), "SUMMARY");
    assert_eq!(
        entry_wire_message(&entry),
        Some(json!({
            "role": "compactionSummary", "summary": "SUMMARY", "tokensBefore": 0, "timestamp": 9,
        }))
    );
    let imported = record(
        "eukhe.compaction-summary",
        None,
        Some(json!({ "summary": "old", "tokensBefore": 40, "timestamp": 3 })),
    );
    assert_eq!(
        entry_wire_message(&imported),
        Some(
            json!({ "role": "compactionSummary", "summary": "old", "tokensBefore": 40, "timestamp": 3 })
        )
    );
}

#[test]
fn transcript_messages_map_shown_entries_in_order() {
    let user = json!({ "role": "user", "content": "hello", "timestamp": 2 });
    let entries = [
        record("pi.user", Some(user.clone()), None),
        record("pi.reset", None, None),
        record("pi.assistant", Some(assistant(700, "stop")), None),
        compaction("S"),
    ];
    let messages = transcript_messages(&entries);
    assert_eq!(messages.len(), 3);
    assert_eq!(messages[0], user);
    assert_eq!(messages[1]["role"], "assistant");
    assert_eq!(
        messages[2],
        json!({ "role": "compactionSummary", "summary": "S", "tokensBefore": 700, "timestamp": 9 })
    );
}
