use serde_json::{json, Value};

use super::*;

/// The wrapper the durable compaction puts around a summary in the entry's
/// model message (`harness/compaction/prompt.rs`, crate-private there).
const SUMMARY_PREFIX: &str =
    "The conversation history before this point was compacted into the following summary:\n\n<summary>\n";
const SUMMARY_SUFFIX: &str = "\n</summary>";

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
        Some(json!({
            "reason": "manual",
            "summary": { "summary": summary, "readFiles": [], "modifiedFiles": [] },
        })),
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
    let wire = |message: &AssistantMessage| {
        serde_json::to_value(assistant_wire_message(message).expect("wire message")).unwrap()
    };
    assert_eq!(wire(&message)["stopReason"], "stop");
    message.raw_stop_reason = Some("content_filter".to_owned());
    let wire = wire(&message);
    assert_eq!(wire["rawStopReason"], "content_filter");
    assert_eq!(wire["stopReasonRaw"], "content_filter");
}

#[test]
fn eukhe_rows_rebuild_their_roles() {
    let bash = record(
        "eukhe.bash",
        Some(json!({ "role": "user", "content": "Ran `ls`", "timestamp": 6 })),
        Some(json!({ "command": "ls", "output": "a", "exitCode": 0, "cancelled": false })),
    );
    assert_eq!(
        entry_wire_message(&bash),
        Some(json!({
            "role": "bashExecution", "command": "ls", "output": "a", "exitCode": 0,
            "cancelled": false, "timestamp": 6,
        }))
    );
    let excluded = record(
        "eukhe.bash",
        None,
        Some(json!({ "command": "ls", "output": "", "cancelled": true,
                     "omitted": { "bytes": 4, "lines": 1, "at": "start" },
                     "artifact": "/tmp/o", "excludeFromContext": true })),
    );
    assert_eq!(
        entry_wire_message(&excluded),
        Some(json!({
            "role": "bashExecution", "command": "ls", "output": "", "cancelled": true,
            "omitted": { "bytes": 4, "lines": 1, "at": "start" },
            "artifact": "/tmp/o", "excludeFromContext": true,
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

/// `/autoresearch <goal>`: the user's message is the goal alone and the
/// mode's instructions are a system prompt section (a `pi.system` entry the
/// model reads): the transcript every client shows (live, attach, resume,
/// `get_messages`) holds the goal and the answer, never the instructions.
#[test]
fn autoresearch_instructions_are_a_section_no_transcript_shows() {
    let goal = json!({ "role": "user", "content": "Make fib.py faster", "timestamp": 1 });
    let system = json!({
        "role": "system", "content": "", "timestamp": 2,
        "sections": {
            "autoresearch": "<autoresearch>\nAutoresearch mode is on and this branch has no experiment yet.\n</autoresearch>",
        },
    });
    let entries = [
        record("pi.user", Some(goal.clone()), None),
        record("pi.system", Some(system), None),
        record("pi.assistant", Some(assistant(9, "stop")), None),
    ];
    let messages = transcript_messages(&entries);
    assert_eq!(messages.len(), 2, "{messages:?}");
    assert_eq!(messages[0], goal);
    assert_eq!(messages[1]["role"], "assistant");
    assert!(
        !Value::Array(messages)
            .to_string()
            .contains("Autoresearch mode is on"),
        "the instructions reached a transcript"
    );
}

#[test]
fn compaction_summaries_show_the_bare_summary() {
    let entry = compaction("SUMMARY");
    assert_eq!(compaction_summary_text(&entry).unwrap(), "SUMMARY");
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

#[test]
fn an_input_row_shows_in_place_of_its_user_entry() {
    let entries = [
        record(
            "eukhe.custom",
            None,
            Some(json!({
                "customType": "sideQuestion", "content": "hello", "display": true,
                "input": true,
            })),
        ),
        record(
            "pi.user",
            Some(json!({ "role": "user", "content": "hello", "timestamp": 2 })),
            None,
        ),
        record("pi.assistant", Some(assistant(1, "stop")), None),
    ];
    let messages = transcript_messages(&entries);
    assert_eq!(messages.len(), 2);
    assert_eq!(messages[0]["role"], "custom");
    assert_eq!(messages[0]["content"], "hello");
    assert_eq!(messages[1]["role"], "assistant");
}

/// The engine's own inputs (autonomous, goal and Director continuations,
/// quota and compaction resumes) reach every transcript as hidden custom
/// messages carrying their origin; a person's words, a `/loop` iteration
/// and a report stay user messages.
#[test]
fn engine_inputs_show_as_hidden_custom_messages() {
    let user_entry = |text: &str, origin: Option<Value>| {
        record(
            "pi.user",
            Some(
                json!({ "role": "user", "content": [{ "type": "text", "text": text }], "timestamp": 7 }),
            ),
            origin.map(|origin| json!({ "origin": origin })),
        )
    };
    let hidden = [
        (
            json!({ "kind": "autonomous", "nudge": "continuation" }),
            "autonomous_continuation",
        ),
        (
            json!({ "kind": "autonomous", "nudge": "gateFailed" }),
            "autonomous_continuation",
        ),
        (
            json!({ "kind": "goal", "context": "continuation" }),
            "goal_prompt",
        ),
        (json!({ "kind": "director" }), "director_continuation"),
        (json!({ "kind": "quotaResume" }), "quota_resume"),
        (json!({ "kind": "compactionResume" }), "compaction_resume"),
    ];
    for (origin, custom_type) in hidden {
        let entry = user_entry(
            "[autonomous-continuation]\n\nkeep going",
            Some(origin.clone()),
        );
        assert_eq!(
            entry_wire_message(&entry),
            Some(json!({
                "role": "custom",
                "customType": custom_type,
                "content": [{ "type": "text", "text": "[autonomous-continuation]\n\nkeep going" }],
                "display": false,
                "details": { "origin": origin },
                "timestamp": 7,
            })),
        );
        // The wire type every client decodes keeps the flag.
        let shown = entry_wire_message(&entry).expect("shown");
        let wire: AgentMessage = to_wire(&shown).expect("decodes");
        let AgentMessage::Custom(custom) = wire else {
            panic!("not a custom message: {wire:?}");
        };
        assert!(!custom.display);
    }
    for origin in [
        None,
        Some(json!({ "kind": "user" })),
        Some(json!({ "kind": "loop", "iteration": 2 })),
        Some(json!({
            "kind": "report",
            "report": { "report": "heartbeat", "schedule": "5m", "run": 1 },
        })),
    ] {
        let message = entry_wire_message(&user_entry("mine", origin.clone())).expect("shown");
        assert_eq!(message["role"], "user", "{origin:?}");
    }
    // A transcript (attach, `get_messages`, a resume) shows the user's
    // prompt and the answers, and the continuation only as hidden.
    let entries = [
        user_entry("optimize the parser", None),
        record("pi.assistant", Some(assistant(1, "stop")), None),
        user_entry(
            "[autonomous-continuation]\n\nAutoresearch mode is on",
            Some(json!({ "kind": "autonomous", "nudge": "continuation" })),
        ),
        record("pi.assistant", Some(assistant(2, "stop")), None),
    ];
    let messages = transcript_messages(&entries);
    let roles: Vec<&str> = messages
        .iter()
        .map(|message| message["role"].as_str().unwrap_or_default())
        .collect();
    assert_eq!(roles, ["user", "assistant", "custom", "assistant"]);
    assert_eq!(messages[2]["display"], false);
}
