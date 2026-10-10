use eukhe_durable::harness::ToolEventCall;
use serde_json::{json, Value};

use super::*;

fn usage(total: u64) -> Value {
    json!({
        "input": total, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": total,
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
    })
}

fn assistant(content: Value, stop_reason: &str, total: u64) -> Value {
    let mut message = json!({
        "role": "assistant", "api": "faux", "provider": "faux",
        "model": "m", "usage": usage(total), "stopReason": stop_reason, "timestamp": 5,
    });
    message["content"] = content;
    message
}

fn entry(id: u64, kind: &str, model: Option<Value>, data: Option<Value>) -> Value {
    let mut entry = json!({ "kind": kind, "id": id, "conversationId": 1 });
    if let Some(model) = model {
        entry["model"] = Value::Array(vec![model]);
    }
    if let Some(data) = data {
        entry["data"] = data;
    }
    entry
}

fn snapshot(entries: Vec<Value>, extra: &Value) -> SnapshotEvent {
    let mut value = json!({
        "tools": [], "nestedTools": [], "compactions": [], "inbox": [], "agent": {},
        "usage": { "models": {}, "tools": {} },
    });
    value["entries"] = Value::Array(entries);
    for (key, field) in extra.as_object().unwrap() {
        value[key] = field.clone();
    }
    serde_json::from_value(value).unwrap()
}

fn event(value: Value) -> AgentEvent {
    serde_json::from_value(value).unwrap()
}

fn translator(mode: CoalesceMode) -> EventTranslator {
    EventTranslator::new(&snapshot(Vec::new(), &json!({})), mode)
}

fn update(changes: Value) -> AgentEvent {
    let mut value = json!({ "type": "message_update", "usage": usage(3) });
    value["changes"] = changes;
    event(value)
}

fn types(frames: &[Value]) -> Vec<&str> {
    frames
        .iter()
        .map(|frame| frame["type"].as_str().unwrap())
        .collect()
}

fn stream_kinds(frames: &[Value]) -> Vec<&str> {
    frames
        .iter()
        .map(|frame| frame["assistantMessageEvent"]["type"].as_str().unwrap())
        .collect()
}

fn start_streaming(translator: &mut EventTranslator) -> Vec<Value> {
    translator.translate(&event(json!({
        "type": "message_start",
        "message": assistant(json!([]), "pending", 0),
    })))
}

#[test]
fn streaming_builds_the_partial_from_text_thinking_and_toolcall_changes() {
    let mut translator = translator(CoalesceMode::Immediate);
    let started = translator.translate(&event(json!({ "type": "run_start", "inputs": [3] })));
    assert_eq!(started, [json!({ "type": "agent_start" })]);
    let start = start_streaming(&mut translator);
    assert_eq!(types(&start), ["message_start"]);
    assert_eq!(
        start[0]["assistantMessageEvent"],
        json!({ "type": "start" })
    );
    // The streaming partial's `pending` stop reason is shown as `stop`.
    assert_eq!(start[0]["message"]["stopReason"], "stop");

    let frames = translator.translate(&update(json!([
        { "type": "thinking_start", "contentIndex": 0, "block": { "type": "thinking", "thinking": "" } },
        { "type": "thinking_delta", "contentIndex": 0, "delta": "plan" },
        { "type": "block", "contentIndex": 0, "block": { "type": "thinking", "thinking": "plan!" } },
        { "type": "text_start", "contentIndex": 1, "block": { "type": "text", "text": "" } },
        { "type": "text_delta", "contentIndex": 1, "delta": "hi" },
        { "type": "toolcall_start", "contentIndex": 2,
          "block": { "type": "toolCall", "id": "c1", "name": "bash", "arguments": { "command": "" } } },
        { "type": "toolcall_delta", "contentIndex": 2, "path": ["command"], "delta": "ls" },
    ])));
    assert_eq!(
        stream_kinds(&frames),
        [
            "thinking_start",
            "thinking_delta",
            "thinking_end",
            "text_start",
            "text_delta",
            "toolcall_start",
            "toolcall_delta"
        ]
    );
    assert!(frames.iter().all(|frame| frame["type"] == "message_update"));
    assert_eq!(frames[1]["assistantMessageEvent"]["delta"], "plan");
    assert_eq!(frames[1]["message"]["content"][0]["thinking"], "plan");
    assert!(frames[2]["assistantMessageEvent"].get("delta").is_none());
    assert_eq!(frames[6]["assistantMessageEvent"]["delta"], "ls");
    // Each frame carries the full partial after its change.
    assert_eq!(
        frames[6]["message"]["content"],
        json!([
            { "type": "thinking", "thinking": "plan!" },
            { "type": "text", "text": "hi" },
            { "type": "toolCall", "id": "c1", "name": "bash", "arguments": { "command": "ls" } },
        ])
    );
    assert_eq!(frames[6]["message"]["usage"]["totalTokens"], 3);
    let partial = translator.mirror().partial.as_ref().unwrap();
    assert_eq!(partial.content.len(), 3);
    assert_eq!(partial.usage.total_tokens, 3);
    assert!(!translator.has_parked());
}

#[test]
fn coalescing_merges_same_kind_and_replaces_on_a_kind_switch() {
    let mut translator = translator(CoalesceMode::Coalesced);
    start_streaming(&mut translator);
    let parked = translator.translate(&update(json!([
        { "type": "text_start", "contentIndex": 0, "block": { "type": "text", "text": "" } },
    ])));
    assert!(parked.is_empty());
    assert!(translator.has_parked());
    for delta in ["a", "b"] {
        let frames = translator.translate(&update(json!([
            { "type": "text_delta", "contentIndex": 0, "delta": delta },
        ])));
        assert!(frames.is_empty());
    }
    let flushed = translator.flush().unwrap();
    assert_eq!(
        flushed["assistantMessageEvent"],
        json!({ "type": "text_delta", "delta": "ab" })
    );
    assert_eq!(flushed["message"]["content"][0]["text"], "ab");
    assert!(translator.flush().is_none());
    assert!(!translator.has_parked());

    // A kind switch replaces the parked update.
    translator.translate(&update(json!([
        { "type": "text_delta", "contentIndex": 0, "delta": "c" },
        { "type": "thinking_start", "contentIndex": 1, "block": { "type": "thinking", "thinking": "" } },
    ])));
    let flushed = translator.flush().unwrap();
    assert_eq!(
        flushed["assistantMessageEvent"],
        json!({ "type": "thinking_start" })
    );
    assert_eq!(flushed["message"]["content"][0]["text"], "abc");
}

#[test]
fn coalescing_flushes_before_block_ends_and_message_end() {
    let mut translator = translator(CoalesceMode::Coalesced);
    start_streaming(&mut translator);
    translator.translate(&update(json!([
        { "type": "thinking_start", "contentIndex": 0, "block": { "type": "thinking", "thinking": "" } },
        { "type": "thinking_delta", "contentIndex": 0, "delta": "x" },
    ])));
    let frames = translator.translate(&update(json!([
        { "type": "thinking_delta", "contentIndex": 0, "delta": "y" },
        { "type": "block", "contentIndex": 0, "block": { "type": "thinking", "thinking": "xy" } },
    ])));
    assert_eq!(stream_kinds(&frames), ["thinking_delta", "thinking_end"]);
    assert_eq!(frames[0]["assistantMessageEvent"]["delta"], "xy");
    assert!(!translator.has_parked());

    translator.translate(&update(json!([
        { "type": "text_start", "contentIndex": 1, "block": { "type": "text", "text": "" } },
        { "type": "text_delta", "contentIndex": 1, "delta": "done" },
    ])));
    assert!(translator.has_parked());
    let final_message = assistant(
        json!([{ "type": "thinking", "thinking": "xy" }, { "type": "text", "text": "done" }]),
        "stop",
        9,
    );
    let frames = translator.translate(&event(json!({
        "type": "message_end",
        "entry": entry(10, "pi.assistant", Some(final_message.clone()), None),
    })));
    assert_eq!(types(&frames), ["message_update", "message_end"]);
    assert_eq!(
        frames[0]["assistantMessageEvent"],
        json!({ "type": "text_delta", "delta": "done" })
    );
    assert_eq!(frames[1]["message"], final_message);
    assert!(translator.mirror().partial.is_none());
    assert!(translator.flush().is_none());
    assert_eq!(translator.mirror().entries.len(), 1);
}

#[test]
fn an_unstreamed_assistant_message_end_starts_its_message() {
    let mut translator = translator(CoalesceMode::Coalesced);
    let message = assistant(json!([{ "type": "text", "text": "hi" }]), "stop", 1);
    let frames = translator.translate(&event(json!({
        "type": "message_end",
        "entry": entry(10, "pi.assistant", Some(message.clone()), None),
    })));
    assert_eq!(types(&frames), ["message_start", "message_end"]);
    assert_eq!(
        frames[0]["assistantMessageEvent"],
        json!({ "type": "start" })
    );
    assert_eq!(frames[0]["message"], message);
}

#[test]
fn user_messages_go_out_from_their_message_end() {
    let mut translator = translator(CoalesceMode::Immediate);
    let user = json!({ "role": "user", "content": "hello", "timestamp": 2 });
    let start = translator.translate(&event(json!({ "type": "message_start", "message": user })));
    assert!(start.is_empty());
    let frames = translator.translate(&event(json!({
        "type": "message_end",
        "entry": entry(4, "pi.user", Some(user.clone()), None),
    })));
    assert_eq!(
        frames,
        [
            json!({ "type": "message_start", "message": user }),
            json!({ "type": "message_end", "message": user }),
        ]
    );
}

/// A run started in the commit that placed its input opens before the
/// input's frames, and its `agent_end` carries the run's messages.
#[test]
fn a_run_opens_before_its_inputs_and_ends_with_its_messages() {
    let mut translator = translator(CoalesceMode::Immediate);
    let user = json!({ "role": "user", "content": "hello", "timestamp": 2 });
    let frames = translator.translate_batch(&[
        event(json!({ "type": "message_start", "message": user })),
        event(json!({ "type": "message_end", "entry": entry(4, "pi.user", Some(user.clone()), None) })),
        event(json!({ "type": "run_start", "inputs": [4] })),
        event(json!({ "type": "turn_start" })),
    ]);
    assert_eq!(
        types(&frames),
        ["agent_start", "turn_start", "message_start", "message_end"]
    );
    let answer = assistant(json!([{ "type": "text", "text": "hi" }]), "stop", 1);
    let frames = translator.translate_batch(&[
        event(json!({ "type": "message_end", "entry": entry(5, "pi.assistant", Some(answer.clone()), None) })),
        event(json!({ "type": "turn_end" })),
        event(json!({ "type": "run_end", "inputs": [4] })),
    ]);
    let end = frames.last().unwrap();
    assert_eq!(end["type"], "agent_end");
    assert_eq!(end["messages"], json!([user, answer]));
}

/// An input row (an `eukhe.custom` row with `input: true`) shows itself in
/// the input's place: the user entry right after it emits no frames, and
/// `agent_end` carries the row as the run's prompt row.
#[test]
fn an_input_row_shows_in_place_of_its_user_entry() {
    let mut translator = translator(CoalesceMode::Immediate);
    let row = json!({
        "role": "custom", "customType": "sideQuestion", "content": "hello",
        "display": true, "timestamp": 0,
    });
    let user = json!({ "role": "user", "content": "hello", "timestamp": 2 });
    let frames = translator.translate_batch(&[
        event(json!({ "type": "entry_appended", "entry": entry(
            3, "eukhe.custom", None,
            Some(json!({ "customType": "sideQuestion", "content": "hello", "display": true, "input": true })),
        ) })),
        event(json!({ "type": "message_start", "message": user })),
        event(json!({ "type": "message_end", "entry": entry(4, "pi.user", Some(user), None) })),
    ]);
    assert_eq!(
        frames,
        [
            json!({ "type": "message_start", "message": row }),
            json!({ "type": "message_end", "message": row }),
        ]
    );
    // A later user entry (nothing before it stands for it) shows again.
    let user_two = json!({ "role": "user", "content": "again", "timestamp": 6 });
    let frames = translator.translate_batch(&[event(json!({
        "type": "message_end", "entry": entry(5, "pi.user", Some(user_two.clone()), None)
    }))]);
    assert_eq!(
        frames,
        [
            json!({ "type": "message_start", "message": user_two }),
            json!({ "type": "message_end", "message": user_two }),
        ]
    );
}

fn tool_update(translator: &mut EventTranslator, fields: &Value) -> Value {
    let mut value =
        json!({ "type": "tool_execution_update", "toolCallId": "c1", "toolName": "bash" });
    for (key, field) in fields.as_object().unwrap() {
        value[key] = field.clone();
    }
    let frames = translator.translate(&event(value));
    assert_eq!(types(&frames), ["tool_execution_update"]);
    frames.into_iter().next().unwrap()
}

fn start_tool(translator: &mut EventTranslator) {
    let frames = translator.translate(&event(json!({
        "type": "tool_execution_start", "toolCallId": "c1", "toolName": "bash",
        "args": { "command": "ls" },
    })));
    assert_eq!(
        frames,
        [json!({
            "type": "tool_execution_start", "toolCallId": "c1", "toolName": "bash",
            "args": { "command": "ls" },
        })]
    );
}

#[test]
fn tool_output_windows_trim_utf16_units_and_append() {
    let mut translator = translator(CoalesceMode::Immediate);
    start_tool(&mut translator);
    let frame = tool_update(
        &mut translator,
        &json!({ "output": { "set": "héllo 😀 world" } }),
    );
    assert_eq!(
        frame["partialResult"],
        json!({ "content": [{ "type": "text", "text": "héllo 😀 world" }], "details": null })
    );
    assert_eq!(frame["args"], json!({ "command": "ls" }));
    // "héllo " is 6 UTF-16 units.
    let frame = tool_update(&mut translator, &json!({ "output": { "trimStart": 6 } }));
    assert_eq!(frame["partialResult"]["content"][0]["text"], "😀 world");
    // One unit ends inside the surrogate pair: the whole char goes.
    let frame = tool_update(
        &mut translator,
        &json!({ "output": { "trimStart": 1, "append": "!" } }),
    );
    assert_eq!(frame["partialResult"]["content"][0]["text"], " world!");
    assert_eq!(translator.mirror().tool("c1").unwrap().output, " world!");
}

#[test]
fn utf16_front_trim_never_splits_a_char() {
    let mut text = "a😀é".to_owned();
    trim_utf16_front(&mut text, 2);
    assert_eq!(text, "é");
    let mut text = "a😀é".to_owned();
    trim_utf16_front(&mut text, 3);
    assert_eq!(text, "é");
    let mut text = "abc".to_owned();
    trim_utf16_front(&mut text, 10);
    assert_eq!(text, "");
    let mut text = "abc".to_owned();
    trim_utf16_front(&mut text, 0);
    assert_eq!(text, "abc");
}

#[test]
fn a_starting_status_shows_its_message_as_the_loader_note() {
    let mut translator = translator(CoalesceMode::Immediate);
    start_tool(&mut translator);
    let details = json!({ "status": "starting", "message": "Starting the Python kernel" });
    let frame = tool_update(
        &mut translator,
        &json!({ "output": { "set": "raw" }, "details": details }),
    );
    assert_eq!(
        frame["partialResult"],
        json!({
            "content": [{ "type": "text", "text": "Starting the Python kernel" }],
            "details": details,
        })
    );
    // Removed details (`Some(null)`, which JSON cannot spell) clear the note.
    let frames = translator.translate(&AgentEvent::ToolExecutionUpdate {
        call: ToolEventCall {
            tool_call_id: "c1".to_owned(),
            tool_name: "bash".to_owned(),
            task_id: None,
            parent_tool_call_id: None,
            parent_task_id: None,
        },
        output: None,
        details: Some(JsonValue::Null),
        diagnostics: None,
    });
    let frame = &frames[0];
    assert_eq!(
        frame["partialResult"],
        json!({ "content": [{ "type": "text", "text": "raw" }], "details": null })
    );
}

#[test]
fn tool_end_reports_the_result_entry() {
    let mut translator = translator(CoalesceMode::Immediate);
    start_tool(&mut translator);
    let result = json!({
        "role": "toolResult", "toolCallId": "c1", "toolName": "bash",
        "content": [{ "type": "text", "text": "out" }], "details": { "exit": 0 },
        "isError": false, "timestamp": 3,
    });
    let frames = translator.translate(&event(json!({
        "type": "tool_execution_end", "toolCallId": "c1", "toolName": "bash",
        "entry": entry(11, "pi.tool-result", Some(result), None),
    })));
    assert_eq!(
        frames,
        [json!({
            "type": "tool_execution_end", "toolCallId": "c1", "toolName": "bash",
            "result": { "content": [{ "type": "text", "text": "out" }], "details": { "exit": 0 } },
            "isError": false,
        })]
    );
    assert!(translator.mirror().tools.is_empty());
}

#[test]
fn a_faulted_tool_ends_with_its_batch_failure_or_the_bare_fact() {
    let end = json!({ "type": "tool_execution_end", "toolCallId": "c1", "toolName": "bash" });
    let mut translator = translator(CoalesceMode::Immediate);
    start_tool(&mut translator);
    let frames = translator.translate_batch(&[
        event(end.clone()),
        event(
            json!({ "type": "task_failed", "taskId": 9, "kind": "pi.tool", "message": "crashed" }),
        ),
    ]);
    assert_eq!(
        frames,
        [json!({
            "type": "tool_execution_end", "toolCallId": "c1", "toolName": "bash",
            "result": { "content": [{ "type": "text", "text": "crashed" }], "details": null },
            "isError": true,
        })]
    );

    start_tool(&mut translator);
    let frames = translator.translate(&event(end));
    assert_eq!(
        frames[0]["result"]["content"][0]["text"],
        "Tool execution ended without a result"
    );
    assert_eq!(frames[0]["isError"], true);
}

#[test]
fn custom_entries_go_out_as_a_message_pair() {
    let mut translator = translator(CoalesceMode::Immediate);
    let display_only = entry(
        5,
        "eukhe.custom",
        None,
        Some(
            json!({ "customType": "compaction_outcome", "content": "done", "display": true,
                     "details": { "success": true } }),
        ),
    );
    let frames = translator.translate(&event(
        json!({ "type": "entry_appended", "entry": display_only }),
    ));
    let message = json!({
        "role": "custom", "customType": "compaction_outcome", "content": "done",
        "display": true, "details": { "success": true }, "timestamp": 0,
    });
    assert_eq!(
        frames,
        [
            json!({ "type": "message_start", "message": message }),
            json!({ "type": "message_end", "message": message }),
        ]
    );

    let user =
        json!({ "role": "user", "content": [{ "type": "text", "text": "ctx" }], "timestamp": 7 });
    let visible = entry(
        6,
        "eukhe.custom",
        Some(user),
        Some(json!({ "customType": "goal_context", "display": false })),
    );
    let frames = translator.translate(&event(json!({ "type": "message_end", "entry": visible })));
    assert_eq!(types(&frames), ["message_start", "message_end"]);
    assert_eq!(
        frames[1]["message"],
        json!({
            "role": "custom", "customType": "goal_context",
            "content": [{ "type": "text", "text": "ctx" }], "display": false, "timestamp": 7,
        })
    );
    assert_eq!(translator.mirror().entries.len(), 2);

    // Other display-only entries add no frames.
    let state = entry(
        7,
        "eukhe.custom-state",
        None,
        Some(json!({ "customType": "x" })),
    );
    let frames = translator.translate(&event(json!({ "type": "entry_appended", "entry": state })));
    assert!(frames.is_empty());
}

/// A committed refinement audit row (`eukhe.refinement` custom state)
/// surfaces as `refine_complete` carrying the refinement result.
#[test]
fn a_refinement_audit_row_goes_out_as_refine_complete() {
    let mut translator = translator(CoalesceMode::Immediate);
    let result = json!({
        "summary": "one edit",
        "appliedEdits": [{ "action": "create", "kind": "memory", "id": "m1", "applied": true }],
    });
    let audit = entry(
        8,
        "eukhe.custom-state",
        None,
        Some(json!({ "customType": "eukhe.refinement", "data": result })),
    );
    let frames = translator.translate(&event(json!({ "type": "entry_appended", "entry": audit })));
    assert_eq!(
        frames,
        [json!({ "type": "refine_complete", "result": result })]
    );
}

#[test]
fn compaction_end_reports_the_placed_summary() {
    let answer = entry(
        1,
        "pi.assistant",
        Some(assistant(json!([]), "stop", 1234)),
        None,
    );
    let mut translator =
        EventTranslator::new(&snapshot(vec![answer], &json!({})), CoalesceMode::Immediate);
    let frames = translator.translate(&event(json!({
        "type": "compaction_start", "taskId": 7, "reason": "threshold", "blocking": true,
    })));
    assert_eq!(
        frames,
        [json!({ "type": "compaction_start", "reason": "threshold" })]
    );
    assert!(translator.mirror().is_compacting());

    let wrapped = "The conversation history before this point was compacted into the following summary:\n\n<summary>\nSUMMARY\n</summary>";
    let mut summary = entry(
        2,
        "pi.compaction",
        Some(
            json!({ "role": "user", "content": [{ "type": "text", "text": wrapped }], "timestamp": 8 }),
        ),
        Some(json!({ "reason": "threshold" })),
    );
    summary["byTaskId"] = json!(7);
    let frames = translator.translate(&event(json!({ "type": "message_end", "entry": summary })));
    assert!(frames.is_empty());
    let frames = translator.translate(&event(json!({
        "type": "compaction_end", "taskId": 7, "reason": "threshold",
    })));
    assert_eq!(
        frames,
        [json!({
            "type": "compaction_end", "reason": "threshold",
            "result": { "summary": "SUMMARY", "tokensBefore": 1234 }, "aborted": false,
            "willRetry": false,
        })]
    );
    assert!(!translator.mirror().is_compacting());
    assert_eq!(translator.mirror().entries.len(), 2);
}

#[test]
fn a_faulted_compaction_ends_with_its_failure() {
    let mut translator = translator(CoalesceMode::Immediate);
    translator.translate(&event(json!({
        "type": "compaction_start", "taskId": 8, "reason": "manual", "blocking": false,
    })));
    let frames = translator.translate_batch(&[
        event(json!({ "type": "compaction_end", "taskId": 8, "reason": "manual" })),
        event(json!({ "type": "task_failed", "taskId": 8, "kind": "pi.compaction", "message": "boom" })),
    ]);
    assert_eq!(
        frames,
        [json!({
            "type": "compaction_end", "reason": "manual", "result": null, "aborted": false,
            "willRetry": false, "errorMessage": "boom",
        })]
    );
}

#[test]
fn turn_end_carries_a_generation_failure_of_its_turn() {
    let mut translator = translator(CoalesceMode::Immediate);
    assert_eq!(
        translator.translate(&event(json!({ "type": "turn_start" }))),
        [json!({ "type": "turn_start" })]
    );
    let failed = translator.translate(&event(json!({
        "type": "task_failed", "taskId": 4, "kind": "pi.generation", "message": "429",
    })));
    assert!(failed.is_empty());
    assert_eq!(
        translator.translate(&event(json!({ "type": "turn_end" }))),
        [json!({ "type": "turn_end", "error": "429" })]
    );
    translator.translate(&event(json!({ "type": "turn_start" })));
    assert_eq!(
        translator.translate(&event(json!({ "type": "turn_end" }))),
        [json!({ "type": "turn_end" })]
    );
}

#[test]
fn run_end_clears_the_live_state() {
    let mut translator = translator(CoalesceMode::Coalesced);
    translator.translate(&event(json!({ "type": "run_start", "inputs": [3] })));
    assert!(translator.mirror().is_streaming());
    start_streaming(&mut translator);
    translator.translate(&update(json!([
        { "type": "text_start", "contentIndex": 0, "block": { "type": "text", "text": "" } },
    ])));
    // Any other frame flushes the parked update first.
    let frames = translator.translate(&event(json!({
        "type": "tool_execution_start", "toolCallId": "c1", "toolName": "bash", "args": {},
    })));
    assert_eq!(types(&frames), ["message_update", "tool_execution_start"]);
    assert!(!translator.has_parked());
    translator.translate(&event(json!({
        "type": "auto_retry_start", "attempt": 1, "at": 0.0, "errorMessage": "overloaded",
    })));
    assert_eq!(translator.mirror().retry_attempt, Some(1));
    let frames = translator.translate(&event(json!({ "type": "run_end", "inputs": [3] })));
    assert_eq!(frames, [json!({ "type": "agent_end", "messages": [] })]);
    let mirror = translator.mirror();
    assert!(!mirror.is_streaming());
    assert!(mirror.partial.is_none());
    assert!(mirror.tools.is_empty());
    assert!(mirror.retry_attempt.is_none());
    assert!(!translator.has_parked());
}

#[test]
fn auto_retry_frames() {
    let mut translator = translator(CoalesceMode::Immediate);
    let frames = translator.translate(&event(json!({
        "type": "auto_retry_start", "attempt": 2, "at": 0.0, "errorMessage": "overloaded",
    })));
    assert_eq!(
        frames,
        [
            json!({ "type": "auto_retry_start", "attempt": 2, "delayMs": 0, "errorMessage": "overloaded" })
        ]
    );
    let frames = translator.translate(&event(json!({ "type": "auto_retry_end", "attempt": 2 })));
    assert_eq!(
        frames,
        [json!({ "type": "auto_retry_end", "success": true, "attempt": 2 })]
    );
    assert_eq!(retry_delay_ms(2_500.0, 1_000.0), 1_500);
    assert_eq!(retry_delay_ms(1_000.0, 2_500.0), 0);
}

#[test]
fn a_snapshot_seeds_and_replaces_the_mirror() {
    let call = assistant(
        json!([{ "type": "toolCall", "id": "c1", "name": "bash", "arguments": { "command": "ls" } }]),
        "toolUse",
        1,
    );
    let seeded = snapshot(
        vec![entry(1, "pi.assistant", Some(call), None)],
        &json!({
            "run": { "inputs": [3] },
            "generation": { "attempt": 2, "retry": { "at": 0.0, "error": "x" } },
            "tools": [
                { "callId": "c1", "name": "bash", "status": "running", "output": "partial",
                  "details": { "status": "running" } },
                { "callId": "c2", "name": "bash", "status": "pending" },
            ],
            "compactions": [{ "taskId": 7, "reason": "overflow", "blocking": true, "attempt": 1 }],
            "inbox": [{ "id": 12, "mode": "steer" }],
        }),
    );
    let mut translator = EventTranslator::new(&seeded, CoalesceMode::Coalesced);
    let mirror = translator.mirror();
    assert!(mirror.is_streaming() && mirror.is_compacting());
    assert_eq!(mirror.retry_attempt, Some(2));
    assert_eq!(
        mirror.tools,
        [RunningTool {
            call_id: "c1".to_owned(),
            name: "bash".to_owned(),
            args: json!({ "command": "ls" }),
            output: "partial".to_owned(),
            details: Some(json!({ "status": "running" })),
        }]
    );
    assert_eq!(mirror.inbox.len(), 1);

    start_streaming(&mut translator);
    translator.translate(&update(json!([
        { "type": "text_start", "contentIndex": 0, "block": { "type": "text", "text": "" } },
    ])));
    let frames = translator.translate(&AgentEvent::Snapshot(snapshot(Vec::new(), &json!({}))));
    assert!(frames.is_empty());
    assert!(!translator.has_parked());
    assert_eq!(
        translator.mirror(),
        &ConversationMirror::from_snapshot(&snapshot(Vec::new(), &json!({})))
    );
}

#[test]
fn bookkeeping_events_update_only_the_mirror() {
    let mut translator = translator(CoalesceMode::Immediate);
    let inbox = translator.translate(&event(json!({
        "type": "inbox_update", "items": [{ "id": 5, "mode": "followUp" }],
    })));
    assert!(inbox.is_empty());
    assert_eq!(translator.mirror().inbox[0].mode, "followUp");
    let bash = entry(
        3,
        "eukhe.bash",
        Some(json!({ "role": "user", "content": "Ran `ls`", "timestamp": 1 })),
        Some(json!({ "command": "ls", "output": "", "cancelled": false, "truncated": false })),
    );
    assert!(translator
        .translate(&event(json!({ "type": "message_end", "entry": bash })))
        .is_empty());
    assert!(translator
        .translate(&event(json!({ "type": "deferred_poll", "pollAt": 1.0 })))
        .is_empty());
    assert_eq!(translator.mirror().entries.len(), 1);
}
