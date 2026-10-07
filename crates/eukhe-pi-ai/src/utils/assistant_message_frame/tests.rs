//! Port of `assistant-message-frame.test.ts`.
//!
//! TS events share one live `partial` that providers keep mutating; Rust
//! events own their partial, so the "live partial" cases hand each event the
//! advanced partial TS would observe when the queued event is encoded.

use serde_json::json;

use eukhe_types::pi_ai::{AssistantMessageDiagnostic, DoneReason, ErrorReason, JsonObject, Usage};

use super::*;

fn seed() -> AssistantMessage {
    AssistantMessage {
        content: Vec::new(),
        api: "test-api".into(),
        provider: "test-provider".into(),
        model: "test-model".into(),
        response_model: None,
        response_id: None,
        provider_thinking_level: None,
        thinking_level: None,
        diagnostics: None,
        usage: Usage::default(),
        stop_reason: StopReason::Pending,
        deferred: None,
        error_message: None,
        raw_stop_reason: None,
        end_turn: None,
        timestamp: 1,
    }
}

fn frame(
    encoder: &mut AssistantMessageFrameEncoder,
    event: &AssistantMessageEvent,
) -> AssistantMessageFrame {
    encoder
        .encode(event)
        .unwrap()
        .unwrap_or_else(|| panic!("Expected {} event to produce a frame", event.type_name()))
}

fn text(text: &str) -> AssistantContentBlock {
    AssistantContentBlock::Text(TextContent::new(text))
}

fn object(value: serde_json::Value) -> JsonObject {
    let serde_json::Value::Object(map) = value else {
        panic!("expected a JSON object")
    };
    map
}

fn tool_call(id: &str, name: &str, arguments: serde_json::Value) -> ToolCall {
    ToolCall {
        id: id.into(),
        name: name.into(),
        arguments: object(arguments),
        thought_signature: None,
        namespace: None,
    }
}

fn with_content(blocks: Vec<AssistantContentBlock>) -> AssistantMessage {
    AssistantMessage {
        content: blocks,
        ..seed()
    }
}

fn reduce(frames: &[AssistantMessageFrame]) -> Option<AssistantMessage> {
    reduce_assistant_message_frames(frames).unwrap()
}

fn reduce_error(frames: &[AssistantMessageFrame]) -> String {
    reduce_assistant_message_frames(frames)
        .unwrap_err()
        .to_string()
}

fn start_frame() -> AssistantMessageFrame {
    AssistantMessageFrame::Start { partial: seed() }
}

#[test]
fn uses_authoritative_text_end_content_and_signature() {
    let mut encoder = AssistantMessageFrameEncoder::new();
    let mut frames = vec![frame(
        &mut encoder,
        &AssistantMessageEvent::Start { partial: seed() },
    )];
    let started = with_content(vec![text("Hello ")]);
    frames.push(frame(
        &mut encoder,
        &AssistantMessageEvent::TextStart {
            content_index: 0,
            partial: started,
        },
    ));
    let advanced = with_content(vec![AssistantContentBlock::Text(TextContent {
        text_signature: Some("sig-text".into()),
        ..TextContent::new("Hello world")
    })]);
    frames.push(frame(
        &mut encoder,
        &AssistantMessageEvent::TextDelta {
            content_index: 0,
            delta: "incorrect".into(),
            partial: advanced.clone(),
        },
    ));
    frames.push(frame(
        &mut encoder,
        &AssistantMessageEvent::TextEnd {
            content_index: 0,
            content: "Hello world".into(),
            partial: advanced,
        },
    ));
    assert_eq!(
        frames.last(),
        Some(&AssistantMessageFrame::TextEnd {
            content_index: 0,
            content: "Hello world".into(),
            text_signature: Some("sig-text".into()),
        })
    );
    assert_eq!(
        reduce(&frames).unwrap().content,
        vec![AssistantContentBlock::Text(TextContent {
            text_signature: Some("sig-text".into()),
            ..TextContent::new("Hello world")
        })]
    );
}

#[test]
fn preserves_provider_thinking_level_from_the_stream_start() {
    let partial = AssistantMessage {
        provider_thinking_level: Some("high".into()),
        ..seed()
    };
    let mut encoder = AssistantMessageFrameEncoder::new();
    let start = frame(&mut encoder, &AssistantMessageEvent::Start { partial });
    let AssistantMessageFrame::Start { partial } = &start else {
        panic!("start frame")
    };
    assert_eq!(partial.provider_thinking_level.as_deref(), Some("high"));
    assert_eq!(
        reduce(&[start]).unwrap().provider_thinking_level.as_deref(),
        Some("high")
    );
}

#[test]
fn preserves_initial_and_final_thinking_metadata_including_redaction() {
    let thinking = |signature: &str| {
        AssistantContentBlock::Thinking(ThinkingContent {
            thinking: "[redacted]".into(),
            thinking_signature: Some(signature.into()),
            redacted: Some(true),
        })
    };
    let mut encoder = AssistantMessageFrameEncoder::new();
    let mut frames = vec![frame(
        &mut encoder,
        &AssistantMessageEvent::Start { partial: seed() },
    )];
    frames.push(frame(
        &mut encoder,
        &AssistantMessageEvent::ThinkingStart {
            content_index: 0,
            partial: with_content(vec![thinking("encrypted-start")]),
        },
    ));
    frames.push(frame(
        &mut encoder,
        &AssistantMessageEvent::ThinkingEnd {
            content_index: 0,
            content: "[redacted]".into(),
            partial: with_content(vec![thinking("encrypted-final")]),
        },
    ));
    assert_eq!(
        frames.last(),
        Some(&AssistantMessageFrame::ThinkingEnd {
            content_index: 0,
            content: "[redacted]".into(),
            thinking_signature: Some("encrypted-final".into()),
            redacted: Some(true),
        })
    );
    assert_eq!(
        reduce(&frames).unwrap().content[0],
        thinking("encrypted-final")
    );
}

#[test]
fn parses_unfinished_tool_json_once_and_uses_authoritative_completed_arguments() {
    let initial_frames = vec![
        start_frame(),
        AssistantMessageFrame::ToolCallStart {
            content_index: 0,
            tool_call: tool_call("initial-id", "write", json!({})),
        },
        AssistantMessageFrame::ToolCallDelta {
            content_index: 0,
            delta: r#"{"path":"READ"#.into(),
        },
    ];
    let AssistantContentBlock::ToolCall(call) = &reduce(&initial_frames).unwrap().content[0] else {
        panic!("tool call")
    };
    assert_eq!(call.arguments, object(json!({ "path": "READ" })));

    let mut complete_frames = initial_frames;
    complete_frames.push(AssistantMessageFrame::ToolCallDelta {
        content_index: 0,
        delta: r#"ME.md","lines":[1,2]}"#.into(),
    });
    complete_frames.push(AssistantMessageFrame::ToolCallEnd {
        content_index: 0,
        id: "final-id".into(),
        name: "write_file".into(),
        arguments: object(json!({ "path": "final.md", "lines": [3] })),
        thought_signature: Some("thought".into()),
        namespace: Some("files".into()),
    });
    assert_eq!(
        reduce(&complete_frames).unwrap().content[0],
        AssistantContentBlock::ToolCall(ToolCall {
            thought_signature: Some("thought".into()),
            namespace: Some("files".into()),
            ..tool_call(
                "final-id",
                "write_file",
                json!({ "path": "final.md", "lines": [3] })
            )
        })
    );
}

#[test]
fn reconciles_queued_text_events_against_one_advanced_live_partial_without_duplicate_content() {
    // Every queued event observes the partial after all four deltas.
    let live = with_content(vec![text("Hello world")]);
    let mut events = vec![
        AssistantMessageEvent::Start {
            partial: live.clone(),
        },
        AssistantMessageEvent::TextStart {
            content_index: 0,
            partial: live.clone(),
        },
    ];
    for delta in ["Hel", "lo", " ", "world"] {
        events.push(AssistantMessageEvent::TextDelta {
            content_index: 0,
            delta: delta.into(),
            partial: live.clone(),
        });
    }
    let mut encoder = AssistantMessageFrameEncoder::new();
    let frames: Vec<AssistantMessageFrame> = events
        .iter()
        .filter_map(|event| encoder.encode(event).unwrap())
        .collect();
    assert_eq!(
        frames
            .iter()
            .map(AssistantMessageFrame::type_name)
            .collect::<Vec<_>>(),
        ["start", "text_start"]
    );
    let AssistantMessageFrame::Start { partial } = &frames[0] else {
        panic!("start frame")
    };
    assert!(partial.content.is_empty());
    assert_eq!(partial.stop_reason, StopReason::Pending);
    assert_eq!(reduce(&frames).unwrap().content, vec![text("Hello world")]);
}

#[test]
fn trims_only_the_covered_prefix_when_a_start_snapshot_lands_inside_a_delta() {
    let partial = with_content(vec![text("Hel")]);
    let mut encoder = AssistantMessageFrameEncoder::new();
    let mut frames = vec![frame(
        &mut encoder,
        &AssistantMessageEvent::Start {
            partial: partial.clone(),
        },
    )];
    frames.push(frame(
        &mut encoder,
        &AssistantMessageEvent::TextStart {
            content_index: 0,
            partial: partial.clone(),
        },
    ));
    let delta = |delta: &str| AssistantMessageEvent::TextDelta {
        content_index: 0,
        delta: delta.into(),
        partial: partial.clone(),
    };
    assert_eq!(encoder.encode(&delta("He")).unwrap(), None);
    let remainder = encoder
        .encode(&delta("llo"))
        .unwrap()
        .expect("Expected uncovered text delta");
    assert_eq!(
        remainder,
        AssistantMessageFrame::TextDelta {
            content_index: 0,
            delta: "lo".into(),
        }
    );
    frames.push(remainder);
    assert_eq!(reduce(&frames).unwrap().content, vec![text("Hello")]);
}

#[test]
fn checkpoints_queued_tool_json_without_replaying_covered_deltas() {
    let live = with_content(vec![AssistantContentBlock::ToolCall(tool_call(
        "call",
        "write",
        json!({ "path": "README.md" }),
    ))]);
    let events = [
        AssistantMessageEvent::Start {
            partial: live.clone(),
        },
        AssistantMessageEvent::ToolCallStart {
            content_index: 0,
            partial: live.clone(),
        },
        AssistantMessageEvent::ToolCallDelta {
            content_index: 0,
            delta: r#"{"path":"READ"#.into(),
            partial: live.clone(),
        },
        AssistantMessageEvent::ToolCallDelta {
            content_index: 0,
            delta: r#"ME.md"}"#.into(),
            partial: live,
        },
    ];
    let mut encoder = AssistantMessageFrameEncoder::new();
    let frames: Vec<AssistantMessageFrame> = events
        .iter()
        .filter_map(|event| encoder.encode(event).unwrap())
        .collect();
    assert_eq!(
        frames
            .iter()
            .map(AssistantMessageFrame::type_name)
            .collect::<Vec<_>>(),
        ["start", "toolcall_start", "toolcall_checkpoint"]
    );
    assert_eq!(
        frames.last(),
        Some(&AssistantMessageFrame::ToolCallCheckpoint {
            content_index: 0,
            json: r#"{"path":"README.md"}"#.into(),
        })
    );
    assert_eq!(
        reduce(&frames).unwrap().content,
        vec![AssistantContentBlock::ToolCall(tool_call(
            "call",
            "write",
            json!({ "path": "README.md" })
        ))]
    );
}

#[test]
fn resumes_legacy_grammar_tool_json_from_initial_arguments() {
    let partial_with = |input: &str| {
        with_content(vec![AssistantContentBlock::ToolCall(tool_call(
            "call",
            "bash",
            json!({ "input": input }),
        ))])
    };
    let mut encoder = AssistantMessageFrameEncoder::new();
    let mut frames = vec![frame(
        &mut encoder,
        &AssistantMessageEvent::Start { partial: seed() },
    )];
    frames.push(frame(
        &mut encoder,
        &AssistantMessageEvent::ToolCallStart {
            content_index: 0,
            partial: partial_with("a"),
        },
    ));
    frames.push(frame(
        &mut encoder,
        &AssistantMessageEvent::ToolCallDelta {
            content_index: 0,
            delta: r#"{"input":"ab"#.into(),
            partial: partial_with("ab"),
        },
    ));
    frames.push(frame(
        &mut encoder,
        &AssistantMessageEvent::ToolCallDelta {
            content_index: 0,
            delta: r#"c"}"#.into(),
            partial: partial_with("abc"),
        },
    ));
    assert_eq!(
        frames[2..],
        [
            AssistantMessageFrame::ToolCallCheckpoint {
                content_index: 0,
                json: r#"{"input":"ab"#.into(),
            },
            AssistantMessageFrame::ToolCallDelta {
                content_index: 0,
                delta: r#"c"}"#.into(),
            },
        ]
    );
    assert_eq!(
        reduce(&frames).unwrap().content,
        vec![AssistantContentBlock::ToolCall(tool_call(
            "call",
            "bash",
            json!({ "input": "abc" })
        ))]
    );
}

#[test]
fn streams_tool_json_compactly_from_an_empty_argument_start() {
    let mut encoder = AssistantMessageFrameEncoder::new();
    let mut frames = vec![frame(
        &mut encoder,
        &AssistantMessageEvent::Start { partial: seed() },
    )];
    frames.push(frame(
        &mut encoder,
        &AssistantMessageEvent::ToolCallStart {
            content_index: 0,
            partial: with_content(vec![AssistantContentBlock::ToolCall(tool_call(
                "call",
                "bash",
                json!({}),
            ))]),
        },
    ));
    frames.push(frame(
        &mut encoder,
        &AssistantMessageEvent::ToolCallDelta {
            content_index: 0,
            delta: r#"{"command":"ls -la /tmp"}"#.into(),
            partial: with_content(vec![AssistantContentBlock::ToolCall(tool_call(
                "call",
                "bash",
                json!({ "command": "ls -la /tmp" }),
            ))]),
        },
    ));
    assert_eq!(
        frames.last(),
        Some(&AssistantMessageFrame::ToolCallDelta {
            content_index: 0,
            delta: r#"{"command":"ls -la /tmp"}"#.into(),
        })
    );
    let AssistantContentBlock::ToolCall(call) = &reduce(&frames).unwrap().content[0] else {
        panic!("tool call")
    };
    assert_eq!(call.arguments, object(json!({ "command": "ls -la /tmp" })));
}

#[test]
fn accepts_a_pre_generation_error_but_rejects_success_or_updates_before_start() {
    let failed = AssistantMessage {
        stop_reason: StopReason::Error,
        error_message: Some("setup failed".into()),
        ..seed()
    };
    assert_eq!(
        AssistantMessageFrameEncoder::new()
            .encode(&AssistantMessageEvent::Error {
                reason: ErrorReason::Error,
                error: failed,
            })
            .unwrap(),
        None
    );
    let completed = AssistantMessage {
        stop_reason: StopReason::Stop,
        ..seed()
    };
    let done_error = AssistantMessageFrameEncoder::new()
        .encode(&AssistantMessageEvent::Done {
            reason: DoneReason::Stop,
            message: completed,
        })
        .unwrap_err();
    assert!(done_error
        .to_string()
        .contains("done event appears before start"));
    let delta_error = AssistantMessageFrameEncoder::new()
        .encode(&AssistantMessageEvent::TextDelta {
            content_index: 0,
            delta: "x".into(),
            partial: seed(),
        })
        .unwrap_err();
    assert!(delta_error
        .to_string()
        .contains("text_delta event appears before start"));
}

#[test]
fn treats_end_signature_metadata_including_absence_as_authoritative() {
    let frames = vec![
        start_frame(),
        AssistantMessageFrame::TextStart {
            content_index: 0,
            content: TextContent {
                text_signature: Some("stale-text".into()),
                ..TextContent::new("")
            },
        },
        AssistantMessageFrame::TextEnd {
            content_index: 0,
            content: String::new(),
            text_signature: None,
        },
        AssistantMessageFrame::ThinkingStart {
            content_index: 1,
            content: ThinkingContent {
                thinking: String::new(),
                thinking_signature: Some("stale-thinking".into()),
                redacted: Some(true),
            },
        },
        AssistantMessageFrame::ThinkingEnd {
            content_index: 1,
            content: String::new(),
            thinking_signature: Some(String::new()),
            redacted: Some(false),
        },
        AssistantMessageFrame::ToolCallStart {
            content_index: 2,
            tool_call: ToolCall {
                thought_signature: Some("stale-tool".into()),
                namespace: Some("stale-namespace".into()),
                ..tool_call("call", "read", json!({}))
            },
        },
        AssistantMessageFrame::ToolCallEnd {
            content_index: 2,
            id: "call".into(),
            name: "read".into(),
            arguments: JsonObject::new(),
            thought_signature: None,
            namespace: None,
        },
    ];
    assert_eq!(
        reduce(&frames).unwrap().content,
        vec![
            text(""),
            AssistantContentBlock::Thinking(ThinkingContent {
                thinking: String::new(),
                thinking_signature: Some(String::new()),
                redacted: Some(false),
            }),
            AssistantContentBlock::ToolCall(tool_call("call", "read", json!({}))),
        ]
    );
}

#[test]
fn stores_authoritative_final_arguments_in_toolcall_end_frames() {
    let call = ToolCall {
        thought_signature: Some("thought".into()),
        namespace: Some("files".into()),
        ..tool_call("call-1", "read", json!({ "path": "README.md" }))
    };
    let partial = with_content(vec![AssistantContentBlock::ToolCall(call.clone())]);
    let mut encoder = AssistantMessageFrameEncoder::new();
    frame(
        &mut encoder,
        &AssistantMessageEvent::Start {
            partial: partial.clone(),
        },
    );
    frame(
        &mut encoder,
        &AssistantMessageEvent::ToolCallStart {
            content_index: 0,
            partial: partial.clone(),
        },
    );
    let end = frame(
        &mut encoder,
        &AssistantMessageEvent::ToolCallEnd {
            content_index: 0,
            tool_call: call,
            partial,
        },
    );
    assert_eq!(
        end,
        AssistantMessageFrame::ToolCallEnd {
            content_index: 0,
            id: "call-1".into(),
            name: "read".into(),
            arguments: object(json!({ "path": "README.md" })),
            thought_signature: Some("thought".into()),
            namespace: Some("files".into()),
        }
    );
}

#[test]
fn whitelists_public_block_fields_from_provider_shaped_partials() {
    // Rust blocks cannot carry provider scratch fields (`index`, `partialJson`);
    // the observable whitelist is the serialized frame: no foreign keys, an
    // empty start content, and no eukhe cache mark on streamed text.
    let partial = AssistantMessage {
        thinking_level: Some(eukhe_types::pi_ai::ModelThinkingLevel::High),
        ..with_content(vec![
            AssistantContentBlock::Text(TextContent {
                text_signature: Some("text-sig".into()),
                cache_breakpoint: Some(eukhe_types::pi_ai::CacheBreakpoint::Ephemeral),
                ..TextContent::new("visible")
            }),
            AssistantContentBlock::ToolCall(tool_call("call", "run", json!({ "value": 1 }))),
        ])
    };
    let mut encoder = AssistantMessageFrameEncoder::new();
    let start = frame(
        &mut encoder,
        &AssistantMessageEvent::Start {
            partial: partial.clone(),
        },
    );
    let text_start = frame(
        &mut encoder,
        &AssistantMessageEvent::TextStart {
            content_index: 0,
            partial,
        },
    );
    assert_eq!(
        serde_json::to_value(&start).unwrap()["partial"]["content"],
        json!([])
    );
    assert!(serde_json::to_value(&start).unwrap()["partial"]
        .get("thinkingLevel")
        .is_none());
    assert_eq!(
        serde_json::to_value(&text_start).unwrap(),
        json!({ "type": "text_start", "contentIndex": 0, "content": { "type": "text", "text": "visible", "textSignature": "text-sig" } })
    );
}

#[test]
fn supports_interleaved_streams_by_content_index() {
    let frames = vec![
        start_frame(),
        AssistantMessageFrame::TextStart {
            content_index: 0,
            content: TextContent::new(""),
        },
        AssistantMessageFrame::ToolCallStart {
            content_index: 1,
            tool_call: tool_call("call", "lookup", json!({})),
        },
        AssistantMessageFrame::ThinkingStart {
            content_index: 2,
            content: ThinkingContent::default(),
        },
        AssistantMessageFrame::TextDelta {
            content_index: 0,
            delta: "answer".into(),
        },
        AssistantMessageFrame::ToolCallDelta {
            content_index: 1,
            delta: r#"{"query":"pi"}"#.into(),
        },
        AssistantMessageFrame::ThinkingDelta {
            content_index: 2,
            delta: "check".into(),
        },
        AssistantMessageFrame::ToolCallEnd {
            content_index: 1,
            id: "call".into(),
            name: "lookup".into(),
            arguments: object(json!({ "query": "pi" })),
            thought_signature: None,
            namespace: None,
        },
        AssistantMessageFrame::TextEnd {
            content_index: 0,
            content: "answer".into(),
            text_signature: None,
        },
        AssistantMessageFrame::ThinkingEnd {
            content_index: 2,
            content: "check".into(),
            thinking_signature: None,
            redacted: None,
        },
    ];
    assert_eq!(
        reduce(&frames).unwrap().content,
        vec![
            text("answer"),
            AssistantContentBlock::ToolCall(tool_call("call", "lookup", json!({ "query": "pi" }))),
            AssistantContentBlock::Thinking(ThinkingContent {
                thinking: "check".into(),
                ..ThinkingContent::default()
            }),
        ]
    );
}

#[test]
fn snapshots_mutable_event_data_and_keeps_reduction_pure() {
    let mut partial = AssistantMessage {
        diagnostics: Some(vec![AssistantMessageDiagnostic {
            kind: "test".into(),
            timestamp: 2,
            error: None,
            details: Some(object(json!({ "value": "original" }))),
        }]),
        ..seed()
    };
    let mut encoder = AssistantMessageFrameEncoder::new();
    let start = frame(
        &mut encoder,
        &AssistantMessageEvent::Start {
            partial: partial.clone(),
        },
    );
    partial.diagnostics.as_mut().unwrap()[0]
        .details
        .as_mut()
        .unwrap()
        .insert("value".into(), json!("mutated"));
    partial.usage.cost.total = 99.0;
    partial
        .content
        .push(AssistantContentBlock::ToolCall(tool_call(
            "call",
            "run",
            json!({ "nested": { "value": "original" } }),
        )));
    let tool_start = frame(
        &mut encoder,
        &AssistantMessageEvent::ToolCallStart {
            content_index: 0,
            partial: partial.clone(),
        },
    );
    if let AssistantContentBlock::ToolCall(source) = &mut partial.content[0] {
        source
            .arguments
            .insert("nested".into(), json!({ "value": "mutated" }));
    }

    let frames = [start, tool_start];
    let mut reduced = reduce(&frames).unwrap();
    assert_eq!(
        reduced.diagnostics.as_ref().unwrap()[0]
            .details
            .as_ref()
            .unwrap()["value"],
        json!("original")
    );
    assert!(reduced.usage.cost.total.abs() < f64::EPSILON);
    let AssistantContentBlock::ToolCall(reduced_call) = &mut reduced.content[0] else {
        panic!("tool call")
    };
    assert_eq!(
        reduced_call.arguments["nested"],
        json!({ "value": "original" })
    );
    reduced_call
        .arguments
        .insert("nested".into(), json!("changed-output"));
    let AssistantMessageFrame::ToolCallStart { tool_call, .. } = &frames[1] else {
        panic!("tool start")
    };
    assert_eq!(
        tool_call.arguments["nested"],
        json!({ "value": "original" })
    );
}

#[test]
fn omits_terminal_events_because_settlement_is_separate() {
    let mut completed = AssistantMessageFrameEncoder::new();
    completed
        .encode(&AssistantMessageEvent::Start { partial: seed() })
        .unwrap();
    let message = AssistantMessage {
        stop_reason: StopReason::Stop,
        ..seed()
    };
    assert_eq!(
        completed
            .encode(&AssistantMessageEvent::Done {
                reason: DoneReason::Stop,
                message,
            })
            .unwrap(),
        None
    );
    let failed = AssistantMessage {
        stop_reason: StopReason::Error,
        error_message: Some("failed".into()),
        ..seed()
    };
    assert_eq!(
        AssistantMessageFrameEncoder::new()
            .encode(&AssistantMessageEvent::Error {
                reason: ErrorReason::Error,
                error: failed,
            })
            .unwrap(),
        None
    );
}

#[test]
fn returns_undefined_when_there_is_no_start_frame() {
    assert_eq!(reduce(&[]), None);
    assert_eq!(
        reduce(&[AssistantMessageFrame::TextDelta {
            content_index: 0,
            delta: "x".into(),
        }]),
        None
    );
}

#[test]
fn rejects_frames_before_start_wrong_block_kinds_duplicate_ends_and_index_gaps() {
    assert!(reduce_error(&[
        AssistantMessageFrame::TextDelta {
            content_index: 0,
            delta: "x".into(),
        },
        start_frame(),
    ])
    .contains("before the start frame"));
    assert!(reduce_error(&[
        start_frame(),
        AssistantMessageFrame::ToolCallStart {
            content_index: 0,
            tool_call: tool_call("call", "run", json!({})),
        },
        AssistantMessageFrame::TextDelta {
            content_index: 0,
            delta: "wrong".into(),
        },
    ])
    .contains("expected text block"));
    let text_end = AssistantMessageFrame::TextEnd {
        content_index: 0,
        content: String::new(),
        text_signature: None,
    };
    assert!(reduce_error(&[
        start_frame(),
        AssistantMessageFrame::TextStart {
            content_index: 0,
            content: TextContent::new(""),
        },
        text_end.clone(),
        text_end,
    ])
    .contains("follows the end"));
    assert!(reduce_error(&[
        start_frame(),
        AssistantMessageFrame::TextStart {
            content_index: 1,
            content: TextContent::new(""),
        },
    ])
    .contains("would leave a gap"));
}

#[test]
fn rejects_conversion_events_whose_content_index_points_to_the_wrong_block_kind() {
    let mut encoder = AssistantMessageFrameEncoder::new();
    encoder
        .encode(&AssistantMessageEvent::Start { partial: seed() })
        .unwrap();
    let error = encoder
        .encode(&AssistantMessageEvent::TextStart {
            content_index: 0,
            partial: with_content(vec![AssistantContentBlock::Thinking(
                ThinkingContent::default(),
            )]),
        })
        .unwrap_err();
    assert!(error
        .to_string()
        .contains("text_start event points to thinking block"));
}

#[test]
fn frames_serialize_with_the_ts_wire_shape() {
    let frame = AssistantMessageFrame::ToolCallEnd {
        content_index: 3,
        id: "c".into(),
        name: "n".into(),
        arguments: JsonObject::new(),
        thought_signature: None,
        namespace: Some("ns".into()),
    };
    let value = serde_json::to_value(&frame).unwrap();
    assert_eq!(
        value,
        json!({ "type": "toolcall_end", "contentIndex": 3, "id": "c", "name": "n", "arguments": {}, "namespace": "ns" })
    );
    assert_eq!(
        serde_json::from_value::<AssistantMessageFrame>(value).unwrap(),
        frame
    );
}
