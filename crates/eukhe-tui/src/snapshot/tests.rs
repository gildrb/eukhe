use super::*;
use crate::chat::StatusKind;
use eukhe_types::daemon::{
    BashRun, CompactionReason, CompactionResult, ErrorSeverity, SessionEvent,
};
use eukhe_types::input_origin::{ChildExit, InputOrigin, Report};
use serde_json::json;

/// Decode one wire fixture into its typed form.
fn wire<T: serde::de::DeserializeOwned>(value: Value) -> T {
    serde_json::from_value(value).expect("fixture decodes")
}

/// Overlay `fields` onto `base`, merging nested objects key by key.
fn overlay(base: &mut Value, fields: Value) {
    match (base, fields) {
        (Value::Object(base), Value::Object(fields)) => {
            for (key, value) in fields {
                overlay(base.entry(key).or_insert(Value::Null), value);
            }
        }
        (base, fields) => *base = fields,
    }
}

/// A wire message fixture completed with the fields its typed form
/// requires and the test does not care about: a zero timestamp, and an
/// assistant message's provider metadata, usage, and `stop` reason.
fn complete_message(message: Value) -> Value {
    let mut completed = if message["role"] == "assistant" {
        json!({
            "content": [],
            "api": "faux",
            "provider": "faux",
            "model": "faux-1",
            "usage": {
                "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
                "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
            },
            "stopReason": "stop",
            "timestamp": 0,
        })
    } else {
        json!({ "timestamp": 0 })
    };
    overlay(&mut completed, message);
    completed
}

/// One typed transcript message from its (completed) wire fixture.
fn msg(message: Value) -> AgentMessage {
    wire(complete_message(message))
}

/// The typed transcript of completed wire fixtures.
fn msgs(messages: impl IntoIterator<Item = Value>) -> Vec<AgentMessage> {
    messages.into_iter().map(msg).collect()
}

/// One typed session event from its wire fixture; the messages it
/// carries are completed like [`msg`]'s.
fn event(mut event: Value) -> SessionEvent {
    if let Some(message) = event.get_mut("message") {
        *message = complete_message(message.take());
    }
    wire(event)
}

/// The display text of a user message.
fn user_text(message: &AgentMessage) -> Option<String> {
    let AgentMessage::User(user) = message else {
        panic!("a user message: {message:?}");
    };
    user_display_text(&user.content)
}

fn test_view() -> crate::view::AgentView {
    crate::view::AgentView::new(crate::theme::Theme::builtin(
        "eukhe",
        crate::theme::ColorMode::TrueColor,
    ))
}

fn card_of(view: &crate::view::AgentView) -> Option<&ToolCallCard> {
    view.chat.iter().find_map(|entry| match entry {
        ChatEntry::Tool(card) => Some(card.as_ref()),
        _ => None,
    })
}

fn cards_of(view: &crate::view::AgentView) -> Vec<ToolCallCard> {
    view.chat
        .iter()
        .filter_map(|entry| match entry {
            ChatEntry::Tool(card) => Some((**card).clone()),
            _ => None,
        })
        .collect()
}

fn rendered_card_text(view: &crate::view::AgentView) -> Vec<String> {
    let Some(card) = card_of(view) else {
        return Vec::new();
    };
    crate::tool_card::render_tool_card(
        card,
        0,
        crate::chat::Detail::Overview,
        &view.theme,
        100,
        true,
    )
    .iter()
    .map(|line| line.iter().map(|span| span.content.as_str()).collect())
    .collect()
}

#[test]
fn image_only_user_message_shows_the_image_placeholder() {
    let message = msg(json!({
        "role": "user",
        "content": [
            { "type": "image", "data": "QUJD", "mimeType": "image/png" }
        ]
    }));
    assert_eq!(user_text(&message), Some("[image]".to_string()));
    assert_eq!(
        message_value_to_entries(&message),
        vec![ChatEntry::User {
            text: "[image]".to_string()
        }]
    );
}

#[test]
fn a_skill_block_user_message_decodes_to_the_card() {
    // TS `addMessageToChat`'s user case: the persisted user message
    // that carried a skill invocation parses into the card + the
    // trailing argument text, never the raw block.
    let message = msg(json!({
        "role": "user",
        "content": "<skill name=\"lookup\" location=\"/s/SKILL.md\">\nRun one query.\n</skill>\n\nfind parity tuis"
    }));
    let entries = message_value_to_entries(&message);
    assert!(
        matches!(
            entries.as_slice(),
            [
                ChatEntry::SkillInvocation(card),
                ChatEntry::User { text }
            ] if card.name == "lookup"
                && card.content == "Run one query."
                && text == "find parity tuis"
        ),
        "entries: {entries:?}"
    );
}

#[test]
fn user_message_with_text_and_image_keeps_the_text() {
    let message = msg(json!({
        "role": "user",
        "content": [
            { "type": "text", "text": "look at this" },
            { "type": "image", "data": "QUJD", "mimeType": "image/png" }
        ]
    }));
    assert_eq!(user_text(&message), Some("look at this".to_string()));
}

#[test]
fn empty_user_message_renders_no_entry() {
    let message = msg(json!({ "role": "user", "content": [] }));
    assert_eq!(user_text(&message), None);
    assert!(message_value_to_entries(&message).is_empty());
}

/// TS `orderMessagesForTranscript`: the wire context is summary-first
/// for the model, but the transcript presents the summary at its
/// chronological boundary -- after the retained messages
/// (`retainedMessageCount`), before anything appended after the
/// compaction.
#[test]
fn transcript_presents_the_summary_after_the_retained_tail() {
    let messages = [
        msg(json!({
            "role": "compactionSummary", "summary": "the story",
            "retainedMessageCount": 2, "tokensBefore": 12, "timestamp": 30u64
        })),
        msg(json!({"role": "user", "content": "second turn", "timestamp": 20u64})),
        msg(json!({
            "role": "assistant",
            "content": [{ "type": "text", "text": "kept intact" }],
            "timestamp": 25u64
        })),
        msg(json!({
            "role": "custom", "customType": "session_slash_command",
            "content": "/compact focus on the goal", "display": true, "timestamp": 40u64,
            "details": { "command": {
                "name": "compact",
                "args": "focus on the goal",
                "text": "/compact focus on the goal"
            } }
        })),
    ];
    let entries = transcript_to_entries(&messages);
    let order: Vec<String> = entries
        .iter()
        .filter_map(|entry| match entry {
            ChatEntry::User { .. } => Some("user".to_string()),
            ChatEntry::Assistant { .. } => Some("assistant".to_string()),
            ChatEntry::CompactionSummary { .. } => Some("summary".to_string()),
            ChatEntry::SlashCommand { .. } => Some("slash".to_string()),
            _ => None,
        })
        .collect();
    assert_eq!(order, ["user", "assistant", "summary", "slash"]);
}

fn slim_attach() -> Value {
    json!({
        "protocol": { "name": "eukhe.daemon", "version": 7 },
        "activeSessionId": "abc123def456",
        "snapshot": {
            "activeSessionId": "abc123def456",
            "summary": { "id": "abc123def456", "cwd": "/tmp" },
            "state": {
                "activeSessionId": "abc123def456",
                "cwd": "/tmp",
                "sessionId": "0199-sess",
                "sessionName": "my session",
                "model": null,
                "thinkingLevel": "default",
                "serviceTier": "auto",
                "isStreaming": false,
                "isCompacting": false,
                "retryAttempt": 0,
                "steeringMode": "all",
                "followUpMode": "all",
                "autoCompactionEnabled": false,
                "messageCount": 2,
                "sessionActions": { "queuedCount": 0, "steering": [], "followUps": [] },
                "compactionCount": 0,
                "goal": null,
                "scopedModels": [],
                "activeToolNames": [],
            },
            "messages": [
                { "role": "user", "content": "hello", "timestamp": 1 },
                complete_message(json!({
                    "role": "assistant",
                    "content": [{ "type": "text", "text": "hi there" }],
                    "provider": "scripted",
                    "model": "faux-1",
                    "usage": { "input": 120, "output": 8 },
                    "timestamp": 2,
                })),
            ],
            "lastEventSequence": 9,
            "lastEventCursor": { "generation": "g", "sequence": 9 },
            "children": [],
        },
        "replay": { "status": "complete", "toSequence": 9, "toCursor": { "generation": "g", "sequence": 9 } },
        "lastEventSequence": 9,
        "lastEventCursor": { "generation": "g", "sequence": 9 },
        "client": { "id": "c1", "capabilities": ["attach_snapshot", "event_sequence", "slim_attach"] },
    })
}

/// The rebuild's loader anchor (the operator's 2026-09-28 rule: the
/// waiting/executing timer counts since the LAST HUMAN PROMPT): the
/// reconstruct reads the NEWEST user message's wall-clock ms timestamp
/// and skips non-user messages.
#[test]
fn reconstructs_the_last_user_prompt_timestamp() {
    // The numeric ms form (the live engine's wire shape).
    let mut attach = slim_attach();
    let snapshot = attach.get_mut("snapshot").expect("snapshot");
    let messages = snapshot
        .get_mut("messages")
        .expect("messages")
        .as_array_mut()
        .expect("messages array");
    assert_eq!(messages[0].get("role"), Some(&json!("user")));
    messages[0]["timestamp"] = json!(1_700_000_000_000u64);
    let view = reconstruct(&attach_data_from_response(attach).unwrap()).expect("reconstructs");
    assert_eq!(view.last_user_prompt_ms, Some(1_700_000_000_000));
    // The newest user prompt wins over an older one and over a newer
    // non-user message.
    let mut attach = slim_attach();
    let messages = attach
        .get_mut("snapshot")
        .expect("snapshot")
        .get_mut("messages")
        .expect("messages")
        .as_array_mut()
        .expect("messages array");
    messages.push(json!({
        "role": "user",
        "content": "newer",
        "timestamp": 1_700_000_000_050u64,
    }));
    messages.push(complete_message(json!({
        "role": "assistant",
        "content": [{ "type": "text", "text": "newest, not a prompt" }],
        "timestamp": 1_700_000_000_090u64,
    })));
    let view = reconstruct(&attach_data_from_response(attach).unwrap()).expect("reconstructs");
    assert_eq!(view.last_user_prompt_ms, Some(1_700_000_000_050));
}

#[test]
fn reconstructs_slim_attach() {
    let data = attach_data_from_response(slim_attach()).unwrap();
    assert_eq!(data.active_session_id, "abc123def456");
    let view = reconstruct(&data).expect("reconstructs");
    assert_eq!(view.chat.len(), 2);
    assert!(matches!(&view.chat[0], ChatEntry::User { text } if text == "hello"));
    assert!(matches!(&view.chat[1], ChatEntry::Assistant(m) if m.blocks
        == vec![MessageBlock::Text("hi there".to_string())]));
    assert_eq!(view.session_id, "0199-sess");
    assert_eq!(view.session_name.as_deref(), Some("my session"));
    assert_eq!(view.last_event_sequence, 9);
    assert_eq!(
        view.event_generation, "g",
        "the cursor's generation reconstructs for the layout handoff's key"
    );
    assert!(
        view.cursor_present,
        "the cursor's presence reconstructs: the layout handoff keys on it"
    );
}

/// The layout handoff's cursor-presence gate (`view::handoff`): an
/// attach that omits the resume cursor reconstructs to collapsed default
/// key values (an empty generation, a zero sequence), which could alias
/// across cursor-less attaches of the same entry count -- the handoff
/// refuses to key on that shape.
#[test]
fn a_cursorless_attach_reconstructs_as_unkeyed_for_the_layout_handoff() {
    let mut attach = slim_attach();
    // The cursor rides both the snapshot block AND the attach's top-level
    // optional fields: a cursor-less attach omits it in BOTH places (the
    // snapshot's sequence is required, and collapses to zero).
    let snapshot = attach
        .get_mut("snapshot")
        .expect("the slim attach carries a snapshot")
        .as_object_mut()
        .expect("the snapshot is a map");
    snapshot.insert("lastEventSequence".to_string(), json!(0));
    snapshot.remove("lastEventCursor");
    let top = attach.as_object_mut().expect("the slim attach is a map");
    top.remove("lastEventSequence");
    top.remove("lastEventCursor");
    let data = attach_data_from_response(attach).unwrap();
    let view = reconstruct(&data).expect("reconstructs");
    assert!(!view.cursor_present, "no cursor means no handoff key");
    assert_eq!(
        view.last_event_sequence, 0,
        "the collapsed sequence the gate protects against"
    );
    assert_eq!(
        view.event_generation, "",
        "the collapsed generation the gate protects against"
    );
}

/// TS `getModelContextLabel`: the attach snapshot's state carries the
/// tray effort suffix with the model (reasoning + level), and a model
/// without reasoning reconstructs bare.
/// The attach state's model block carries the provider next to the id
/// (TS `state.model.provider`): both reconstruct, so the picker's
/// current-model match disambiguates the same id across providers
/// (prime-inference and openrouter both list `z-ai/glm-5.3`). The
/// display-string form and a provider-less object keep `None` (older
/// daemons).
#[test]
fn reconstructs_the_model_provider_alongside_the_id() {
    let mut attach = slim_attach();
    attach["snapshot"]["state"]["model"] =
        json!({ "id": "z-ai/glm-5.3", "provider": "prime-inference" });
    let data = attach_data_from_response(attach).unwrap();
    let view = reconstruct(&data).expect("reconstructs");
    assert_eq!(view.model_id.as_deref(), Some("z-ai/glm-5.3"));
    assert_eq!(view.model_provider.as_deref(), Some("prime-inference"));

    let mut attach = slim_attach();
    attach["snapshot"]["state"]["model"] = json!({ "id": "z-ai/glm-5.3" });
    let data = attach_data_from_response(attach).unwrap();
    let view = reconstruct(&data).expect("reconstructs");
    assert_eq!(view.model_id.as_deref(), Some("z-ai/glm-5.3"));
    assert_eq!(view.model_provider, None, "an object without a provider");

    let mut attach = slim_attach();
    attach["snapshot"]["state"]["model"] = json!("z-ai/glm-5.3");
    let data = attach_data_from_response(attach).unwrap();
    let view = reconstruct(&data).expect("reconstructs");
    assert_eq!(view.model_id.as_deref(), Some("z-ai/glm-5.3"));
    assert_eq!(view.model_provider, None, "the display-string form");
}

#[test]
fn reconstructs_the_tray_effort_suffix() {
    let mut attach = slim_attach();
    attach["snapshot"]["state"]["model"] = json!({
        "id": "faux-1", "provider": "faux", "reasoning": true
    });
    attach["snapshot"]["state"]["thinkingLevel"] = json!("high");
    let data = attach_data_from_response(attach.clone()).unwrap();
    let view = reconstruct(&data).expect("reconstructs");
    assert_eq!(view.model_id.as_deref(), Some("faux-1"));
    assert_eq!(
        view.thinking_suffix,
        Some("high".to_string()),
        "the attach state's level rides the reconstructed tray label"
    );
    attach["snapshot"]["state"]["model"] = json!({
        "id": "faux-plain", "provider": "faux", "reasoning": false
    });
    attach["snapshot"]["state"]["thinkingLevel"] = json!("off");
    let data = attach_data_from_response(attach).unwrap();
    let view = reconstruct(&data).expect("reconstructs");
    assert_eq!(
        view.thinking_suffix, None,
        "a model without reasoning reconstructs the bare id's label"
    );
}

#[test]
fn reconstructs_the_queue_from_session_actions() {
    let mut attach = slim_attach();
    attach["snapshot"]["state"]["sessionActions"] = json!({
        "queuedCount": 2,
        "steering": [{ "text": "turn right", "origin": { "kind": "user" } }],
        "followUps": [{ "text": "then summarize", "origin": { "kind": "user" } }],
    });
    let data = attach_data_from_response(attach).unwrap();
    let view = reconstruct(&data).expect("reconstructs");
    assert_eq!(
        view.queued,
        crate::queued::QueuedMessages {
            steering: vec![queued_item("turn right", InputOrigin::User)],
            follow_ups: vec![queued_item("then summarize", InputOrigin::User)],
            starting: None,
        },
        "an attach re-syncs the queue strip from the snapshot"
    );
}

/// One queued item.
fn queued_item(text: &str, origin: InputOrigin) -> eukhe_types::daemon::QueuedItem {
    eukhe_types::daemon::QueuedItem {
        text: text.to_string(),
        origin,
    }
}

/// The typed child-status origins ride the attach snapshot too (replay
/// parity with the live frames): the parked notices stay classified
/// across a re-attach.
#[test]
fn reconstructs_the_child_status_origins_from_session_actions() {
    let mut attach = slim_attach();
    attach["snapshot"]["state"]["sessionActions"] = json!({
        "queuedCount": 3,
        "steering": [{ "text": "turn right", "origin": { "kind": "user" } }],
        "followUps": [
            {
                "text": "[child-exited: no-reply child:lane]\n\nLast assistant text: done",
                "origin": { "kind": "report", "report": { "report": "childExited", "child": "lane", "exit": "noReply" } },
            },
            { "text": "then summarize", "origin": { "kind": "user" } },
            {
                "text": "[child-failed child:broken]\n\nboom",
                "origin": { "kind": "report", "report": { "report": "childFailed", "child": "broken" } },
            },
        ],
    });
    let data = attach_data_from_response(attach).unwrap();
    let view = reconstruct(&data).expect("reconstructs");
    let origins: Vec<&InputOrigin> = view
        .queued
        .follow_ups
        .iter()
        .map(|item| &item.origin)
        .collect();
    assert_eq!(
        origins,
        [
            &InputOrigin::Report {
                report: Report::ChildExited {
                    child: "lane".to_string(),
                    exit: ChildExit::NoReply,
                },
            },
            &InputOrigin::User,
            &InputOrigin::Report {
                report: Report::ChildFailed {
                    child: "broken".to_string(),
                    failure: None,
                },
            },
        ],
        "the attach re-sync carries the typed origins"
    );
}

/// The injected-continuation origin rides the attach snapshot too
/// (replay parity with the live frames): a re-attach keeps the
/// engine-minted continuations classified.
#[test]
fn reconstructs_the_injected_origin_from_session_actions() {
    let mut attach = slim_attach();
    attach["snapshot"]["state"]["sessionActions"] = json!({
        "queuedCount": 2,
        "steering": [],
        "followUps": [
            {
                "text": "[goal: continuation]\n\nKeep driving the goal.",
                "origin": { "kind": "goal", "context": "continuation" },
            },
            { "text": "then summarize", "origin": { "kind": "user" } },
        ],
    });
    let data = attach_data_from_response(attach).unwrap();
    let view = reconstruct(&data).expect("reconstructs");
    assert_eq!(
        view.queued.follow_ups,
        [
            queued_item(
                "[goal: continuation]\n\nKeep driving the goal.",
                InputOrigin::Goal {
                    context: eukhe_types::goal::GoalContextKind::Continuation,
                },
            ),
            queued_item("then summarize", InputOrigin::User),
        ],
        "the attach re-sync carries the injected origin"
    );
}

/// TS #2063: an attach re-sync mid-preparing keeps the picked-up
/// prompt visible too -- the snapshot's active action projects the
/// same starting row the live frames carry.
#[test]
fn reconstructs_the_starting_row_from_session_actions() {
    let mut attach = slim_attach();
    attach["snapshot"]["state"]["sessionActions"] = json!({
        "queuedCount": 0,
        "steering": [],
        "followUps": [],
        "active": {
            "kind": "turn",
            "phase": "preparing",
            "label": "queued before compaction",
        },
    });
    let data = attach_data_from_response(attach).unwrap();
    let view = reconstruct(&data).expect("reconstructs");
    assert_eq!(
        view.queued.starting,
        Some("queued before compaction".to_string()),
        "an attach re-sync keeps the preparing turn's prompt visible"
    );
}

#[test]
fn decodes_the_user_bash_event_triple() {
    // The `!command` lane (TS `runUserBash`): bash_start carries the
    // command and identity, bash_output one chunk, bash_end the
    // settled outcome -- all decoded whole-object.
    let start = event_to_update(&event(json!({
        "type": "bash_start",
        "command": "echo hi",
        "excludeFromContext": false,
    })));
    assert_eq!(
        start,
        TurnUpdate::BashStart {
            command: "echo hi".to_string(),
            exclude_from_context: false,
            run: BashRun::default(),
        }
    );
    let side_start = event_to_update(&event(json!({
        "type": "bash_start",
        "command": "echo pane",
        "excludeFromContext": true,
        "transient": true,
        "runId": "run-1",
    })));
    assert_eq!(
        side_start,
        TurnUpdate::BashStart {
            command: "echo pane".to_string(),
            exclude_from_context: true,
            run: BashRun {
                transient: true,
                run_id: Some("run-1".to_string()),
            },
        }
    );
    assert_eq!(
        event_to_update(&event(json!({ "type": "bash_output", "chunk": "hi\n" }))),
        TurnUpdate::BashOutput {
            chunk: "hi\n".to_string()
        }
    );
    assert_eq!(
        event_to_update(&event(json!({
            "type": "bash_end",
            "exitCode": 0,
            "cancelled": false,
            "output": "hi\n",
            "omitted": { "bytes": 3, "lines": 1, "at": "end" },
        }))),
        TurnUpdate::BashEnd {
            exit_code: Some(0),
            cancelled: false,
            output: "hi\n".to_string(),
            omitted: Some(eukhe_types::output::OmittedOutput {
                bytes: 3,
                lines: 1,
                at: eukhe_types::output::OmittedAt::End,
            }),
            artifact: None,
            error_message: None,
            run: BashRun::default(),
        }
    );
}

#[test]
fn decodes_session_action_update_as_the_queue_projection() {
    let update = event_to_update(&event(json!({
        "type": "session_action_update",
        "actions": {
            "queuedCount": 1,
            "steering": [],
            "followUps": [{ "text": "queued follow-up", "origin": { "kind": "user" } }],
        },
    })));
    assert_eq!(
        update,
        TurnUpdate::QueueUpdated(crate::queued::QueuedMessages {
            steering: vec![],
            follow_ups: vec![queued_item("queued follow-up", InputOrigin::User)],
            starting: None,
        })
    );
}

/// The live queue update carries the typed child-status origin: the
/// parked notices classify on the live path exactly like the attach
/// path.
#[test]
fn decodes_the_child_status_origin_from_the_live_queue_update() {
    let update = event_to_update(&event(json!({
        "type": "session_action_update",
        "actions": {
            "queuedCount": 2,
            "steering": [{
                "text": "[child-exited: no-reply child:lane]",
                "origin": { "kind": "report", "report": { "report": "childExited", "child": "lane", "exit": "noReply" } },
            }],
            "followUps": [{ "text": "then summarize", "origin": { "kind": "user" } }],
        },
    })));
    assert_eq!(
        update,
        TurnUpdate::QueueUpdated(crate::queued::QueuedMessages {
            steering: vec![queued_item(
                "[child-exited: no-reply child:lane]",
                InputOrigin::Report {
                    report: Report::ChildExited {
                        child: "lane".to_string(),
                        exit: ChildExit::NoReply,
                    },
                },
            )],
            follow_ups: vec![queued_item("then summarize", InputOrigin::User)],
            starting: None,
        })
    );
}

/// The live queue update carries the injected-continuation origin: the
/// parked continuations classify on the live path exactly like the
/// attach path.
#[test]
fn decodes_the_injected_origin_from_the_live_queue_update() {
    let update = event_to_update(&event(json!({
        "type": "session_action_update",
        "actions": {
            "queuedCount": 2,
            "steering": [],
            "followUps": [
                {
                    "text": "[goal: continuation]\n\nKeep driving the goal.",
                    "origin": { "kind": "goal", "context": "continuation" },
                },
                { "text": "then summarize", "origin": { "kind": "user" } },
            ],
        },
    })));
    assert_eq!(
        update,
        TurnUpdate::QueueUpdated(crate::queued::QueuedMessages {
            steering: Vec::new(),
            follow_ups: vec![
                queued_item(
                    "[goal: continuation]\n\nKeep driving the goal.",
                    InputOrigin::Goal {
                        context: eukhe_types::goal::GoalContextKind::Continuation,
                    },
                ),
                queued_item("then summarize", InputOrigin::User),
            ],
            starting: None,
        })
    );
}

/// TS #2063 (RES-1306): a queue update that reports a preparing turn
/// carries the picked-up prompt's label as the strip's starting row,
/// whatever the parked lanes hold; a later phase (the turn committed)
/// drops it.
#[test]
fn decodes_the_preparing_turn_label_as_the_starting_row() {
    let preparing = json!({
        "type": "session_action_update",
        "actions": {
            "queuedCount": 0,
            "steering": [],
            "followUps": [],
            "active": {
                "kind": "turn",
                "phase": "preparing",
                "label": "queued before compaction",
            },
        },
    });
    assert_eq!(
        event_to_update(&event(preparing)),
        TurnUpdate::QueueUpdated(crate::queued::QueuedMessages {
            steering: vec![],
            follow_ups: vec![],
            starting: Some("queued before compaction".to_string()),
        })
    );
    let committed = json!({
        "type": "session_action_update",
        "actions": {
            "queuedCount": 0,
            "steering": [],
            "followUps": [],
            "active": {
                "kind": "turn",
                "phase": "committing",
                "label": "queued before compaction",
            },
        },
    });
    assert_eq!(
        event_to_update(&event(committed)),
        TurnUpdate::QueueUpdated(crate::queued::QueuedMessages::default())
    );
    // An active action that is not a turn never projects a starting
    // row.
    let other_kind = json!({
        "type": "session_action_update",
        "actions": {
            "queuedCount": 0,
            "steering": [],
            "followUps": [],
            "active": {
                "kind": "session_command",
                "phase": "preparing",
                "label": "/theme dark",
            },
        },
    });
    assert_eq!(
        event_to_update(&event(other_kind)),
        TurnUpdate::QueueUpdated(crate::queued::QueuedMessages::default())
    );
}

/// The rebuild side of the single-line retry UX (operator ruling
/// 2026-09-23): the `provider_retry_outcome` row replaces the failed
/// attempts its episode superseded -- the rebuilt chat shows ONE line
/// per episode, never the per-attempt error rows TS renders.
#[test]
fn retry_outcome_row_collapses_the_superseded_attempts() {
    let user = json!({"role": "user", "content": "run the deploy"});
    let failed = |text: &str| {
        json!({
            "role": "assistant",
            "content": [],
            "stopReason": "error",
            "errorMessage": text,
        })
    };
    let outcome = json!({
        "role": "custom",
        "customType": "provider_retry_outcome",
        "content": "Recovered after 2 retries: 429 Too many concurrent requests (limit: 32)",
        "display": true,
        "details": { "success": true, "attempts": 2, "finalError": "429 Too many concurrent requests (limit: 32)" },
    });
    let recovered = json!({"role": "assistant", "content": [{"type": "text", "text": "deployed"}], "stopReason": "stop"});
    let messages = vec![
        user,
        failed("Error: 429 Too many concurrent requests (limit: 32). Try again shortly."),
        failed("Error: 429 Too many concurrent requests (limit: 32). Try again shortly."),
        outcome,
        recovered,
    ];
    let entries = transcript_to_entries(&msgs(messages));
    // Exactly: the user row, the ONE outcome line, the recovered reply.
    assert_eq!(entries.len(), 3, "entries: {entries:?}");
    assert!(matches!(
        entries[1],
        ChatEntry::Status { ref text, kind: StatusKind::Info }
            if text.contains("Recovered after 2 retries")
                && text.contains("429 Too many concurrent requests")
    ));
    // Zero superseded attempt rows survive.
    assert!(
        entries
            .iter()
            .all(|entry| !is_superseded_attempt_row(entry)),
        "per-attempt rows must collapse: {entries:?}"
    );
}

/// Without an outcome row the failure is not an episode: the lone
/// error row keeps today's rendering (retries disabled or a
/// non-retryable kind).
#[test]
fn a_lone_failed_attempt_without_an_outcome_row_stays() {
    let user = json!({"role": "user", "content": "hi"});
    let failed = json!({
        "role": "assistant",
        "content": [],
        "stopReason": "error",
        "errorMessage": "401 Unauthorized",
    });
    let entries = transcript_to_entries(&msgs([user, failed]));
    assert_eq!(entries.len(), 2, "entries: {entries:?}");
    assert!(
        entries.iter().any(is_superseded_attempt_row),
        "the lone failure renders its own row: {entries:?}"
    );
}

/// Aborted attempts are never collateral of the collapse.
#[test]
fn aborted_attempts_never_collapse() {
    let user = json!({"role": "user", "content": "hi"});
    let aborted = json!({
        "role": "assistant",
        "content": [],
        "stopReason": "aborted",
        "errorMessage": "Operation aborted",
    });
    let outcome = json!({
        "role": "custom",
        "customType": "provider_retry_outcome",
        "content": "\u{26a0} Error: Retry failed after 1 attempts: Retry cancelled",
        "display": true,
        "details": { "success": false, "attempts": 1, "finalError": "Retry cancelled" },
    });
    let entries = transcript_to_entries(&msgs([user, aborted, outcome]));
    assert_eq!(entries.len(), 3, "the abort row stays: {entries:?}");
    assert!(
        entries
            .iter()
            .any(|entry| matches!(entry, ChatEntry::Assistant(assistant) if assistant.aborted)),
        "the abort renders: {entries:?}"
    );
}

#[test]
fn decodes_auto_retry_events() {
    let start = event_to_update(&event(json!({
        "type": "auto_retry_start",
        "attempt": 1,
        "maxAttempts": 2,
        "delayMs": 50,
        "errorMessage": "provider down",
    })));
    assert_eq!(
        start,
        TurnUpdate::AutoRetryStart {
            attempt: 1,
            max_attempts: Some(2),
            delay_ms: 50,
            error_message: "provider down".to_string(),
            reason: RetryStartReason::Quick,
        }
    );
    let backup = event_to_update(&event(json!({
        "type": "auto_retry_start",
        "attempt": 3,
        "maxAttempts": 5,
        "delayMs": 0,
        "errorMessage": "provider down",
        "reason": "backup",
        "backupModel": "prime-inference/glm-5.3",
    })));
    assert_eq!(
        backup,
        TurnUpdate::AutoRetryStart {
            attempt: 3,
            max_attempts: Some(5),
            delay_ms: 0,
            error_message: "provider down".to_string(),
            reason: RetryStartReason::Backup {
                backup_model: "prime-inference/glm-5.3".to_string()
            },
        }
    );
    let end = event_to_update(&event(json!({
        "type": "auto_retry_end",
        "success": false,
        "attempt": 2,
        "finalError": "provider down",
    })));
    assert_eq!(
        end,
        TurnUpdate::AutoRetryEnd {
            success: false,
            attempt: 2,
            final_error: Some("provider down".to_string()),
            restored_model: None,
        }
    );
    let settled = event_to_update(&event(json!({
        "type": "auto_retry_end",
        "success": true,
        "attempt": 2,
        "restoredModel": "prime-inference/glm-5.3",
    })));
    assert_eq!(
        settled,
        TurnUpdate::AutoRetryEnd {
            success: true,
            attempt: 2,
            final_error: None,
            restored_model: Some("prime-inference/glm-5.3".to_string()),
        }
    );
}

/// The python-kernel bootstrap's `starting` partials carry the loader
/// note (the same stage text TS hands `setWorkingMessage`); streamed
/// `ok` output and non-text payloads do not.
#[test]
fn loader_note_comes_from_starting_partials_only() {
    let booting = json!({
        "content": [
            { "type": "text", "text": "\u{203a} setting up python kernel (one-time, ~30s)\u{2026}" }
        ],
        "details": { "status": "starting" },
    });
    assert_eq!(
        working_message_from_update(&wire(booting)).as_deref(),
        Some("\u{203a} setting up python kernel (one-time, ~30s)\u{2026}")
    );
    let streamed = json!({
        "content": [{ "type": "text", "text": "visual parity ok" }],
        "details": { "status": "ok" },
    });
    assert_eq!(working_message_from_update(&wire(streamed)), None);
    let no_text = json!({
        "content": [],
        "details": { "status": "starting" },
    });
    assert_eq!(working_message_from_update(&wire(no_text)), None);
}

#[test]
fn failed_assistant_message_end_maps_final() {
    let update = event_to_update(&event(json!({
        "type": "message_end",
        "message": {
            "role": "assistant",
            "stopReason": "error",
            "errorMessage": "Provider server error",
            "content": [],
        },
    })));
    match update {
        TurnUpdate::AssistantMessage {
            streaming, message, ..
        } => {
            assert!(!streaming, "message_end is final");
            assert_eq!(message.stop_reason, eukhe_types::ai::StopReason::Error);
        }
        other => panic!("unexpected update: {other:?}"),
    }
}

#[test]
fn decodes_block_content() {
    let items = message_value_to_entries(&msg(json!({
        "role": "user",
        "content": [{ "text": "hello " }, { "text": "world" }],
    })));
    assert_eq!(
        items,
        vec![ChatEntry::User {
            text: "hello world".to_string()
        }]
    );
    let items = message_value_to_entries(&msg(json!({
        "role": "assistant",
        "content": [
            { "type": "thinking", "thinking": "hmm" },
            { "type": "text", "text": "working" },
            { "type": "toolCall", "id": "t1", "name": "bash", "arguments": { "command": "ls" } },
        ],
    })));
    assert_eq!(items.len(), 2);
    assert!(matches!(
        &items[0],
        ChatEntry::Assistant(m) if m.blocks.len() == 2 && m.has_tool_calls
    ));
    assert!(matches!(&items[1], ChatEntry::Tool(card) if card.name == "bash"));
}

#[test]
fn decodes_streamed_events() {
    let user = event_to_update(&event(json!({
        "type": "message_start",
        "message": { "role": "user", "content": "go" },
    })));
    assert_eq!(user, TurnUpdate::UserMessage("go".to_string()));
    let partial = event_to_update(&event(json!({
        "type": "message_update",
        "message": { "role": "assistant", "content": [{ "type": "text", "text": "work" }] },
        "assistantMessageEvent": { "type": "text_delta", "delta": "work" },
    })));
    assert!(matches!(
        &partial,
        TurnUpdate::AssistantMessage { message, streaming: true, .. }
            if assistant_text(message) == "work"
    ));
    let final_message = event_to_update(&event(json!({
        "type": "message_end",
        "message": { "role": "assistant", "content": [{ "type": "text", "text": "done" }] },
    })));
    assert!(matches!(
        &final_message,
        TurnUpdate::AssistantMessage { message, streaming: false, .. }
            if assistant_text(message) == "done"
    ));
    let ended = event_to_update(&event(json!({ "type": "turn_end" })));
    assert_eq!(
        ended,
        TurnUpdate::TurnEnded {
            outcome: crate::snapshot::TurnOutcome::Unreported
        }
    );
    let failed = event_to_update(&event(json!({ "type": "turn_end", "error": "boom" })));
    assert_eq!(
        failed,
        TurnUpdate::TurnEnded {
            outcome: crate::snapshot::TurnOutcome::Failed("boom".to_string())
        }
    );
    assert_eq!(
        event_to_update(&event(json!({ "type": "agent_end", "messages": [] }))),
        TurnUpdate::Idle
    );
}

/// The concatenated text blocks of an assistant message.
fn assistant_text(message: &eukhe_types::ai::AssistantMessage) -> String {
    message
        .content
        .iter()
        .filter_map(|block| match block {
            eukhe_types::ai::AssistantContentBlock::Text(text) => Some(text.text.as_str()),
            _ => None,
        })
        .collect()
}

#[test]
fn session_command_rows_decode_once() {
    let echo = json!({
        "type": "message_start",
        "message": {
            "role": "custom",
            "customType": "session_slash_command",
            "content": "/goal ship it",
            "display": true,
            "details": { "command": { "name": "goal", "args": "ship it", "text": "/goal ship it" } },
        },
    });
    assert_eq!(
        event_to_update(&event(echo.clone())),
        TurnUpdate::CustomRow(ChatEntry::SlashCommand {
            text: "/goal ship it".to_string()
        })
    );
    // The closing frame of the pair must not duplicate the row.
    let end = json!({
        "type": "message_end",
        "message": echo["message"].clone(),
    });
    assert_eq!(event_to_update(&event(end)), TurnUpdate::StatusUpdate);

    let result = json!({
        "type": "message_start",
        "message": {
            "role": "custom",
            "customType": "session_slash_command_result",
            "content": "Goal active: ship it",
            "display": true,
            "details": {
                "command": { "name": "goal", "args": "ship it", "text": "/goal ship it" },
                "success": true, "severity": "info",
            },
        },
    });
    // The outcome row decodes as a system status row, never a user
    // block (the operator's 2026-09-25 ruling: command output is not
    // user text).
    assert_eq!(
        event_to_update(&event(result)),
        TurnUpdate::CustomRow(ChatEntry::Status {
            text: "Goal active: ship it".to_string(),
            kind: StatusKind::Info
        })
    );
    // A failed command's outcome row carries the error tone.
    let failed = json!({
        "type": "message_start",
        "message": {
            "role": "custom",
            "customType": "session_slash_command_result",
            "content": "Command failed: boom",
            "display": true,
            "details": {
                "command": { "name": "goal", "args": "clear", "text": "/goal clear" },
                "success": false, "severity": "error",
            },
        },
    });
    assert_eq!(
        event_to_update(&event(failed)),
        TurnUpdate::CustomRow(ChatEntry::Status {
            text: "Command failed: boom".to_string(),
            kind: StatusKind::Error
        })
    );
}

#[test]
fn session_command_rows_respect_display_and_shape() {
    // Non-display rows (the refine result) render nothing.
    let hidden = json!({
        "role": "custom",
        "customType": "session_slash_command_result",
        "content": "Refined continual harness state: 1 edit applied.",
        "display": false,
    });
    assert!(message_value_to_entries(&msg(hidden)).is_empty());
    // A displayed outcome row renders in the status-row class with
    // the severity's tone (the operator's 2026-09-25 ruling: command
    // output is system output, never user text).
    let outcome = json!({
        "role": "custom",
        "customType": "session_slash_command_result",
        "content": "Goal cleared.",
        "display": true,
        "details": {
            "command": { "name": "goal", "args": "clear", "text": "/goal clear" },
            "success": true, "severity": "info",
        },
    });
    assert_eq!(
        message_value_to_entries(&msg(outcome)),
        vec![ChatEntry::Status {
            text: "Goal cleared.".to_string(),
            kind: StatusKind::Info,
        }]
    );
    // Unknown displayed custom types render the generic box (the TS
    // live dispatch fallthrough; harness digests persist with
    // display=false and render nothing).
    let other = json!({
        "role": "custom",
        "customType": "harness_digest",
        "content": "digest",
        "display": true,
    });
    assert!(matches!(
        message_value_to_entries(&msg(other)).as_slice(),
        [ChatEntry::CustomPanel(_)]
    ));
    // A command row without command details renders the malformed
    // notice (TS `isSessionSlashCommandMessage` fallback).
    let malformed = json!({
        "role": "custom",
        "customType": "session_slash_command",
        "content": "/goal",
        "display": true,
        "details": {},
    });
    assert_eq!(
        message_value_to_entries(&msg(malformed)),
        vec![ChatEntry::User {
            text: "[Malformed session command message]".to_string()
        }]
    );
}

/// A transcript with tool calls replays the way the TS attach does: the
/// assistant's tool card stays pending until the matching
/// `role: "toolResult"` message completes it; orphan results render
/// nothing.
#[test]
fn transcript_replay_completes_tool_cards() {
    let transcript = [
        json!({ "role": "user", "content": "run it", "timestamp": 1 }),
        json!({
            "role": "assistant",
            "content": [
                { "type": "text", "text": "calling" },
                { "type": "toolCall", "id": "call-1", "name": "ipython", "arguments": {"code": "1"} },
            ],
            "provider": "faux", "model": "faux-1",
            "usage": { "input": 10, "output": 2 }, "stopReason": "toolUse",
            "timestamp": 2,
        }),
        json!({
            "role": "toolResult",
            "toolCallId": "call-1",
            "toolName": "ipython",
            "content": [{ "type": "text", "text": "42" }],
            "details": { "durationMs": 3, "status": "ok" },
            "isError": false,
            "timestamp": 3,
        }),
        json!({
            "role": "toolResult",
            "toolCallId": "orphan",
            "toolName": "ipython",
            "content": [{ "type": "text", "text": "no card" }],
            "isError": false,
            "timestamp": 4,
        }),
        json!({
            "role": "assistant",
            "content": [{ "type": "text", "text": "done" }],
            "provider": "faux", "model": "faux-1",
            "usage": { "input": 10, "output": 2 }, "stopReason": "stop",
            "timestamp": 5,
        }),
    ];
    let chat = transcript_to_entries(&msgs(transcript));
    // user row, assistant text, tool card, final assistant text -
    // and the orphan result keeps its standalone card (the live
    // push path's twin; the rebuilt transcript never drops it).
    assert_eq!(chat.len(), 5, "chat: {chat:?}");
    let Some(ChatEntry::Tool(card)) = chat.get(2) else {
        panic!("tool card at index 2: {chat:?}");
    };
    assert!(card.started);
    assert!(!card.result_partial);
    let result = card.result.as_ref().expect("result replayed");
    assert_eq!(
        result.content,
        vec![json!({ "type": "text", "text": "42" })]
    );
    assert_eq!(result.details, json!({ "durationMs": 3, "status": "ok" }));
    assert!(!result.is_error);
    let Some(ChatEntry::Tool(orphan)) = chat.get(3) else {
        panic!("orphan card at its wire position (index 3): {chat:?}");
    };
    assert_eq!(orphan.id, "orphan");
    assert!(orphan.result.is_some(), "the orphan keeps its own card");
}

/// A pending card (result absent) replays with no result, like a turn
/// still in flight when the session was last persisted.
#[test]
fn transcript_replay_keeps_pending_cards_without_results() {
    let transcript = [
        json!({ "role": "user", "content": "run it", "timestamp": 1 }),
        json!({
            "role": "assistant",
            "content": [
                { "type": "toolCall", "id": "call-1", "name": "ipython", "arguments": {} },
            ],
            "provider": "faux", "model": "faux-1",
            "usage": { "input": 10, "output": 2 }, "stopReason": "toolUse",
            "timestamp": 2,
        }),
    ];
    let chat = transcript_to_entries(&msgs(transcript));
    let Some(ChatEntry::Tool(card)) = chat.get(1) else {
        panic!("tool card at index 1: {chat:?}");
    };
    assert!(!card.started);
    assert!(card.result.is_none());
}

/// `Reconstructed::push_message` folds a late `toolResult` message onto
/// the card an earlier chunk added (streamed snapshot reassembly).
#[test]
fn push_message_completes_pending_tool_card() {
    let mut reconstructed = Reconstructed::default();
    reconstructed.push_message(&msg(json!({
        "role": "assistant",
        "content": [
            { "type": "toolCall", "id": "call-1", "name": "ipython", "arguments": {} },
        ],
        "provider": "faux", "model": "faux-1",
        "usage": { "input": 10, "output": 2 }, "stopReason": "toolUse",
        "timestamp": 2,
    })));
    reconstructed.push_message(&msg(json!({
        "role": "toolResult",
        "toolCallId": "call-1",
        "toolName": "ipython",
        "content": [{ "type": "text", "text": "out" }],
        "isError": true,
        "timestamp": 3,
    })));
    assert_eq!(reconstructed.chat.len(), 1);
    let Some(ChatEntry::Tool(card)) = reconstructed.chat.first() else {
        panic!("single tool card: {:?}", reconstructed.chat);
    };
    let result = card.result.as_ref().expect("result applied");
    assert!(result.is_error);
    assert_eq!(
        result.content,
        vec![json!({ "type": "text", "text": "out" })]
    );
}

/// A provider-failure turn replays like the TS transcript: the healthy
/// exchange renders once, and every failed retry attempt folds into its
/// own error row (TS `buildConversationComponents` pushes one component
/// per assistant message, even a content-less failure).
#[test]
fn transcript_replay_stacks_provider_failure_rows() {
    let failed_attempt = |timestamp: u64| {
        json!({
            "role": "assistant",
            "content": [],
            "provider": "prime-inference", "model": "mock-1",
            "stopReason": "error",
            "errorMessage": "Connection error.",
            "timestamp": timestamp,
        })
    };
    let transcript = [
        json!({ "role": "user", "content": "hello", "timestamp": 1 }),
        json!({
            "role": "assistant",
            "content": [{ "type": "text", "text": "battery hello from mock" }],
            "provider": "prime-inference", "model": "mock-1",
            "usage": { "input": 10, "output": 2 }, "stopReason": "stop",
            "timestamp": 2,
        }),
        json!({ "role": "user", "content": "again", "timestamp": 3 }),
        failed_attempt(4),
        failed_attempt(5),
        failed_attempt(6),
    ];
    let chat = transcript_to_entries(&msgs(transcript));
    // One user + reply, one user, then one entry per failed attempt.
    assert_eq!(chat.len(), 6, "chat: {chat:?}");
    let replies: Vec<&crate::chat::AssistantMessage> = chat
        .iter()
        .filter_map(|entry| match entry {
            ChatEntry::Assistant(message) => Some(message.as_ref()),
            _ => None,
        })
        .collect();
    assert_eq!(replies.len(), 4);
    assert_eq!(
        replies[0].blocks,
        vec![MessageBlock::Text("battery hello from mock".to_string())]
    );
    assert!(replies[0].error.is_none(), "the healthy reply stays clean");
    for row in &replies[1..] {
        assert!(row.blocks.is_empty());
        assert_eq!(
            row.error.as_deref(),
            Some("Error: Connection error."),
            "each failed attempt stacks its own error row"
        );
        assert!(!row.aborted);
    }
}

/// An aborted assistant message folds into its abort row even when the
/// message streamed no content (TS renders the abort row always).
#[test]
fn transcript_replay_renders_contentless_abort() {
    let transcript = [
        json!({ "role": "user", "content": "hello", "timestamp": 1 }),
        json!({
            "role": "assistant",
            "content": [],
            "provider": "faux", "model": "faux-1",
            "stopReason": "aborted",
            "timestamp": 2,
        }),
    ];
    let chat = transcript_to_entries(&msgs(transcript));
    assert_eq!(chat.len(), 2, "chat: {chat:?}");
    let Some(ChatEntry::Assistant(message)) = chat.get(1) else {
        panic!("abort row: {chat:?}");
    };
    assert!(message.blocks.is_empty());
    assert_eq!(message.error.as_deref(), Some("Operation aborted"));
    assert!(message.aborted);
}

#[test]
fn decodes_compaction_events() {
    // The start pair (TS `AgentSession.compact` event).
    assert_eq!(
        event_to_update(&event(json!({
            "type": "compaction_start",
            "reason": "manual",
            "customInstructions": "focus on the goal",
        }))),
        TurnUpdate::CompactionStart {
            reason: CompactionReason::Manual,
            custom_instructions: Some("focus on the goal".to_string()),
        }
    );
    assert_eq!(
        event_to_update(&event(
            json!({ "type": "compaction_start", "reason": "manual" })
        )),
        TurnUpdate::CompactionStart {
            reason: CompactionReason::Manual,
            custom_instructions: None,
        }
    );
    // Success carries the client-facing result.
    assert_eq!(
        event_to_update(&event(json!({
            "type": "compaction_end",
            "reason": "manual",
            "result": { "summary": "s", "firstKeptEntryId": "e1", "tokensBefore": 12 },
            "aborted": false,
            "willRetry": false,
            "customInstructions": "focus",
        }))),
        TurnUpdate::CompactionEnd {
            reason: CompactionReason::Manual,
            result: Some(CompactionResult {
                summary: "s".to_string(),
                first_kept_entry_id: Some("e1".to_string()),
                tokens_before: 12,
            }),
            custom_instructions: Some("focus".to_string()),
            aborted: false,
            error_message: None,
            error_severity: None,
        }
    );
    // A skip carries the warning message; the result stays absent.
    assert_eq!(
        event_to_update(&event(json!({
            "type": "compaction_end",
            "reason": "manual",
            "aborted": false,
            "willRetry": false,
            "errorMessage": "Session is too short to compact",
            "errorSeverity": "warning",
        }))),
        TurnUpdate::CompactionEnd {
            reason: CompactionReason::Manual,
            result: None,
            custom_instructions: None,
            aborted: false,
            error_message: Some("Session is too short to compact".to_string()),
            error_severity: Some(ErrorSeverity::Warning),
        }
    );
    // A summary delta carries its text chunk verbatim (the live
    // streamed block's input; the settling end stays the summary's
    // only durable source).
    assert_eq!(
        event_to_update(&event(json!({
            "type": "compaction_summary_delta",
            "delta": "The session covered the goal.",
        }))),
        TurnUpdate::CompactionSummaryDelta {
            delta: "The session covered the goal.".to_string(),
        }
    );
}

#[test]
fn transcript_replay_renders_the_compaction_outcome_row() {
    // A skipped auto-compaction warns (TS `CompactionOutcomeMessageComponent`).
    let items = message_value_to_entries(&msg(json!({
        "role": "custom",
        "customType": "compaction_outcome",
        "content": "Auto-compaction skipped: not enough context",
        "display": true,
        "details": { "reason": "threshold", "outcome": "skipped" },
    })));
    assert_eq!(
        items,
        vec![ChatEntry::Status {
            text: "Auto-compaction skipped: not enough context".to_string(),
            kind: StatusKind::Warning,
        }]
    );
    // A failed overflow recovery errors.
    let items = message_value_to_entries(&msg(json!({
        "role": "custom",
        "customType": "compaction_outcome",
        "content": "Context overflow recovery failed: boom",
        "display": true,
        "details": { "reason": "overflow", "outcome": "failed" },
    })));
    assert!(matches!(
        &items[0],
        ChatEntry::Status { kind: StatusKind::Error, text }
            if text == "Context overflow recovery failed: boom"
    ));
    // A cancelled compaction errors too (TS: only `skipped` warns).
    let items = message_value_to_entries(&msg(json!({
        "role": "custom",
        "customType": "compaction_outcome",
        "content": "Compaction cancelled",
        "display": true,
        "details": { "reason": "threshold", "outcome": "cancelled" },
    })));
    assert!(matches!(
        &items[0],
        ChatEntry::Status { kind: StatusKind::Error, text }
            if text == "Compaction cancelled"
    ));
    // An envelope TS `isCompactionOutcomeMessage` rejects renders the
    // malformed notice (invalid reason and outcome both).
    for details in [
        json!({ "reason": "manual", "outcome": "skipped" }),
        json!({ "reason": "threshold", "outcome": "compacted" }),
        json!({}),
    ] {
        let items = message_value_to_entries(&msg(json!({
            "role": "custom",
            "customType": "compaction_outcome",
            "content": "text",
            "display": true,
            "details": details,
        })));
        assert_eq!(
            items,
            vec![ChatEntry::Status {
                text: "[Malformed compaction outcome message]".to_string(),
                kind: StatusKind::Error,
            }]
        );
    }
}

#[test]
fn transcript_replay_renders_the_compaction_summary() {
    // The attach snapshot's `role: "compactionSummary"` message (the
    // session store's fold) renders the summary row with its fields.
    let items = message_value_to_entries(&msg(json!({
        "role": "compactionSummary",
        "summary": "the story so far",
        "tokensBefore": 1234,
        "retainedMessageCount": 2,
        "customInstructions": "tests",
        "timestamp": 1,
    })));
    assert_eq!(items.len(), 1);
    assert!(matches!(
        &items[0],
        ChatEntry::CompactionSummary { summary, tokens_before, custom_instructions }
        if summary == "the story so far"
            && *tokens_before == 1234
            && custom_instructions.as_deref() == Some("tests")
    ));
}

/// A settled content-less assistant message renders nothing (TS: the
/// component's rows are empty and spacing stays `hidden`).
#[test]
fn transcript_replay_skips_contentless_settled_messages() {
    let items = message_value_to_entries(&msg(json!({
        "role": "assistant",
        "content": [],
        "stopReason": "stop",
    })));
    assert_eq!(items, Vec::new());
    // A provider error beside tool calls renders no message row either:
    // the cards carry the failure.
    let items = message_value_to_entries(&msg(json!({
        "role": "assistant",
        "content": [
            { "type": "toolCall", "id": "t1", "name": "bash", "arguments": { "command": "ls" } },
        ],
        "stopReason": "error",
        "errorMessage": "Connection error.",
    })));
    assert_eq!(items.len(), 1);
    assert!(matches!(&items[0], ChatEntry::Tool(card) if card.name == "bash"));
}

/// A `goal_update` event decodes to the wire goal payload (the session
/// view owns announcement and tray rendering).
#[test]
fn goal_update_decodes_the_goal_payload() {
    let update = event_to_update(&event(json!({
        "type": "goal_update",
        "goal": {
            "active": false,
            "status": "complete",
            "goalId": "g-1",
            "objective": "ship it",
            "tokensUsed": 120,
            "timeUsedSeconds": 3,
            "continuationsUsed": 2,
            "lastReason": "Goal achieved"
        }
    })));
    let TurnUpdate::GoalUpdate(goal) = update else {
        panic!("expected a goal update");
    };
    assert_eq!(goal.status, eukhe_types::goal::GoalStatus::Complete);
    assert_eq!(goal.objective.as_deref(), Some("ship it"));
    assert_eq!(goal.last_reason.as_deref(), Some("Goal achieved"));
}

/// The attach snapshot's `state.goal` rehydrates with the session (TS
/// `snapshot.ts: goal: session.goalState`); a null goal stays absent.
#[test]
fn attach_snapshot_carries_the_goal_state() {
    let attach = json!({
        "protocol": { "name": "eukhe.daemon", "version": 7 },
        "activeSessionId": "abc123def456",
        "snapshot": {
            "activeSessionId": "abc123def456",
            "summary": { "id": "abc123def456", "cwd": "/tmp" },
            "state": {
                "activeSessionId": "abc123def456",
                "cwd": "/tmp",
                "sessionId": "0199-sess",
                "model": null,
                "thinkingLevel": "default",
                "serviceTier": "auto",
                "isStreaming": false,
                "isCompacting": false,
                "retryAttempt": 0,
                "steeringMode": "all",
                "followUpMode": "all",
                "autoCompactionEnabled": false,
                "messageCount": 0,
                "sessionActions": { "queuedCount": 0, "steering": [], "followUps": [] },
                "compactionCount": 0,
                "goal": {
                    "active": true,
                    "status": "active",
                    "objective": "keep shipping",
                    "tokensUsed": 10,
                    "timeUsedSeconds": 1,
                    "continuationsUsed": 0
                },
                "scopedModels": [],
                "activeToolNames": []
            },
            "messages": [],
            "lastEventSequence": 3,
            "lastEventCursor": { "generation": "g-1", "sequence": 3 }
        },
        "lastEventSequence": 3
    });
    let data = attach_data_from_response(attach).unwrap();
    let reconstructed = reconstruct(&data).expect("reconstructs");
    let goal = reconstructed.goal.expect("snapshot goal");
    assert_eq!(goal.status, eukhe_types::goal::GoalStatus::Active);
    assert_eq!(goal.objective.as_deref(), Some("keep shipping"));
}

/// The tray's context usage rides the attach snapshot's state: the
/// reconstruct hands it to the rebuild that follows every attach.
#[test]
fn attach_snapshot_carries_the_tray_context_usage() {
    let mut attach = slim_attach();
    attach["snapshot"]["state"]["contextUsage"] =
        json!({ "tokens": 9_400, "contextWindow": 128_000, "percent": 7.34 });
    let data = attach_data_from_response(attach).unwrap();
    let usage = reconstruct(&data)
        .expect("reconstructs")
        .context_usage
        .expect("snapshot context usage");
    assert_eq!(usage.tokens, 9_400);
    assert_eq!(usage.context_window, 128_000);

    // Unknown tokens (a fresh compaction) clear the tray display.
    let mut attach = slim_attach();
    attach["snapshot"]["state"]["contextUsage"] =
        json!({ "tokens": null, "contextWindow": 128_000, "percent": null });
    let data = attach_data_from_response(attach).unwrap();
    assert_eq!(
        reconstruct(&data).expect("reconstructs").context_usage,
        None
    );

    // A state without the field (a model-less session) stays `None`.
    let data = attach_data_from_response(slim_attach()).unwrap();
    assert_eq!(
        reconstruct(&data).expect("reconstructs").context_usage,
        None
    );
}

/// The synthetic image-heavy tool-result row: a `role: "toolResult"`
/// message with one 500KB image payload block (the `attach_image` emit's
/// stored shape).
fn image_heavy_tool_result(payload: &str) -> serde_json::Value {
    json!({
        "role": "toolResult",
        "toolCallId": "call-img",
        "toolName": "ipython",
        "content": [
            { "type": "text", "text": "Loaded 1 image(s) into context: /tmp/shot.png" },
            { "type": "image", "data": payload, "mimeType": "image/png" }
        ],
        "details": { "status": "ok" },
        "isError": false,
        "timestamp": 10u64
    })
}

fn elided_image_tool_result(elided_bytes: u64, width: u64, height: u64) -> serde_json::Value {
    json!({
        "role": "toolResult",
        "toolCallId": "call-img",
        "toolName": "ipython",
        "content": [
            { "type": "text", "text": "Loaded 1 image(s) into context: /tmp/shot.png" },
            {
                "type": "image",
                "data": "",
                "mimeType": "image/png",
                "elidedBytes": elided_bytes,
                "widthPx": width,
                "heightPx": height
            }
        ],
        "details": { "status": "ok" },
        "isError": false,
        "timestamp": 10u64
    })
}

/// One row's joined span text.
fn line_text(line: &crate::Line) -> String {
    line.iter().map(|span| span.content.as_str()).collect()
}

#[test]
fn an_image_heavy_transcript_replays_and_renders_its_first_frame() {
    // The synthetic image-heavy fixture: a transcript whose tail carries
    // many half-megabyte image tool results. The first-frame fold and the
    // collapsed-detail layout must complete without any payload
    // processing, and the expanded card renders the payload's
    // placeholder, never its bytes.
    let payload = "A".repeat(500 * 1024);
    let mut messages = Vec::new();
    for index in 0..16 {
        messages.push(json!({
            "role": "user", "content": format!("turn {index}"), "timestamp": index
        }));
        let mut result = image_heavy_tool_result(&payload);
        result["toolCallId"] = json!(format!("call-img-{index}"));
        messages.push(result);
    }
    let entries = transcript_to_entries(&msgs(messages));
    assert_eq!(entries.len(), 32, "a user row and a card per turn");

    // The first-frame geometry pass over the whole transcript completes.
    let mut view = test_view();
    for entry in entries {
        view.push_entry(entry);
    }
    // The whole transcript renders, and its rows carry no payload bytes.
    let rows = view.render_transcript(100);
    assert!(rows.len() > 40, "the transcript frame renders");
    let flat: Vec<String> = rows.iter().map(line_text).collect();
    assert!(
        flat.iter().all(|row| !row.contains(&"A".repeat(64))),
        "no payload bytes reach the frame: {flat:?}"
    );
}

#[test]
fn elided_image_tool_results_render_their_marker_metadata() {
    // The elision marker the daemon's attach snapshot writes for an
    // `elide_snapshot_images` client: the fold keeps the card, and the
    // expanded card renders the marker's dimensions -- the same row the
    // payload's own metadata produced.
    let entries = transcript_to_entries(&msgs([elided_image_tool_result(500 * 1024, 64, 32)]));
    let card = entries
        .iter()
        .find_map(|entry| match entry {
            ChatEntry::Tool(card) => Some(card.as_ref()),
            _ => None,
        })
        .expect("the tool card");
    let rows = crate::tool_card::render_tool_card(
        card,
        0,
        crate::chat::Detail::All,
        &crate::theme::Theme::builtin("eukhe", crate::theme::ColorMode::TrueColor),
        100,
        true,
    );
    let flat: Vec<String> = rows.iter().map(line_text).collect();
    assert!(
        flat.iter()
            .any(|row| row.contains("`- [image/png - 64x32]")),
        "the marker's dimensions render: {flat:?}"
    );
    // The hidden form renders the same metadata with its size.
    assert_eq!(
        card.result.as_ref().unwrap().text_output(false),
        "Loaded 1 image(s) into context: /tmp/shot.png\n[Image: [image/png]]"
    );
}

/// The thinking-channel render pins (the two provider envelopes' stored
/// row shapes) live in their own child module with this file's harness.
mod thinking_pins;

/// The tool-card folds (streamed naming, the failed-frame sweep, replay
/// pairing) live in their own child module with this file's harness.
mod tool_cards;
