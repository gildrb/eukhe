//! Stored calls replayed in the current dialect: the context of an old
//! transcript through the compiled core's lift table, and the placement of
//! a lift's arguments.

use eukhe_ai::providers::faux::{
    faux_assistant_message, faux_tool_call, FauxAssistantMessageOptions,
};
use eukhe_bend::rules::call_lift::Arg;
use eukhe_types::pi_ai::{
    AssistantMessage, JsonObject, JsonValue, Message, StopReason, TextContent, ToolResultMessage,
    UserContent, UserContentBlock, UserMessage,
};
use serde_json::json;

use super::{place, PlaceError};
use crate::harness::context::{derive_view, order_tool_results};
use crate::types::{ConversationId, EntryId, EntryRecord};

fn object(value: JsonValue) -> JsonObject {
    let JsonValue::Object(object) = value else {
        panic!("the test value must be a JSON object")
    };
    object
}

fn entry(id: u64, model: Message) -> EntryRecord {
    EntryRecord {
        model: Some(vec![model]),
        data: None,
        edits: None,
        kind: "pi.message".to_owned(),
        id: EntryId::from_number(id),
        conversation_id: ConversationId::from_number(1),
        head: None,
        by_task_id: None,
    }
}

fn user(text: &str) -> Message {
    Message::User(UserMessage {
        content: UserContent::Text(text.to_owned()),
        timestamp: 0,
    })
}

/// One assistant answer calling `(name, id, arguments)` in order.
fn calling(calls: &[(&str, &str, &JsonValue)]) -> Message {
    let blocks: Vec<_> = calls
        .iter()
        .map(|(name, id, arguments)| {
            faux_tool_call(*name, object((*arguments).clone()), Some((*id).to_owned()))
        })
        .collect();
    Message::Assistant(AssistantMessage {
        stop_reason: StopReason::ToolUse,
        timestamp: 0,
        ..faux_assistant_message(blocks, FauxAssistantMessageOptions::default())
    })
}

fn result(id: &str, name: &str, details: &JsonValue) -> Message {
    Message::ToolResult(ToolResultMessage {
        tool_call_id: id.to_owned(),
        tool_name: name.to_owned(),
        content: vec![UserContentBlock::Text(TextContent::new("ok"))],
        details: Some(details.clone()),
        usage: None,
        nested_calls: None,
        is_error: false,
        timestamp: 0,
        duration_ms: None,
    })
}

/// A transcript stored before 9695afec6 (zoom@1), with a current edit
/// call, an MCP call (a family the table lacks), and a zoom rev that never
/// existed.
fn old_transcript() -> (
    Vec<EntryRecord>,
    Vec<(&'static str, &'static str, JsonValue)>,
) {
    let calls = vec![
        ("zoom", "z1", json!({ "i": "open line", "id": 3, "n": 2 })),
        (
            "edit",
            "e1",
            json!({ "i": "fix", "input": "[a.rs#AB12]\nCUT 1" }),
        ),
        ("mcp__docs__search", "m1", json!({ "q": "lift" })),
        ("zoom", "z0", json!({ "id": 1 })),
    ];
    let refs: Vec<_> = calls.iter().map(|(n, i, a)| (*n, *i, a)).collect();
    let entries = vec![
        entry(1, user("look at line 3")),
        entry(2, calling(&refs)),
        entry(3, result("z1", "zoom", &json!({ "version": "zoom@1" }))),
        entry(4, result("e1", "edit", &json!({ "version": "edit@hl.1" }))),
        entry(
            5,
            result("m1", "mcp__docs__search", &json!({ "version": "mcp@1" })),
        ),
        entry(6, result("z0", "zoom", &json!({ "version": "zoom@0" }))),
    ];
    (entries, calls)
}

/// The zoom@1 call replays as a zoom@2 call (its arguments are a zoom@2
/// call's as stored) with its receipt; the current call and the foreign
/// one are untouched; the stranded one replays as stored, with its
/// receipt.
#[test]
fn an_old_transcript_replays_in_the_current_dialect() {
    let (entries, calls) = old_transcript();
    let refs: Vec<_> = calls.iter().map(|(n, i, a)| (*n, *i, a)).collect();
    assert_eq!(
        derive_view(&entries).messages,
        vec![
            user("look at line 3"),
            calling(&refs),
            result(
                "z1",
                "zoom",
                &json!({
                    "version": "zoom@2",
                    "lift": { "from": "zoom@1", "outcome": "lifted", "receipts": [] },
                })
            ),
            result("e1", "edit", &json!({ "version": "edit@hl.1" })),
            result("m1", "mcp__docs__search", &json!({ "version": "mcp@1" })),
            result(
                "z0",
                "zoom",
                &json!({
                    "version": "zoom@0",
                    "lift": { "from": "zoom@0", "outcome": "stranded" },
                })
            ),
        ]
    );
}

/// The same transcript renders the same bytes twice; the lifted view
/// replays as itself; a turn added after it leaves its bytes.
#[test]
fn a_replay_renders_the_same_bytes() {
    let (mut entries, _) = old_transcript();
    let first = derive_view(&entries).messages;
    let bytes = serde_json::to_string(&first).expect("messages serialize");
    assert_eq!(
        serde_json::to_string(&derive_view(&entries).messages).expect("messages serialize"),
        bytes
    );
    assert_eq!(order_tool_results(&first), first);
    entries.push(entry(7, user("and line 4")));
    let longer = derive_view(&entries).messages;
    assert_eq!(
        serde_json::to_string(&longer[..first.len()]).expect("messages serialize"),
        bytes
    );
}

/// Each kept argument takes its stored value under its new name, in the
/// lift's order; an added one takes its parsed value.
#[test]
fn a_lift_places_stored_and_added_arguments() {
    let stored = object(json!({ "a": 1, "file": "x.rs", "x": [2] }));
    let kept = |index: usize, key: &str| Arg::Kept {
        index,
        key: key.to_owned(),
    };
    let placed = place(
        &stored,
        vec![
            kept(0, "a"),
            kept(1, "path"),
            kept(2, "x"),
            Arg::Added {
                key: "limit".to_owned(),
                json: "10".to_owned(),
            },
        ],
    )
    .expect("a whole placement");
    assert_eq!(
        placed,
        object(json!({ "a": 1, "path": "x.rs", "x": [2], "limit": 10 }))
    );
}

/// A placement that would drop, repeat or invent an argument, or add one
/// that is not JSON, is refused.
#[test]
fn a_placement_that_loses_an_argument_is_refused() {
    let stored = object(json!({ "a": 1, "b": 2 }));
    let kept = |index: usize, key: &str| Arg::Kept {
        index,
        key: key.to_owned(),
    };
    assert!(matches!(
        place(&stored, vec![kept(0, "a")]),
        Err(PlaceError::Dropped(1))
    ));
    assert!(matches!(
        place(&stored, vec![kept(0, "a"), kept(0, "b")]),
        Err(PlaceError::Stored(0))
    ));
    assert!(matches!(
        place(&stored, vec![kept(0, "a"), kept(1, "a")]),
        Err(PlaceError::Twice(key)) if key == "a"
    ));
    assert!(matches!(
        place(
            &stored,
            vec![
                kept(0, "a"),
                kept(1, "b"),
                Arg::Added {
                    key: "c".to_owned(),
                    json: "{".to_owned(),
                },
            ],
        ),
        Err(PlaceError::Added { key, .. }) if key == "c"
    ));
}
