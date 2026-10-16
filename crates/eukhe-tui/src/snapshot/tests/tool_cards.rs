//! The tool-card folds: streamed calls naming their card late, the
//! failed-frame sweep and re-armed ids, and the replay's pairing of
//! results with pending cards.

use super::*;

/// The live wire shape that broke the ipython card: a provider announces
/// the tool call before the function name streams in (the openai-style
/// toolcall-start frame carries the block unnamed), so the first
/// `message_update` frame has an empty `name`. The card must not freeze
/// on that frame -- the named frame routes it to the ipython renderer and
/// the collapsed line shows the code preview, not the raw arguments
/// JSON.
#[test]
fn unnamed_streamed_tool_call_renders_code_once_named() {
    let mut view = test_view();
    apply_streamed_tool_card(&mut view, "call-1", "", &json!({ "code": "fibonacci(23)" }));
    assert!(
        card_of(&view).is_none(),
        "a call without a streamed name renders no card yet"
    );
    apply_streamed_tool_card(
        &mut view,
        "call-1",
        "ipython",
        &json!({ "code": "fibonacci(23)" }),
    );
    let card = card_of(&view).expect("the named frame creates the card");
    assert_eq!(card.name, "ipython");
    assert!(card.args.get("code").is_some(), "args stream into the card");
    let rows = rendered_card_text(&view);
    assert!(
        rows.iter()
            .any(|row| row.contains("python") && row.contains("fibonacci(23)")),
        "the ipython card renders the code preview: {rows:?}"
    );
    assert!(
        rows.iter()
            .all(|row| !row.contains("\"code\"") && !row.contains('{')),
        "the raw arguments JSON must not render: {rows:?}"
    );
}

/// TS `message_end`'s failed-frame sweep: every still-pending card
/// settles with the failure text as an error result, the pending set
/// drains, and the card flags the abort so the tool's late result
/// frames land on nothing.
#[test]
fn failed_frame_sweep_settles_pending_tool_cards() {
    let mut view = test_view();
    apply_streamed_tool_card(
        &mut view,
        "call-1",
        "bash",
        &json!({ "command": "sleep 10" }),
    );
    apply_tool_execution_start(&mut view, "call-1", "bash", Value::Null);
    let mut pending = std::collections::HashSet::from(["call-1".to_string()]);
    let mut aborted = std::collections::HashSet::new();
    settle_pending_tool_cards(
        &mut view,
        &mut pending,
        &mut aborted,
        "Operation aborted - 3s",
    );
    assert!(pending.is_empty(), "the sweep drains the pending set");
    // Every drained id records as aborted - late frames for a call
    // that never created a card land on nothing the same way.
    assert_eq!(
        aborted,
        std::collections::HashSet::from(["call-1".to_string()]),
        "the sweep records the settled ids"
    );
    let card = card_of(&view).expect("the streamed card");
    assert!(card.aborted, "the settled card flags the abort");
    let result = card.result.as_ref().expect("the settle result");
    assert!(result.is_error, "the settle result is an error");
    assert_eq!(result.text_output(false), "Operation aborted - 3s");
    assert!(!card.result_partial, "the settle result is final");
    assert!(card.ended_at.is_some(), "the settle stamps the card ended");
}

/// A reused id after a failed run re-arms as a fresh card (TS's cleared
/// pending map forces a new component for the new invocation); the old
/// settled card keeps its sweep-written abort result in the transcript.
#[test]
fn reused_id_after_abort_re_arms_as_a_fresh_card() {
    let mut view = test_view();
    apply_streamed_tool_card(
        &mut view,
        "call-1",
        "bash",
        &json!({ "command": "sleep 10" }),
    );
    apply_tool_execution_start(&mut view, "call-1", "bash", Value::Null);
    let mut pending = std::collections::HashSet::from(["call-1".to_string()]);
    let mut aborted = std::collections::HashSet::new();
    settle_pending_tool_cards(
        &mut view,
        &mut pending,
        &mut aborted,
        "Operation aborted - 3s",
    );
    let settled = cards_of(&view);
    // The re-armed invocation's streamed frame: a fresh card, not a
    // refresh of the settled one.
    apply_streamed_tool_card(
        &mut view,
        "call-1",
        "bash",
        &json!({ "command": "echo ready" }),
    );
    let cards = cards_of(&view);
    assert_eq!(cards.len(), 2, "two cards: {cards:?}");
    assert!(cards[0].aborted, "the old card keeps its abort");
    assert_eq!(
        cards[0]
            .result
            .as_ref()
            .expect("the settle result")
            .text_output(false),
        "Operation aborted - 3s"
    );
    assert!(!cards[1].aborted, "the new card starts fresh");
    assert_eq!(cards[1].result, None, "the new card has no result");
    assert_eq!(cards[1].args.get("command"), Some(&json!("echo ready")));
    // The execution start marks the new invocation's card; the old
    // settled card stays untouched.
    apply_tool_execution_start(&mut view, "call-1", "bash", Value::Null);
    let cards = cards_of(&view);
    assert_eq!(cards[0], settled[0], "the settled card is untouched");
    assert!(cards[1].started, "the fresh card runs");
}

/// A second failed run settles the re-armed invocation's own card -- the
/// newest card carrying the id -- so the older card keeps the first
/// sweep's result (TS's pending map only ever holds the current
/// component).
#[test]
fn sweep_settles_the_re_armed_card_not_the_settled_one() {
    let mut view = test_view();
    apply_streamed_tool_card(
        &mut view,
        "call-1",
        "bash",
        &json!({ "command": "sleep 10" }),
    );
    let mut pending = std::collections::HashSet::from(["call-1".to_string()]);
    let mut aborted = std::collections::HashSet::new();
    settle_pending_tool_cards(
        &mut view,
        &mut pending,
        &mut aborted,
        "Operation aborted - 3s",
    );
    apply_streamed_tool_card(
        &mut view,
        "call-1",
        "bash",
        &json!({ "command": "echo ready" }),
    );
    let mut pending = std::collections::HashSet::from(["call-1".to_string()]);
    let mut aborted = std::collections::HashSet::new();
    settle_pending_tool_cards(
        &mut view,
        &mut pending,
        &mut aborted,
        "Aborted after 1 retry attempt - 8s",
    );
    let cards = cards_of(&view);
    assert_eq!(cards.len(), 2, "two cards: {cards:?}");
    assert_eq!(
        cards[0]
            .result
            .as_ref()
            .expect("the first settle")
            .text_output(false),
        "Operation aborted - 3s",
        "the older card keeps its own sweep result"
    );
    assert!(cards[1].aborted, "the re-armed card settled");
    assert_eq!(
        cards[1]
            .result
            .as_ref()
            .expect("the second settle")
            .text_output(false),
        "Aborted after 1 retry attempt - 8s"
    );
}

/// The latest streamed frame wins on an existing card (TS builds the
/// pending component against the latest streaming call), so a card that
/// somehow kept an empty name picks the name up from the next frame.
#[test]
fn existing_card_refreshes_name_and_args_from_latest_frame() {
    let mut view = test_view();
    view.push_entry(ChatEntry::Tool(Box::new(ToolCallCard {
        id: "call-1".into(),
        name: String::new(),
        args: Value::Null,
        ..Default::default()
    })));
    apply_streamed_tool_card(&mut view, "call-1", "ipython", &json!({ "code": "x = 1" }));
    let card = card_of(&view).expect("the streamed frame finds the card");
    assert_eq!(card.name, "ipython");
    assert_eq!(card.args.get("code"), Some(&json!("x = 1")));
}

/// `tool_execution_start` reports the actual tool name ("ipython" on
/// the wire today); it backfills a card still unnamed and creates the
/// card when the message frames have not arrived yet.
#[test]
fn tool_execution_start_reports_the_tool_name() {
    let mut view = test_view();
    view.push_entry(ChatEntry::Tool(Box::new(ToolCallCard {
        id: "call-1".into(),
        name: String::new(),
        args: Value::Null,
        ..Default::default()
    })));
    apply_tool_execution_start(
        &mut view,
        "call-1",
        "ipython",
        json!({ "code": "print('hi')" }),
    );
    let card = card_of(&view).expect("the start event finds the card");
    assert_eq!(card.name, "ipython");
    assert!(card.started, "the start event marks execution started");

    let mut fresh = test_view();
    apply_tool_execution_start(
        &mut fresh,
        "call-2",
        "ipython",
        json!({ "code": "fibonacci(23)" }),
    );
    let rows = rendered_card_text(&fresh);
    assert!(
        rows.iter()
            .any(|row| row.contains("python") && row.contains("fibonacci(23)")),
        "a card created from the start event renders the code preview: {rows:?}"
    );
}

#[test]
fn an_unmatched_replay_result_keeps_its_standalone_card() {
    // A `toolResult` whose call never landed on a pending card
    // keeps its orphan card exactly like the live push path - the
    // rebuilt transcript never drops the standalone result.
    let mut rebuilt = Reconstructed::default();
    rebuilt.push_message(&msg(json!({
        "role": "user",
        "content": "run it",
    })));
    rebuilt.push_message(&msg(json!({
        "role": "toolResult",
        "toolCallId": "orphan",
        "toolName": "bash",
        "content": [{ "type": "text", "text": "orphan output" }],
        "isError": false,
        "timestamp": 123,
    })));
    assert_eq!(rebuilt.chat.len(), 2, "the orphan card lands");
    match &rebuilt.chat[1] {
        ChatEntry::Tool(card) => {
            assert_eq!(card.id, "orphan");
            assert_eq!(card.name, "bash");
            assert!(
                card.result.is_some(),
                "the orphan keeps its own result card"
            );
        }
        other => panic!("the orphan is a card: {other:?}"),
    }
}

#[test]
fn a_bulk_replay_never_drops_an_orphan_result() {
    // The bulk path (slim attach, the get-messages rebuild) keeps
    // an unmatched `toolResult` as its standalone orphan card -
    // the rebuilt transcript matches the live and incremental
    // paths.
    let chat = transcript_to_entries(&[
        msg(json!({
            "role": "user",
            "content": "run it",
        })),
        msg(json!({
            "role": "toolResult",
            "toolCallId": "orphan",
            "toolName": "bash",
            "content": [{ "type": "text", "text": "orphan output" }],
            "isError": false,
            "timestamp": 123,
        })),
    ]);
    assert_eq!(chat.len(), 2, "the orphan card lands in the bulk path");
    match &chat[1] {
        ChatEntry::Tool(card) => {
            assert_eq!(card.id, "orphan");
            assert_eq!(card.name, "bash");
            assert!(card.result.is_some(), "the bulk orphan keeps its own card");
        }
        other => panic!("the orphan is a card: {other:?}"),
    }
}

#[test]
fn a_bulk_replay_settles_the_last_pending_card_for_a_reused_id() {
    // A later invocation reusing a `tool_call_id` settles its OWN
    // card (the live `rposition` match), never the first
    // invocation's pending one - and the result never becomes an
    // orphan.
    let chat = transcript_to_entries(&[
        msg(json!({
            "role": "assistant",
            "content": [
                { "type": "text", "text": "calling twice" },
                { "type": "toolCall", "id": "dup", "name": "ipython", "arguments": {"code": "1"} },
            ],
            "timestamp": 1,
        })),
        msg(json!({
            "role": "assistant",
            "content": [
                { "type": "text", "text": "again" },
                { "type": "toolCall", "id": "dup", "name": "ipython", "arguments": {"code": "2"} },
            ],
            "timestamp": 2,
        })),
        msg(json!({
            "role": "toolResult",
            "toolCallId": "dup",
            "toolName": "ipython",
            "content": [{ "type": "text", "text": "the second run" }],
            "isError": false,
            "timestamp": 3,
        })),
    ]);
    let cards: Vec<&crate::chat::ToolCallCard> = chat
        .iter()
        .filter_map(|entry| match entry {
            ChatEntry::Tool(card) => Some(card.as_ref()),
            _ => None,
        })
        .collect();
    assert_eq!(cards.len(), 2, "two cards for the reused id: {chat:?}");
    assert!(cards[0].result.is_none(), "the first stays pending");
    let settled = cards[1].result.as_ref().expect("the LAST card settled");
    assert_eq!(
        settled.content,
        vec![json!({ "type": "text", "text": "the second run" })]
    );
}

#[test]
fn an_interleaved_replay_pairs_results_in_arrival_order() {
    // Call, result, ANOTHER call reusing the id, result: each
    // result settles the call it FOLLOWED (the live arrival-order
    // pairing), never the later invocation's card.
    let chat = transcript_to_entries(&[
        msg(json!({
            "role": "assistant",
            "content": [
                { "type": "text", "text": "first" },
                { "type": "toolCall", "id": "dup", "name": "ipython", "arguments": {"code": "1"} },
            ],
            "timestamp": 1,
        })),
        msg(json!({
            "role": "toolResult",
            "toolCallId": "dup",
            "toolName": "ipython",
            "content": [{ "type": "text", "text": "the first run" }],
            "isError": false,
            "timestamp": 2,
        })),
        msg(json!({
            "role": "assistant",
            "content": [
                { "type": "text", "text": "second" },
                { "type": "toolCall", "id": "dup", "name": "ipython", "arguments": {"code": "2"} },
            ],
            "timestamp": 3,
        })),
        msg(json!({
            "role": "toolResult",
            "toolCallId": "dup",
            "toolName": "ipython",
            "content": [{ "type": "text", "text": "the second run" }],
            "isError": false,
            "timestamp": 4,
        })),
    ]);
    let cards: Vec<&crate::chat::ToolCallCard> = chat
        .iter()
        .filter_map(|entry| match entry {
            ChatEntry::Tool(card) => Some(card.as_ref()),
            _ => None,
        })
        .collect();
    assert_eq!(cards.len(), 2, "two cards: {chat:?}");
    assert_eq!(
        cards[0]
            .result
            .as_ref()
            .and_then(|result| result.content.first())
            .and_then(|block| block.get("text"))
            .and_then(Value::as_str),
        Some("the first run"),
        "the FIRST call kept its own result"
    );
    assert_eq!(
        cards[1]
            .result
            .as_ref()
            .and_then(|result| result.content.first())
            .and_then(|block| block.get("text"))
            .and_then(Value::as_str),
        Some("the second run"),
        "the SECOND call kept its own result"
    );
}

#[test]
fn an_orphan_result_keeps_its_wire_position() {
    // An orphan result BETWEEN two ordinary messages lands at its
    // own wire position in the rebuilt transcript - never at the
    // tail (condensation can never span across it).
    let chat = transcript_to_entries(&[
        msg(json!({
            "role": "user",
            "content": "before",
            "timestamp": 1,
        })),
        msg(json!({
            "role": "toolResult",
            "toolCallId": "orphan",
            "toolName": "bash",
            "content": [{ "type": "text", "text": "orphan output" }],
            "isError": false,
            "timestamp": 2,
        })),
        msg(json!({
            "role": "user",
            "content": "after",
            "timestamp": 3,
        })),
    ]);
    assert_eq!(chat.len(), 3, "the orphan card sits between: {chat:?}");
    match &chat[1] {
        ChatEntry::Tool(card) => assert!(card.result.is_some()),
        other => panic!("the orphan sits at its wire position: {other:?}"),
    }
    assert!(matches!(&chat[2], ChatEntry::User { text } if text == "after"));
}

#[test]
fn a_leftover_settle_keeps_its_own_orphan_card() {
    // A result arriving after its card ALREADY settled (a leftover)
    // never crosses a later reused invocation: it keeps its own
    // orphan card at its wire position, and the later card stays
    // pending - exactly the live push path.
    let chat = transcript_to_entries(&[
        msg(json!({
            "role": "assistant",
            "content": [
                { "type": "text", "text": "first" },
                { "type": "toolCall", "id": "dup", "name": "ipython", "arguments": {"code": "1"} },
            ],
            "timestamp": 1,
        })),
        msg(json!({
            "role": "toolResult",
            "toolCallId": "dup",
            "toolName": "ipython",
            "content": [{ "type": "text", "text": "the first run" }],
            "isError": false,
            "timestamp": 2,
        })),
        msg(json!({
            "role": "toolResult",
            "toolCallId": "dup",
            "toolName": "ipython",
            "content": [{ "type": "text", "text": "the leftover" }],
            "isError": false,
            "timestamp": 3,
        })),
        msg(json!({
            "role": "assistant",
            "content": [
                { "type": "text", "text": "second" },
                { "type": "toolCall", "id": "dup", "name": "ipython", "arguments": {"code": "2"} },
            ],
            "timestamp": 4,
        })),
    ]);
    let cards: Vec<&crate::chat::ToolCallCard> = chat
        .iter()
        .filter_map(|entry| match entry {
            ChatEntry::Tool(card) => Some(card.as_ref()),
            _ => None,
        })
        .collect();
    assert_eq!(
        cards.len(),
        3,
        "the call, the leftover's orphan, and the later call: {chat:?}"
    );
    assert_eq!(
        cards[0]
            .result
            .as_ref()
            .and_then(|result| result.content.first())
            .and_then(|block| block.get("text"))
            .and_then(Value::as_str),
        Some("the first run"),
        "the FIRST call kept its own result"
    );
    let leftover = cards[1];
    assert_eq!(leftover.id, "dup");
    assert!(
        leftover.result.is_some(),
        "the leftover keeps its own orphan card"
    );
    assert_eq!(
        leftover
            .result
            .as_ref()
            .and_then(|result| result.content.first())
            .and_then(|block| block.get("text"))
            .and_then(Value::as_str),
        Some("the leftover")
    );
    // The second invocation's card stays pending (its result arrives
    // later or never).
    let second_call = chat.iter().rev().find_map(|entry| match entry {
        ChatEntry::Tool(card) if card.result.is_none() => Some(card.as_ref()),
        _ => None,
    });
    let Some(second) = second_call else {
        panic!("the second call: {chat:?}")
    };
    assert!(
        second.result.is_none(),
        "the later invocation stays pending"
    );
}
