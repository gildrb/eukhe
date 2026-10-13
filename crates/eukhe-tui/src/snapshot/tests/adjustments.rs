//! Request adjustments on assistant messages: the snapshot decode keeps
//! them typed (an unreadable entry is counted, never dropped), and the
//! transcript shows them as dim notes from the `details` level up.

use super::*;
use eukhe_types::pi_ai::{AdjustedField, AdjustmentReason, RequestAdjustment};

fn adjusted_reply() -> Value {
    json!({
        "role": "assistant",
        "content": [{ "type": "text", "text": "answer body" }],
        "provider": "faux", "model": "faux-1",
        "stopReason": "stop",
        "adjustments": [
            { "field": "serviceTier", "change": "dropped", "reason": "unsupportedByModel" },
            { "field": "maxTokens", "change": "clamped", "requested": 64000, "sent": 30000, "reason": "contextWindow" },
            { "field": "strictTool", "change": "dropped", "reason": "unsupportedSchema", "subject": "read" },
            { "field": "notAField", "change": "dropped", "reason": "unsupportedByModel" },
        ],
        "timestamp": 1,
    })
}

#[test]
fn snapshot_assistant_message_decodes_its_adjustments() {
    let entries = message_value_to_entries(&msg(adjusted_reply()));
    let [ChatEntry::Assistant(message)] = entries.as_slice() else {
        panic!("entries: {entries:?}");
    };
    assert_eq!(
        message.adjustments.read,
        vec![
            RequestAdjustment::dropped(
                AdjustedField::ServiceTier,
                AdjustmentReason::UnsupportedByModel
            ),
            RequestAdjustment::clamped(
                AdjustedField::MaxTokens,
                64_000,
                30_000,
                AdjustmentReason::ContextWindow
            ),
            RequestAdjustment::dropped(
                AdjustedField::StrictTool,
                AdjustmentReason::UnsupportedSchema
            )
            .for_subject("read"),
        ]
    );
    assert_eq!(
        message.adjustments.unreadable, 1,
        "the malformed entry is counted"
    );
}

#[test]
fn a_tool_only_message_keeps_its_adjustments() {
    // No body, only a tool call: the message still folds into a component
    // so the adjustment notes have a place to render.
    let entries = message_value_to_entries(&msg(json!({
        "role": "assistant",
        "content": [{ "type": "toolCall", "id": "c1", "name": "read", "arguments": {} }],
        "stopReason": "toolUse",
        "adjustments": [
            { "field": "strictTool", "change": "dropped", "reason": "unsupportedSchema", "subject": "read" },
        ],
    })));
    let [ChatEntry::Assistant(message), ChatEntry::Tool(card)] = entries.as_slice() else {
        panic!("entries: {entries:?}");
    };
    assert!(message.blocks.is_empty());
    assert!(message.has_tool_calls);
    assert_eq!(message.adjustments.read.len(), 1);
    assert_eq!(card.name, "read");
}

#[test]
fn adjustment_notes_render_from_the_details_level() {
    // Rows trimmed of their margin and padding; a message's last row leads
    // with the OSC 133 zone-end marker, so rows are matched by their end.
    let frame_text = |view: &mut crate::view::AgentView| -> Vec<String> {
        view.render_transcript(100)
            .iter()
            .map(|row| line_text(row).trim().to_string())
            .collect()
    };
    let notes = [
        "adjusted: serviceTier dropped (model does not support it)",
        "adjusted: maxTokens 64000 -> 30000 (context window)",
        "adjusted: strictTool read dropped (schema cannot be strict)",
        "adjusted: 1 adjustment could not be read",
    ];
    let mut view = test_view();
    for entry in message_value_to_entries(&msg(adjusted_reply())) {
        view.push_entry(entry);
    }
    view.detail = crate::chat::Detail::Overview;
    let overview = frame_text(&mut view);
    assert!(
        overview.iter().any(|row| row.ends_with("answer body")),
        "the body renders: {overview:?}"
    );
    assert!(
        !overview.iter().any(|row| row.contains("adjusted:")),
        "the overview level hides the notes: {overview:?}"
    );
    for detail in [crate::chat::Detail::Details, crate::chat::Detail::All] {
        view.detail = detail;
        let rows = frame_text(&mut view);
        for note in notes {
            assert!(
                rows.iter().any(|row| row.ends_with(note)),
                "{detail:?} shows {note:?}: {rows:?}"
            );
        }
    }
}
