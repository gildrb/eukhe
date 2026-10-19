//! The rounds in a row with the same tool calls and the same results
//! (docs/harness.md H4.8, law `rec_never_runs_a_repeat`; omp
//! `tool-call-loop-guard.ts`, whose `wait` exemption is here a result that
//! changes). The count comes from the request's context, so a restart
//! keeps it and a failed reply (not in the context) never adds to it.

use std::fmt::Write as _;

use eukhe_types::pi_ai::{
    AssistantContentBlock, JsonObject, JsonValue, Message, ToolCall, UserContentBlock,
};

/// The intent parameter of every tool schema (docs/tools.md S7.3): it
/// says why, not what, so two calls that differ only in it are the same.
const INTENT: &str = "i";

/// The canonical JSON of a call's arguments: object keys sorted at every
/// depth, the top-level intent `i` left out.
pub(crate) fn canonical_arguments(arguments: &JsonObject) -> String {
    let mut out = String::new();
    write_object(
        arguments,
        arguments.keys().filter(|key| *key != INTENT).collect(),
        &mut out,
    );
    out
}

/// `object` with only `keys`, in sorted order.
fn write_object(object: &JsonObject, mut keys: Vec<&String>, out: &mut String) {
    keys.sort();
    out.push('{');
    for (index, key) in keys.into_iter().enumerate() {
        if index > 0 {
            out.push(',');
        }
        let _ = write!(out, "{}:", JsonValue::String(key.clone()));
        write_canonical(&object[key], out);
    }
    out.push('}');
}

fn write_canonical(value: &JsonValue, out: &mut String) {
    match value {
        JsonValue::Object(object) => write_object(object, object.keys().collect(), out),
        JsonValue::Array(items) => {
            out.push('[');
            for (index, item) in items.iter().enumerate() {
                if index > 0 {
                    out.push(',');
                }
                write_canonical(item, out);
            }
            out.push(']');
        }
        JsonValue::Null | JsonValue::Bool(_) | JsonValue::Number(_) | JsonValue::String(_) => {
            let _ = write!(out, "{value}");
        }
    }
}

/// The calls as a set: each call's name and canonical arguments, sorted.
fn call_set<'a>(calls: impl Iterator<Item = &'a ToolCall>) -> Vec<(&'a str, String)> {
    let mut set: Vec<(&str, String)> = calls
        .map(|call| (call.name.as_str(), canonical_arguments(&call.arguments)))
        .collect();
    set.sort();
    set
}

/// One round at the end of a context: its calls as a set, and its results
/// (content and error flag), in context order.
type Round<'a> = (Vec<(&'a str, String)>, Vec<(&'a [UserContentBlock], bool)>);

/// The rounds in a row that `calls` would make: 1 and the rounds at the
/// end of `messages` with the same calls (names and canonical arguments,
/// in any order) and the same results as the last round. A round is a
/// reply with tool calls (whatever its stop reason) and the results after
/// it. When the results change (a call polls a job that makes progress),
/// a new row starts: it is no repeat. A user message (a steer, the user's
/// next turn) ends the row: the user changed the context. System messages
/// do not; a reply without tool calls does.
pub(crate) fn rounds_in_a_row(messages: &[Message], calls: &[ToolCall]) -> u32 {
    let set = call_set(calls.iter());
    let mut last: Option<Round<'_>> = None;
    let mut results = Vec::new();
    let mut rounds = 1_u32;
    for message in messages.iter().rev() {
        match message {
            Message::System(_) => {}
            Message::User(_) => break,
            Message::ToolResult(result) => {
                results.push((result.content.as_slice(), result.is_error));
            }
            Message::Assistant(reply) => {
                results.reverse();
                let round = (
                    call_set(reply.content.iter().filter_map(|content| match content {
                        AssistantContentBlock::ToolCall(call) => Some(call),
                        AssistantContentBlock::Text(_) | AssistantContentBlock::Thinking(_) => None,
                    })),
                    std::mem::take(&mut results),
                );
                let same = !round.0.is_empty()
                    && match &last {
                        None => round.0 == set,
                        Some(last) => round == *last,
                    };
                if !same {
                    break;
                }
                rounds = rounds.saturating_add(1);
                last.get_or_insert(round);
            }
        }
    }
    rounds
}

#[cfg(test)]
mod tests {
    use eukhe_ai::providers::faux::{faux_assistant_message, FauxAssistantMessageOptions};
    use eukhe_types::pi_ai::{
        AssistantContentBlock, JsonObject, JsonValue, Message, StopReason, TextContent, ToolCall,
        ToolResultMessage, UserContent, UserContentBlock, UserMessage,
    };
    use serde_json::json;

    use super::{canonical_arguments, rounds_in_a_row};

    fn object(value: JsonValue) -> JsonObject {
        let JsonValue::Object(object) = value else {
            panic!("the test arguments must be a JSON object")
        };
        object
    }

    fn call(id: &str, arguments: JsonValue) -> ToolCall {
        ToolCall {
            id: id.to_owned(),
            name: "read".to_owned(),
            arguments: object(arguments),
            ..ToolCall::default()
        }
    }

    /// A reply with `calls` and stop reason `stop_reason`, then a result
    /// with `result` for each call.
    fn round(stop_reason: StopReason, calls: &[ToolCall], result: &str) -> Vec<Message> {
        let mut round = vec![Message::Assistant(faux_assistant_message(
            calls
                .iter()
                .cloned()
                .map(AssistantContentBlock::ToolCall)
                .collect::<Vec<_>>(),
            FauxAssistantMessageOptions {
                stop_reason: Some(stop_reason),
                ..FauxAssistantMessageOptions::default()
            },
        ))];
        round.extend(calls.iter().map(|call| {
            Message::ToolResult(ToolResultMessage {
                tool_call_id: call.id.clone(),
                tool_name: call.name.clone(),
                content: vec![UserContentBlock::Text(TextContent::new(result))],
                details: None,
                usage: None,
                nested_calls: None,
                is_error: false,
                timestamp: 0,
                duration_ms: None,
            })
        }));
        round
    }

    #[test]
    fn canonical_arguments_ignore_the_intent_and_the_key_order() {
        assert_eq!(
            [
                json!({"i": "first look", "path": "a.rs", "range": {"to": 9, "from": 1}}),
                json!({"range": {"from": 1, "to": 9}, "path": "a.rs", "i": "look again"}),
                json!({"range": {"from": 1, "to": 9}, "path": "a.rs"}),
                // Only the top-level intent is left out.
                json!({"path": "a.rs", "range": {"i": 1}}),
            ]
            .map(|arguments| canonical_arguments(&object(arguments))),
            [
                r#"{"path":"a.rs","range":{"from":1,"to":9}}"#.to_owned(),
                r#"{"path":"a.rs","range":{"from":1,"to":9}}"#.to_owned(),
                r#"{"path":"a.rs","range":{"from":1,"to":9}}"#.to_owned(),
                r#"{"path":"a.rs","range":{"i":1}}"#.to_owned(),
            ]
        );
    }

    #[test]
    fn counts_the_rounds_with_the_same_calls_and_the_same_results() {
        let calls = [call("c1", json!({"path": "a.rs", "i": "look"}))];
        let next = [call("c9", json!({"i": "again", "path": "a.rs"}))];
        let other = [call("c2", json!({"path": "b.rs"}))];
        let same: Vec<Message> = [
            round(StopReason::ToolUse, &calls, "one"),
            // A reply with stop reason `stop` and tool calls is a round.
            round(StopReason::Stop, &calls, "one"),
        ]
        .concat();
        let changed: Vec<Message> = [
            round(StopReason::ToolUse, &calls, "one"),
            round(StopReason::ToolUse, &calls, "two"),
        ]
        .concat();
        let steered: Vec<Message> = [
            same.clone(),
            vec![Message::User(UserMessage {
                content: UserContent::Text("look at b.rs instead".to_owned()),
                timestamp: 0,
            })],
        ]
        .concat();
        assert_eq!(
            [
                rounds_in_a_row(&[], &next),
                rounds_in_a_row(&same, &next),
                rounds_in_a_row(&same, &other),
                rounds_in_a_row(&changed, &next),
                rounds_in_a_row(&steered, &next),
            ],
            [1, 3, 1, 2, 1]
        );
    }
}
