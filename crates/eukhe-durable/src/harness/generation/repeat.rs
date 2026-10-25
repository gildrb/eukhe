//! The rounds in a row with the same tool calls and the same results
//! (docs/harness.md H4.8, law `rec_never_runs_a_repeat`; omp
//! `tool-call-loop-guard.ts`, whose `wait` exemption is here a result that
//! changes). The count comes from the request's context, so a restart
//! keeps it and a failed reply (not in the context) never adds to it. The
//! compiled core walks the context (`eukhe_bend::rules::repeat`,
//! `laws/repeat.bend`): Rust gives it each message newest first, each
//! round's calls and each result as an id, and canonicalizes only the
//! rounds the walk reaches.

use std::fmt::Write as _;
use std::num::NonZeroU32;

use eukhe_bend::rules::repeat::{Row, Seen};
use eukhe_types::pi_ai::{AssistantContentBlock, JsonObject, JsonValue, Message, ToolCall};

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

/// Equal values to equal ids, numbered in the order first seen (the ids
/// of one walk).
struct Ids<T> {
    seen: Vec<T>,
}

impl<T: PartialEq> Ids<T> {
    fn new() -> Ids<T> {
        Ids { seen: Vec::new() }
    }

    fn id(&mut self, value: T) -> u64 {
        let found = self.seen.iter().position(|seen| *seen == value);
        let index = found.unwrap_or_else(|| {
            self.seen.push(value);
            self.seen.len() - 1
        });
        index as u64
    }
}

/// The rounds in a row that `calls` would make: 1 and the rounds at the
/// end of `messages` with the same calls (names and canonical arguments,
/// in any order) and the same results as the last round. A round is a
/// reply with tool calls (whatever its stop reason) and the results after
/// it. When the results change (a call polls a job that makes progress),
/// a new row starts: it is no repeat. A user message (a steer, the user's
/// next turn) ends the row: the user changed the context. System messages
/// do not; a reply without tool calls does. The compiled core decides all
/// of this (`laws/repeat.bend`); Rust gives each round's calls (as a set)
/// and each result (content and error flag) an id, equal values equal ids.
pub(crate) fn rounds_in_a_row(messages: &[Message], calls: &[ToolCall]) -> NonZeroU32 {
    let mut sets = Ids::new();
    let mut results = Ids::new();
    let mut row = Row::open(sets.id(call_set(calls.iter())));
    for message in messages.iter().rev() {
        let seen = match message {
            Message::System(_) => Seen::System,
            Message::User(_) => Seen::User,
            Message::ToolResult(result) => {
                Seen::Result(results.id((result.content.as_slice(), result.is_error)))
            }
            Message::Assistant(reply) => {
                let set = call_set(reply.content.iter().filter_map(|content| match content {
                    AssistantContentBlock::ToolCall(call) => Some(call),
                    AssistantContentBlock::Text(_) | AssistantContentBlock::Thinking(_) => None,
                }));
                if set.is_empty() {
                    Seen::Said
                } else {
                    Seen::Called(sets.id(set))
                }
            }
        };
        if let Some(rounds) = row.step(seen) {
            return rounds;
        }
    }
    row.end()
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

    /// The Rust-to-core bridge: the ids Rust gives a context's calls (the
    /// intent and the key order dropped) and results reach the compiled
    /// walk, which `laws/repeat.bend` pins.
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
                rounds_in_a_row(&[], &next).get(),
                rounds_in_a_row(&same, &next).get(),
                rounds_in_a_row(&same, &other).get(),
                rounds_in_a_row(&changed, &next).get(),
                rounds_in_a_row(&steered, &next).get(),
            ],
            [1, 3, 1, 2, 1]
        );
    }
}
