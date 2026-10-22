//! The rebuild side of `laws/turn_visibility.bend`: a reopened chat folds
//! the row each ended turn left live (R4, R5, R7) and collapses a retry
//! episode to its one line (R6), whatever order its rows were stored in.

use super::*;

fn user(text: &str) -> Value {
    json!({ "role": "user", "content": text })
}

fn answer(text: &str) -> Value {
    json!({ "role": "assistant", "content": [{ "type": "text", "text": text }] })
}

fn tool_round() -> [Value; 2] {
    [
        json!({
            "role": "assistant",
            "content": [
                { "type": "text", "text": "listing" },
                { "type": "toolCall", "id": "c1", "name": "bash", "arguments": { "command": "ls" } },
            ],
            "stopReason": "toolUse",
        }),
        json!({
            "role": "toolResult",
            "toolCallId": "c1",
            "toolName": "bash",
            "content": [{ "type": "text", "text": "a b" }],
            "isError": false,
        }),
    ]
}

fn failed_attempt(error: &str) -> Value {
    json!({ "role": "assistant", "content": [], "stopReason": "error", "errorMessage": error })
}

fn outcome(success: bool, text: &str) -> Value {
    json!({
        "role": "custom",
        "customType": "provider_retry_outcome",
        "content": text,
        "display": true,
        "details": { "success": success, "attempts": 1, "finalError": "529 overloaded" },
    })
}

fn ended(messages: impl IntoIterator<Item = Value>) -> Vec<ChatEntry> {
    fold_transcript(&msgs(messages), TurnTail::Ended)
}

fn running(messages: impl IntoIterator<Item = Value>) -> Vec<ChatEntry> {
    fold_transcript(&msgs(messages), TurnTail::Running)
}

/// The entries with the tool cards' fold instants cleared: two folds of
/// the same transcript compare whole.
fn unclocked(mut entries: Vec<ChatEntry>) -> Vec<ChatEntry> {
    for entry in &mut entries {
        if let ChatEntry::Tool(card) = entry {
            card.started_at = None;
            card.ended_at = None;
        }
    }
    entries
}

/// F4, F5, F6 (`laws/turn_visibility.bend`): a run that ended before its
/// prompt got any assistant message (it stopped before its first request,
/// the engine reported nothing, or the generation failed without a
/// message) leaves the stored prompt alone; the reopened chat says the
/// turn ended without a reply and names the next step, like the live row.
#[test]
fn a_prompt_with_no_reply_and_no_run_folds_the_no_reply_row() {
    assert_eq!(
        ended([user("say hi")]),
        vec![
            ChatEntry::User {
                text: "say hi".to_string()
            },
            no_reply_row(),
        ]
    );
    // A run still open may answer yet: no row.
    assert_eq!(
        running([user("say hi")]),
        vec![ChatEntry::User {
            text: "say hi".to_string()
        }]
    );
}

/// F4: a run that ended after a tool round, with no answering turn after
/// it (an abort during the tools), says so on reopen too.
#[test]
fn a_run_that_ended_after_a_tool_round_folds_the_no_reply_row() {
    let [call, result] = tool_round();
    let mut expected = running([user("list"), call.clone(), result.clone()]);
    expected.push(no_reply_row());
    assert_eq!(
        unclocked(ended([user("list"), call, result])),
        unclocked(expected)
    );
}

/// A tool round followed by another prompt is no evidence the run ended
/// (a steering prompt lands mid-run): no row there.
#[test]
fn a_tool_round_before_the_next_prompt_folds_no_row() {
    let [call, result] = tool_round();
    let entries = ended([user("list"), call, result, user("and now?"), answer("done")]);
    assert!(!entries.contains(&no_reply_row()), "entries: {entries:?}");
}

/// F8: a blank answer shows the "without a reply" row live; the reopened
/// chat folds the same row, also for a turn an older prompt ended.
#[test]
fn a_blank_answer_folds_the_no_reply_row() {
    let blank = json!({ "role": "assistant", "content": [], "stopReason": "stop" });
    assert_eq!(
        ended([user("one"), blank, user("two"), answer("ok")]),
        vec![
            ChatEntry::User {
                text: "one".to_string()
            },
            no_reply_row(),
            ChatEntry::User {
                text: "two".to_string()
            },
            ChatEntry::Assistant(Box::new(AssistantMessage {
                blocks: vec![MessageBlock::Text("ok".to_string())],
                has_tool_calls: false,
                streaming: false,
                error: None,
                aborted: false,
            })),
        ]
    );
}

/// F8: a failure whose tool cards carry it shows the fallback failure row
/// live (at its `turn_end`); the reopened chat folds the same row, unless
/// a retry outcome row followed it (that row is the one line).
#[test]
fn a_failure_with_tool_calls_folds_its_failure_row() {
    let failed_tools = json!({
        "role": "assistant",
        "content": [
            { "type": "toolCall", "id": "c1", "name": "bash", "arguments": { "command": "ls" } },
        ],
        "stopReason": "error",
        "errorMessage": "stream reset",
    });
    let mut expected = running([user("list"), failed_tools.clone()]);
    expected.push(failure_row("stream reset"));
    assert_eq!(ended([user("list"), failed_tools.clone()]), expected);

    let disclosed = outcome(
        false,
        "\u{26a0} Error: Retry failed after 1 attempts: stream reset",
    );
    assert_eq!(
        ended([user("list"), failed_tools.clone(), disclosed.clone()]),
        running([user("list"), failed_tools, disclosed])
    );
}

/// F14: the outcome row of a recovered episode lands after the answer that
/// ended it (`retry_outcome.rs`); the reopened chat drops the failed
/// attempts before that answer, exactly like the live chat whose retry
/// popped them.
#[test]
fn a_recovered_episode_drops_its_attempts_before_the_answer() {
    let recovered = outcome(true, "Recovered after 1 retries: 529 overloaded");
    assert_eq!(
        ended([
            user("deploy"),
            failed_attempt("Error: 529 overloaded"),
            answer("deployed"),
            recovered.clone(),
        ]),
        ended([user("deploy"), answer("deployed"), recovered])
    );
}

/// F15: a reply that streamed text and then failed, with the failure
/// disclosed by its outcome row: the reply keeps its text and the outcome
/// row is the one error.
#[test]
fn a_failed_reply_with_text_keeps_one_error() {
    let failed_text = json!({
        "role": "assistant",
        "content": [{ "type": "text", "text": "Here is the pl" }],
        "stopReason": "error",
        "errorMessage": "529 overloaded",
    });
    let disclosed = outcome(
        false,
        "\u{26a0} Error: Retry failed after 0 attempts: 529 overloaded",
    );
    assert_eq!(
        ended([user("plan"), failed_text, disclosed.clone()]),
        ended([user("plan"), answer("Here is the pl"), disclosed])
    );
}
