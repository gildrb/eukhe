//! The rebuild side of `LAWS.bend` section `turn_visibility`: a reopened chat folds
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
    fold_transcript(&msgs(messages), TurnTail::Ended(None))
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

/// F4, F5, F6 (`LAWS.bend` section `turn_visibility`): a run that ended before its
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

/// A run the engine stopped at its tool round cap ends after a tool
/// round too; the attach snapshot's `runLimitError` names the cap, so the
/// reopened chat shows that failure, as the live row did, and never the
/// "no other model" report.
#[test]
fn a_run_stopped_at_its_tool_round_cap_folds_the_cap_failure() {
    let cap = "The run stopped at its tool round cap: 250 rounds (maxToolRounds)";
    let [call, result] = tool_round();
    let mut expected = running([user("list"), call.clone(), result.clone()]);
    expected.push(failure_row(cap));
    let entries = fold_transcript(
        &msgs([user("list"), call, result]),
        TurnTail::Ended(Some(cap)),
    );
    assert_eq!(unclocked(entries), unclocked(expected));
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

/// `message` with this provider usage and its stream marks.
fn used(mut message: Value, input: u64, cache_read: u64) -> Value {
    message["usage"] = json!({
        "input": input, "output": 10, "cacheRead": cache_read, "cacheWrite": 0, "totalTokens": 0,
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
    });
    message["timing"] = json!({ "firstTokenMs": 1, "lastTokenMs": 5 });
    message
}

/// The footer rows of `entries`, as their text.
fn footers(entries: &[ChatEntry]) -> Vec<String> {
    entries
        .iter()
        .filter_map(|entry| match entry {
            ChatEntry::TurnFooter(usage) => Some(usage.row_text()),
            _ => None,
        })
        .collect()
}

/// A turn that used tokens closes with its usage footer after its end
/// rows, the row the live pump pushes when the run ends; a failed tool
/// result counts, and a turn without tokens has no footer.
#[test]
fn a_turn_that_used_tokens_folds_its_footer_last() {
    let [call, mut result] = tool_round();
    result["isError"] = json!(true);
    let entries = ended([
        user("list"),
        used(call, 100, 300),
        result,
        used(answer("done"), 20, 380),
        user("again"),
        answer("ok"),
    ]);
    assert_eq!(
        footers(&entries),
        ["-- 1 tool, 1 failed - in 120 - out 20 - cache r 680 w 0 (85% hit)"]
    );
    let footer = entries
        .iter()
        .position(|entry| matches!(entry, ChatEntry::TurnFooter(_)))
        .expect("a footer");
    assert!(matches!(entries[footer + 1], ChatEntry::User { .. }));
}

/// The footer counts the calls their cards mark `x`: a bash script that
/// exited nonzero is no error result, and still counts as failed.
#[test]
fn a_nonzero_exit_counts_as_failed_as_its_card_marks_it() {
    let [call, mut result] = tool_round();
    result["details"] =
        json!({ "version": "bash@1", "steps": [], "end": { "kind": "finished", "status": 2 } });
    let entries = ended([
        user("list"),
        used(call, 100, 0),
        result,
        used(answer("done"), 20, 0),
    ]);
    assert!(entries.iter().any(
        |entry| matches!(entry, ChatEntry::Tool(card) if crate::tool_card::marks_failed(card))
    ));
    assert_eq!(footers(&entries), ["-- 1 tool, 1 failed - in 120 - out 20"]);
}

/// A tool round followed by another prompt may go on past it (a steering
/// prompt): its usage carries into the one footer of the turn that ends.
#[test]
fn a_tool_round_before_the_next_prompt_carries_its_usage_on() {
    let [call, result] = tool_round();
    let entries = ended([
        user("list"),
        used(call, 100, 0),
        result,
        user("and now?"),
        used(answer("done"), 20, 0),
    ]);
    assert_eq!(footers(&entries), ["-- 1 tool - in 120 - out 20"]);
    assert!(matches!(entries.last(), Some(ChatEntry::TurnFooter(_))));
}

/// The open run's newest turn folds no footer yet; its usage so far seeds
/// the live tally, without the in-flight partial its `message_end` adds.
#[test]
fn the_open_turn_hands_its_usage_to_the_live_tally() {
    let [call, result] = tool_round();
    let mut partial = used(answer("do"), 7, 0);
    partial.as_object_mut().expect("object").remove("timing");
    let (entries, open) = fold_turns(
        &msgs([user("list"), used(call, 100, 0), result, partial]),
        TurnTail::Running,
    );
    assert!(footers(&entries).is_empty());
    assert_eq!(open.row_text(), "-- 1 tool - in 100 - out 10");
}
