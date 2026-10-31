//! LAWS.bend H4.1, H4.7 and H4.8: the recoveries that help a weaker
//! model get unstuck. A length stop while the model still reasons is
//! retried with a length note; the same calls with the same results are
//! redirected with a note before they run a fifth time; tool calls leaked
//! as text are rebuilt, or noted and then stand as text. A reply with tool
//! calls runs them whatever its stop reason, but no call of a reply cut at
//! the output limit runs. A noted retry is a new request: it goes out at
//! once and does not spend `retry.maxRetries`.

use std::sync::{Arc, Mutex, PoisonError};
use std::time::Duration;

use eukhe_ai::providers::faux::{
    faux_assistant_message, faux_text, faux_thinking, faux_tool_call, FauxAssistantMessageOptions,
    FauxContentBlock, FauxResponseStep, RegisterFauxProviderOptions,
};
use eukhe_chord::json::JsonValue;
use eukhe_types::pi_ai::{Message, StopReason, UserContentBlock};

use super::run_bounds::tool;
use crate::harness::tests::chat_support::{
    all_entries, chat_setup, open_chat, ChatSetup, OpenChat,
};
use crate::harness::tests::support::{add_tool, context, describe_message};
use crate::harness::types::{InputSubmissionDraft, PartialRetryPolicy};
use crate::storage::MemoryStorage;
use crate::types::SubmissionStatus;

const ASK: &str = "go";

/// Thinking of 47 characters: the faux provider counts 12 output tokens.
const THINKING: &str = "The user wants a plan. First I check the files.";

/// The last message of each request the model got.
type Seen = Arc<Mutex<Vec<String>>>;

/// A step that records the last message of its request, then replies
/// with `content` and `stop_reason`.
fn reply(seen: &Seen, content: Vec<FauxContentBlock>, stop_reason: StopReason) -> FauxResponseStep {
    let seen = Arc::clone(seen);
    FauxResponseStep::factory(move |request, _, _, _| {
        seen.lock().unwrap_or_else(PoisonError::into_inner).push(
            request
                .messages()
                .last()
                .map_or_else(String::new, describe_message),
        );
        Ok(faux_assistant_message(
            content.clone(),
            FauxAssistantMessageOptions {
                stop_reason: Some(stop_reason),
                ..FauxAssistantMessageOptions::default()
            },
        ))
    })
}

fn tick(id: &str) -> FauxContentBlock {
    faux_tool_call("tick", serde_json::Map::new(), Some(id.to_owned()))
}

/// How a run settled: its status, reason and detail.
type Settled = (SubmissionStatus, Option<String>, Option<JsonValue>);

/// Run one input to its end: how it settled, and the messages of the
/// transcript (its system entries aside), as `describe_message` shows them.
async fn settle(setup: &ChatSetup) -> (Settled, Vec<String>) {
    let OpenChat { harness, root } = open_chat(Arc::new(MemoryStorage::new()), setup, None)
        .await
        .unwrap();
    harness.resume().unwrap();
    let settled = root
        .submit(InputSubmissionDraft::new(ASK), context())
        .await
        .unwrap()
        .wait(context())
        .await
        .unwrap()
        .into_record();
    let entries = all_entries(&root, context()).await.unwrap();
    harness.close(context()).await.unwrap();
    let lines = entries
        .iter()
        .flat_map(|entry| entry.model.iter().flatten())
        .filter_map(|message| match message {
            Message::System(_) => None,
            Message::User(_) | Message::Assistant(_) => Some(describe_message(message)),
            // An error result shows its text, not only `error`.
            Message::ToolResult(result) => Some(format!(
                "result:{}:{}:{}",
                result.tool_call_id,
                result.is_error,
                result
                    .content
                    .iter()
                    .map(|content| match content {
                        UserContentBlock::Text(text) => text.text.as_str(),
                        UserContentBlock::Image(_) => "[image]",
                    })
                    .collect::<String>()
            )),
        })
        .collect();
    (
        (
            settled.state.status(),
            settled.state.reason().map(str::to_owned),
            settled.state.detail().cloned(),
        ),
        lines,
    )
}

fn seen(seen: &Seen) -> Vec<String> {
    seen.lock().unwrap_or_else(PoisonError::into_inner).clone()
}

fn user(text: &str) -> String {
    format!("user:{text}")
}

/// The length note of `attempt`, the `row`th in a row, for a reply of
/// only [`THINKING`].
fn length_note(attempt: u64, row: u32) -> String {
    user(&format!(
        "Harness note, attempt {attempt}: your previous reply hit the 12-token output limit \
         while it was still reasoning. It gave no text and no tool call, so the harness \
         discarded it with every tool call that it planned. If you plan the whole task again \
         in your reasoning, you hit the same limit. Reason only about the next step, then call \
         its tool. For a large answer (a file, a document, a long text), write a minimal \
         working version first, then extend it with more edits in later turns. Length note \
         {row} of 3."
    ))
}

const NO_ANSWER: &str = "The model gave no answer: its reply (stop reason length) has no text \
                         and no tool call, only 47 characters of thinking";

#[tokio::test]
async fn a_length_stop_while_reasoning_is_retried_with_a_length_note_and_answers() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let requests = Seen::default();
    setup.faux.set_responses(vec![
        reply(&requests, vec![faux_thinking(THINKING)], StopReason::Length),
        reply(&requests, vec![faux_text("done")], StopReason::Stop),
    ]);
    assert_eq!(
        (settle(&setup).await, seen(&requests)),
        (
            (
                (SubmissionStatus::Done, None, None),
                vec![
                    user(ASK),
                    "assistant:".to_owned(),
                    "assistant:done".to_owned()
                ]
            ),
            vec![user(ASK), length_note(2, 1)]
        )
    );
}

#[tokio::test]
async fn length_stops_while_reasoning_fail_the_run_after_three_length_notes() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let requests = Seen::default();
    setup.faux.set_responses(
        (0..5)
            .map(|_| reply(&requests, vec![faux_thinking(THINKING)], StopReason::Length))
            .collect(),
    );
    let error = format!(
        "{NO_ANSWER}. The model hit the output limit while it was still reasoning after 3 length \
         notes in a row: use a different model or raise the model's max output tokens"
    );
    assert_eq!(
        (settle(&setup).await, seen(&requests)),
        (
            (
                (
                    SubmissionStatus::Unanswered,
                    Some("model_error".to_owned()),
                    Some(JsonValue::from(error))
                ),
                [user(ASK)]
                    .into_iter()
                    .chain((0..4).map(|_| "assistant:".to_owned()))
                    .collect()
            ),
            vec![
                user(ASK),
                length_note(2, 1),
                length_note(3, 2),
                length_note(4, 3)
            ]
        )
    );
    assert_eq!(setup.faux.get_pending_response_count(), 1);
}

/// The redirect note of `attempt` for the call `same` with `{}`, the
/// `row`th in a row.
fn redirect_note(attempt: u64, row: u32) -> String {
    user(&format!(
        "Harness note, attempt {attempt}: you made the same tool calls 5 times in a row, and \
         they gave the same results each time: `same` with `{{}}`. The harness did not run them \
         again. Do not make these calls with these arguments again in this turn. Use different \
         arguments, use a different tool, or give your answer with what you found. Redirect \
         note {row} of 2."
    ))
}

#[tokio::test]
async fn the_same_call_with_the_same_results_is_redirected_on_the_fifth_round_and_then_fails() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    add_tool(&setup.registry, tool("same", |_| "same".to_owned()), None).unwrap();
    let requests = Seen::default();
    setup.faux.set_responses(
        (0..8)
            .map(|round| {
                let call =
                    faux_tool_call("same", serde_json::Map::new(), Some(format!("c{round}")));
                reply(&requests, vec![call], StopReason::ToolUse)
            })
            .collect(),
    );
    let error = "The model made the same tool calls (same) with the same results 5 times in a \
                 row, after 2 redirect notes; the harness did not run them again";
    let mut logged = vec![user(ASK)];
    for round in 0..4 {
        logged.push("assistant:".to_owned());
        logged.push(format!("result:c{round}:false:same"));
    }
    logged.extend(["assistant:"; 3].map(str::to_owned));
    let ((status, reason, detail), lines) = settle(&setup).await;
    assert_eq!(
        ((status, reason, detail), lines, seen(&requests)),
        (
            (
                SubmissionStatus::Unanswered,
                Some("model_error".to_owned()),
                Some(JsonValue::from(error))
            ),
            logged,
            vec![
                user(ASK),
                "result:c0:same".to_owned(),
                "result:c1:same".to_owned(),
                "result:c2:same".to_owned(),
                "result:c3:same".to_owned(),
                redirect_note(2, 1),
                redirect_note(3, 2),
            ]
        )
    );
    assert_eq!(setup.faux.get_pending_response_count(), 1);
}

#[tokio::test]
async fn a_hermes_tool_call_leaked_as_text_is_rebuilt_and_runs() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    add_tool(&setup.registry, tool("tick", |n| format!("tick {n}")), None).unwrap();
    let requests = Seen::default();
    let leaked = "I will look.\n<tool_call>{\"name\": \"tick\", \"arguments\": {}}</tool_call>";
    setup.faux.set_responses(vec![
        reply(&requests, vec![faux_text(leaked)], StopReason::Stop),
        reply(&requests, vec![faux_text("done")], StopReason::Stop),
    ]);
    let ((status, reason, detail), lines) = settle(&setup).await;
    // The rebuilt call's id names the request's cutoff and attempt.
    let result = lines
        .iter()
        .find(|line| line.starts_with("result:leak_"))
        .cloned()
        .unwrap_or_default();
    assert!(result.ends_with(":false:tick 0"), "{result}");
    assert_eq!(
        ((status, reason, detail), lines, seen(&requests)),
        (
            (SubmissionStatus::Done, None, None),
            vec![
                user(ASK),
                "assistant:I will look.".to_owned(),
                result.clone(),
                "assistant:done".to_owned()
            ],
            vec![user(ASK), result.replacen(":false:", ":", 1)]
        )
    );
}

/// The leak note of `attempt`, the `row`th in a row.
fn leak_note(attempt: u64, row: u32) -> String {
    user(&format!(
        "Harness note, attempt {attempt}: your previous reply wrote a tool call as hermes markup \
         in its text, and the harness could not read it (the tool call has no name). No tool \
         ran. Make the call again through the tool-calling interface, with its arguments as one \
         JSON object that agrees with the schema of the tool. Do not write a tool call as text. \
         If you need no tool, give the answer as plain text. Leak note {row} of 2."
    ))
}

#[tokio::test]
async fn a_broken_leaked_tool_call_is_noted_and_then_stands_as_text_after_two_notes() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    add_tool(&setup.registry, tool("tick", |n| format!("tick {n}")), None).unwrap();
    let requests = Seen::default();
    let leaked = "<tool_call>{\"arguments\": {}}</tool_call>";
    setup.faux.set_responses(
        (0..4)
            .map(|_| reply(&requests, vec![faux_text(leaked)], StopReason::Stop))
            .collect(),
    );
    assert_eq!(
        (settle(&setup).await, seen(&requests)),
        (
            (
                (SubmissionStatus::Done, None, None),
                vec![
                    user(ASK),
                    format!("assistant:{leaked}"),
                    format!("assistant:{leaked}"),
                    format!("assistant:{leaked}"),
                ]
            ),
            vec![user(ASK), leak_note(2, 1), leak_note(3, 2)]
        )
    );
    assert_eq!(setup.faux.get_pending_response_count(), 1);
}

#[tokio::test]
async fn a_reply_with_stop_reason_stop_runs_its_tool_calls() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    add_tool(&setup.registry, tool("tick", |n| format!("tick {n}")), None).unwrap();
    let requests = Seen::default();
    setup.faux.set_responses(vec![
        reply(&requests, vec![tick("c0")], StopReason::Stop),
        reply(&requests, vec![faux_text("done")], StopReason::Stop),
    ]);
    assert_eq!(
        (settle(&setup).await, seen(&requests)),
        (
            (
                (SubmissionStatus::Done, None, None),
                vec![
                    user(ASK),
                    "assistant:".to_owned(),
                    "result:c0:false:tick 0".to_owned(),
                    "assistant:done".to_owned()
                ]
            ),
            vec![user(ASK), "result:c0:tick 0".to_owned()]
        )
    );
}

/// The `truncated` result of a call of `tick` in a reply of 4 output
/// tokens.
fn truncated(id: &str) -> String {
    format!(
        "result:{id}:true:<harness>\n[error] Tool tick was not run: the reply hit the 4-token \
         output limit, so its arguments may be cut. Make the call again with complete \
         arguments. For large content, write a minimal version first, then extend it with \
         edits.\n</harness>"
    )
}

#[tokio::test]
async fn no_call_of_a_reply_cut_at_the_output_limit_runs() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    add_tool(&setup.registry, tool("tick", |n| format!("tick {n}")), None).unwrap();
    let requests = Seen::default();
    setup.faux.set_responses(vec![
        reply(&requests, vec![tick("c0"), tick("c1")], StopReason::Length),
        reply(&requests, vec![tick("c2")], StopReason::ToolUse),
        reply(&requests, vec![faux_text("done")], StopReason::Stop),
    ]);
    // The tool's first run is the call of the next reply: `tick 0`.
    assert_eq!(
        (settle(&setup).await, seen(&requests)),
        (
            (
                (SubmissionStatus::Done, None, None),
                vec![
                    user(ASK),
                    "assistant:".to_owned(),
                    truncated("c0"),
                    truncated("c1"),
                    "assistant:".to_owned(),
                    "result:c2:false:tick 0".to_owned(),
                    "assistant:done".to_owned()
                ]
            ),
            vec![
                user(ASK),
                "result:c1:error".to_owned(),
                "result:c2:tick 0".to_owned()
            ]
        )
    );
}

/// A noted retry goes out at once, and the policy has no retries left. A
/// transient retry would wait a full-jitter draw of up to 10^12 ms (the
/// policy's base delay and cap): below the test's 60 s with a chance of
/// 6 in 10^8.
#[tokio::test]
async fn a_noted_retry_is_sent_at_once_and_spends_no_retry() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    setup.settings.update(|settings| {
        settings.retry = Some(PartialRetryPolicy {
            enabled: Some(true),
            max_retries: Some(0),
            base_delay_ms: Some(1e12),
            max_agent_delay_ms: Some(1e12),
        });
    });
    let requests = Seen::default();
    setup.faux.set_responses(vec![
        reply(&requests, vec![faux_thinking(THINKING)], StopReason::Length),
        reply(&requests, vec![faux_text("done")], StopReason::Stop),
    ]);
    let settled = tokio::time::timeout(Duration::from_secs(60), settle(&setup))
        .await
        .expect("the noted retry waited");
    assert_eq!(
        (settled, seen(&requests)),
        (
            (
                (SubmissionStatus::Done, None, None),
                vec![
                    user(ASK),
                    "assistant:".to_owned(),
                    "assistant:done".to_owned()
                ]
            ),
            vec![user(ASK), length_note(2, 1)]
        )
    );
}
