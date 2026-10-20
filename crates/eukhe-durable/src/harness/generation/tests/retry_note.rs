//! docs/harness.md H4.7: a retry after a noted reply never sends the
//! request that was cut. A model that loops on a request, as a greedy one
//! does every time, loops on the same request again; the retry's request
//! ends with a note that names the retry's attempt and what went wrong
//! (law `run_retry_sends_a_new_request`), and the run never logs that note
//! (law `run_note_is_never_logged`).

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_ai::providers::faux::{
    faux_assistant_message, faux_text, faux_thinking, FauxAssistantMessageOptions,
    FauxResponseStep, RegisterFauxProviderOptions,
};
use eukhe_chord::json::JsonValue;
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessageDiagnostic, Message, StopReason, UserContent,
};

use crate::harness::generation::decide::MAX_NOTES;
use crate::harness::generation::note::{NoteCause, RetryNote};
use crate::harness::tests::chat_support::{
    all_entries, chat_setup, open_chat, ChatSetup, OpenChat,
};
use crate::harness::tests::support::{context, describe_message};
use crate::harness::types::{ConversationStreamOptions, InputSubmissionDraft, PartialRetryPolicy};
use crate::storage::MemoryStorage;
use crate::types::SubmissionStatus;

const ASK: &str = "list the subreddits";

const ANSWER: &str = "- r/Bitcoin\n- r/ethereum\n- r/CryptoCurrency";

/// What the repetition guard reports for 200 lines of `- r/Bitcoin`.
const CUT: &str = "Provider stream repeating: the same line 64 times in a row: \"- r/Bitcoin\"";

/// Each request the model got, as its messages.
type Seen = Arc<Mutex<Vec<Vec<String>>>>;

/// Each request the model got, as its messages and its idle deadline.
type SeenIdle = Arc<Mutex<Vec<(Vec<String>, Option<f64>)>>>;

/// The line `- r/Bitcoin`, 200 times.
fn looped() -> Vec<AssistantContentBlock> {
    vec![faux_text("- r/Bitcoin\n".repeat(200))]
}

fn answer() -> Vec<AssistantContentBlock> {
    vec![faux_text(ANSWER)]
}

/// A model that decodes greedily: it replies `noted` to a request that
/// ends with a harness note, and `plain` to any other request.
fn greedy(
    seen: &Seen,
    plain: Vec<AssistantContentBlock>,
    noted: Vec<AssistantContentBlock>,
) -> FauxResponseStep {
    let seen = Arc::clone(seen);
    FauxResponseStep::factory(move |request, _, _, _| {
        let messages = request.messages();
        seen.lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(messages.iter().map(describe_message).collect());
        let has_note = messages.last().is_some_and(|message| match message {
            Message::User(user) => match &user.content {
                UserContent::Text(text) => text.starts_with("Harness note"),
                UserContent::Blocks(_) => false,
            },
            Message::Assistant(_) | Message::ToolResult(_) | Message::System(_) => false,
        });
        let content = if has_note {
            noted.clone()
        } else {
            plain.clone()
        };
        Ok(faux_assistant_message(
            content,
            FauxAssistantMessageOptions::default(),
        ))
    })
}

/// A logged message: what it says, its stop reason and its error.
type Logged = (String, Option<StopReason>, Option<String>);

fn user(text: &str) -> Logged {
    (format!("user:{text}"), None, None)
}

fn failed(error: &str) -> Logged {
    (
        "assistant:".to_owned(),
        Some(StopReason::Error),
        Some(error.to_owned()),
    )
}

/// The note of `attempt`, the `attempt - 1`th noted retry of a generation.
fn note(attempt: u64, cause: NoteCause) -> String {
    let spent = u32::try_from(attempt - 1).unwrap();
    format!(
        "user:{}",
        RetryNote {
            attempt,
            cause,
            spent
        }
        .text()
    )
}

fn repeated() -> NoteCause {
    NoteCause::Repeated {
        period: 1,
        line: "- r/Bitcoin".to_owned(),
    }
}

/// Run one input to its end: its status, reason and detail, and the
/// messages the transcript logs (its system entries aside).
async fn settle(
    setup: &ChatSetup,
    max_retries: u32,
) -> (
    (SubmissionStatus, Option<String>, Option<JsonValue>),
    Vec<Logged>,
) {
    setup.settings.update(|settings| {
        settings.retry = Some(PartialRetryPolicy {
            enabled: Some(true),
            max_retries: Some(max_retries),
            base_delay_ms: Some(1.0),
            ..PartialRetryPolicy::default()
        });
    });
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
            Message::Assistant(assistant) => Some((
                describe_message(message),
                Some(assistant.stop_reason),
                assistant.error_message.clone(),
            )),
            Message::User(_) | Message::ToolResult(_) => {
                Some((describe_message(message), None, None))
            }
            Message::System(_) => None,
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

/// The observed failure: the request that looped was sent again, looped
/// again, and failed the run. Now its retry ends with a note, which the
/// model answers.
#[tokio::test]
async fn a_retry_after_a_repeating_stream_ends_its_request_with_a_note_and_answers() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let seen = Seen::default();
    setup
        .faux
        .set_responses((0..4).map(|_| greedy(&seen, looped(), answer())).collect());
    assert_eq!(
        note(2, repeated()),
        "user:Harness note, attempt 2: your previous reply repeated the line \"- r/Bitcoin\" \
         until it was cut. Give the answer again; never list the same item twice."
    );
    let settled = settle(&setup, 3).await;
    assert_eq!(
        (
            settled,
            seen.lock().unwrap_or_else(PoisonError::into_inner).clone()
        ),
        (
            (
                (SubmissionStatus::Done, None, None),
                vec![
                    user(ASK),
                    failed(CUT),
                    (format!("assistant:{ANSWER}"), Some(StopReason::Stop), None),
                ]
            ),
            vec![
                vec![format!("user:{ASK}")],
                vec![format!("user:{ASK}"), note(2, repeated())],
            ]
        )
    );
}

/// A reply with no answer is noted the same way.
#[tokio::test]
async fn a_retry_after_no_answer_ends_its_request_with_a_note_and_answers() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let seen = Seen::default();
    let thinking = vec![faux_thinking("The user wants a list.")];
    setup.faux.set_responses(
        (0..4)
            .map(|_| greedy(&seen, thinking.clone(), answer()))
            .collect(),
    );
    assert_eq!(
        note(2, NoteCause::NoAnswer),
        "user:Harness note, attempt 2: your previous reply gave no text and no tool call. Give \
         the answer again, as text or as a tool call."
    );
    let no_answer = "The model gave no answer: its reply (stop reason stop) has no text and no \
                     tool call, only 22 characters of thinking";
    let settled = settle(&setup, 3).await;
    assert_eq!(
        (
            settled,
            seen.lock().unwrap_or_else(PoisonError::into_inner).clone()
        ),
        (
            (
                (SubmissionStatus::Done, None, None),
                vec![
                    user(ASK),
                    failed(no_answer),
                    (format!("assistant:{ANSWER}"), Some(StopReason::Stop), None),
                ]
            ),
            vec![
                vec![format!("user:{ASK}")],
                vec![format!("user:{ASK}"), note(2, NoteCause::NoAnswer)],
            ]
        )
    );
}

/// docs/harness.md H4.5: a stream that stalled is noted (M3). Its retry
/// is a new request: it ends with a note and has twice the idle deadline
/// the stream stalled under, so it does not stall the same way again. A
/// noted retry spends a note: with no transient retries left
/// (`retry.maxRetries` 0) the run still answers.
#[tokio::test]
async fn a_retry_after_a_stall_has_a_note_and_twice_the_idle_deadline() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let stall = "Provider stream stalled: no stream event for 2000ms";
    let seen = SeenIdle::default();
    let step = |stalled: bool| {
        let seen = Arc::clone(&seen);
        FauxResponseStep::factory(move |request, options, _, _| {
            let idle = options.and_then(|options| options.stream.request.stream_idle_timeout_ms);
            let messages = request.messages().iter().map(describe_message).collect();
            seen.lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push((messages, idle));
            if !stalled {
                return Ok(faux_assistant_message(
                    answer(),
                    FauxAssistantMessageOptions::default(),
                ));
            }
            let mut message = faux_assistant_message(
                Vec::<AssistantContentBlock>::new(),
                FauxAssistantMessageOptions {
                    stop_reason: Some(StopReason::Error),
                    error_message: Some(stall.to_owned()),
                    ..FauxAssistantMessageOptions::default()
                },
            );
            let mut details = serde_json::Map::new();
            details.insert("kind".to_owned(), "stream_stalled".into());
            details.insert("idleTimeoutMs".to_owned(), 2000.into());
            message.diagnostics = Some(vec![AssistantMessageDiagnostic {
                kind: "provider_stream_failure".to_owned(),
                timestamp: 0,
                error: None,
                details: Some(details),
            }]);
            Ok(message)
        })
    };
    setup.faux.set_responses(vec![step(true), step(false)]);
    setup.settings.update(|settings| {
        settings.stream = Some(ConversationStreamOptions {
            stream_idle_timeout_ms: Some(2000.0),
            ..ConversationStreamOptions::default()
        });
    });
    let stalled = NoteCause::Stalled { idle_ms: 2000 };
    assert_eq!(
        note(2, stalled.clone()),
        "user:Harness note, attempt 2: your previous reply produced no output for 2 s, so the \
         harness cut it. Reason briefly, then act: give the answer or call the tool of the next \
         step."
    );
    let settled = settle(&setup, 0).await;
    assert_eq!(
        (
            settled,
            seen.lock().unwrap_or_else(PoisonError::into_inner).clone()
        ),
        (
            (
                (SubmissionStatus::Done, None, None),
                vec![
                    user(ASK),
                    failed(stall),
                    (format!("assistant:{ANSWER}"), Some(StopReason::Stop), None),
                ]
            ),
            vec![
                (vec![format!("user:{ASK}")], Some(2000.0)),
                (vec![format!("user:{ASK}"), note(2, stalled)], Some(4000.0)),
            ]
        )
    );
}

/// A model that loops whatever the note: each retry names its own
/// attempt, so no two requests are the same, and the run fails once the
/// notes (`MAX_NOTES`) run out. A noted retry spends a note, not a retry:
/// the retry policy (2 retries) does not stop it.
#[tokio::test]
async fn every_retry_after_a_cut_sends_a_new_request_until_the_notes_run_out() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let seen = Seen::default();
    let requests = MAX_NOTES + 1;
    setup.faux.set_responses(
        (0..=requests)
            .map(|_| greedy(&seen, looped(), looped()))
            .collect(),
    );
    let settled = settle(&setup, 2).await;
    let mut logged = vec![user(ASK)];
    logged.extend((0..requests).map(|_| failed(CUT)));
    let mut sent = vec![vec![format!("user:{ASK}")]];
    sent.extend(
        (2..=u64::from(requests))
            .map(|attempt| vec![format!("user:{ASK}"), note(attempt, repeated())]),
    );
    assert_eq!(
        (
            settled,
            seen.lock().unwrap_or_else(PoisonError::into_inner).clone()
        ),
        (
            (
                (
                    SubmissionStatus::Unanswered,
                    Some("model_error".to_owned()),
                    Some(JsonValue::from(CUT))
                ),
                logged
            ),
            sent
        )
    );
}
