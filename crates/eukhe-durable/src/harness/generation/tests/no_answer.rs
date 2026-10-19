//! docs/harness.md H4.7: a message that ends the model's turn with no text
//! and no tool call (only thinking, or nothing) is no answer. It fails as a
//! noted model error: it is retried with a note while notes are left
//! (`MAX_NOTES`), whatever the retry policy, else the run fails with
//! `model_error`.

use std::sync::Arc;

use eukhe_ai::providers::faux::{
    faux_assistant_message, faux_text, faux_thinking, FauxAssistantMessageOptions,
    FauxResponseStep, RegisterFauxProviderOptions,
};
use eukhe_chord::json::JsonValue;
use eukhe_types::pi_ai::{AssistantContentBlock, Message, StopReason};

use crate::harness::generation::decide::MAX_NOTES;
use crate::harness::tests::chat_support::{
    all_entries, chat_setup, open_chat, ChatSetup, OpenChat,
};
use crate::harness::tests::support::context;
use crate::harness::types::{InputSubmissionDraft, PartialRetryPolicy};
use crate::storage::MemoryStorage;
use crate::types::{EntryRecord, SubmissionStatus};

const THINKING: &str = "The user wants a plan. First I check the files.";

/// What the harness writes for a reply of only [`THINKING`].
const NO_ANSWER: &str = "The model gave no answer: its reply (stop reason stop) has no text \
                         and no tool call, only 47 characters of thinking";

/// A reply that stops with only thinking: no text, no tool call.
fn thinking_only() -> FauxResponseStep {
    faux_assistant_message(
        vec![faux_thinking(THINKING)],
        FauxAssistantMessageOptions::default(),
    )
    .into()
}

fn answer() -> FauxResponseStep {
    faux_assistant_message(
        vec![faux_text("Here is the plan.")],
        FauxAssistantMessageOptions::default(),
    )
    .into()
}

fn retry(enabled: bool, max_retries: u32) -> PartialRetryPolicy {
    PartialRetryPolicy {
        enabled: Some(enabled),
        max_retries: Some(max_retries),
        base_delay_ms: Some(1.0),
        ..PartialRetryPolicy::default()
    }
}

/// The stop reason, error message and content of each assistant message
/// of the transcript, oldest first.
fn assistants(
    entries: &[EntryRecord],
) -> Vec<(StopReason, Option<String>, Vec<AssistantContentBlock>)> {
    entries
        .iter()
        .flat_map(|entry| entry.model.iter().flatten())
        .filter_map(|message| match message {
            Message::Assistant(message) => Some((
                message.stop_reason,
                message.error_message.clone(),
                message.content.clone(),
            )),
            Message::User(_) | Message::ToolResult(_) | Message::System(_) => None,
        })
        .collect()
}

/// The failed message a reply of only [`THINKING`] leaves in the transcript.
fn failed() -> (StopReason, Option<String>, Vec<AssistantContentBlock>) {
    (
        StopReason::Error,
        Some(NO_ANSWER.to_owned()),
        vec![faux_thinking(THINKING)],
    )
}

/// Run one input to its end: its status, reason and detail, and the
/// assistant messages of the transcript.
async fn settle(
    setup: &ChatSetup,
) -> (
    (SubmissionStatus, Option<String>, Option<JsonValue>),
    Vec<(StopReason, Option<String>, Vec<AssistantContentBlock>)>,
) {
    let OpenChat { harness, root } = open_chat(Arc::new(MemoryStorage::new()), setup, None)
        .await
        .unwrap();
    harness.resume().unwrap();
    let settled = root
        .submit(InputSubmissionDraft::new("plan it"), context())
        .await
        .unwrap()
        .wait(context())
        .await
        .unwrap()
        .into_record();
    let entries = all_entries(&root, context()).await.unwrap();
    harness.close(context()).await.unwrap();
    (
        (
            settled.state.status(),
            settled.state.reason().map(str::to_owned),
            settled.state.detail().cloned(),
        ),
        assistants(&entries),
    )
}

#[tokio::test]
async fn a_reply_of_only_thinking_is_retried_and_then_answers() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    setup.faux.set_responses(vec![thinking_only(), answer()]);
    setup
        .settings
        .update(|settings| settings.retry = Some(retry(true, 3)));
    assert_eq!(
        settle(&setup).await,
        (
            (SubmissionStatus::Done, None, None),
            vec![
                failed(),
                (StopReason::Stop, None, vec![faux_text("Here is the plan.")]),
            ]
        )
    );
    assert_eq!(setup.faux.state().call_count, 2);
}

/// The notes bound the noted retries, not `retry.maxRetries` (1 here).
#[tokio::test]
async fn replies_of_only_thinking_past_the_notes_fail_the_run_with_model_error() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let requests = usize::try_from(MAX_NOTES).unwrap() + 1;
    let mut responses: Vec<_> = (0..requests).map(|_| thinking_only()).collect();
    responses.push(answer());
    setup.faux.set_responses(responses);
    setup
        .settings
        .update(|settings| settings.retry = Some(retry(true, 1)));
    assert_eq!(
        settle(&setup).await,
        (
            (
                SubmissionStatus::Unanswered,
                Some("model_error".to_owned()),
                Some(JsonValue::from(NO_ANSWER))
            ),
            vec![failed(); requests]
        )
    );
    assert_eq!(setup.faux.get_pending_response_count(), 1);
}

/// A noted retry is a new request, not a transient error: a disabled
/// retry policy with no retries does not stop it.
#[tokio::test]
async fn a_reply_of_only_thinking_is_retried_with_a_note_when_the_retry_policy_is_disabled() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    setup.faux.set_responses(vec![thinking_only(), answer()]);
    setup
        .settings
        .update(|settings| settings.retry = Some(retry(false, 0)));
    assert_eq!(
        settle(&setup).await,
        (
            (SubmissionStatus::Done, None, None),
            vec![
                failed(),
                (StopReason::Stop, None, vec![faux_text("Here is the plan.")]),
            ]
        )
    );
    assert_eq!(setup.faux.state().call_count, 2);
}
