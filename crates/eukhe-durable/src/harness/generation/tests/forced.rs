//! A forced tool call (`bend/infer.bend` §2) through a whole run: every
//! request ends with the soft prompt, a retry sets the native forced choice
//! where the API has one, and a call missed by every request fails the run
//! with [`ForcedToolError::NotCalled`].

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_ai::providers::faux::{
    faux_assistant_message, faux_tool_call, FauxAssistantMessageOptions, FauxResponseStep,
    RegisterFauxProviderOptions,
};
use eukhe_ai::types::{AssistantMessage, StopReason, ToolChoice};
use eukhe_chord::json::to_json;
use eukhe_types::pi_ai::{TextContent, UserContentBlock};

use crate::harness::define::define_tool;
use crate::harness::generation::force::soft_prompt;
use crate::harness::generation::ForcedToolError;
use crate::harness::tests::chat_support::{chat_setup, open_chat, ChatSetup, OpenChat};
use crate::harness::tests::support::{add_tool, context, describe_message, empty_object_schema};
use crate::harness::types::{
    ConversationStreamOptions, ForcedTool, InputSubmissionDraft, ToolExecutionResult,
    ToolRegistration,
};
use crate::storage::MemoryStorage;
use crate::types::{SubmissionRecord, SubmissionStatus};

/// What each request asked: its tool choice and its last two messages.
type Seen = Arc<Mutex<Vec<(Option<ToolChoice>, Vec<String>)>>>;

/// A faux setup over an API that maps a native forced choice, with the
/// `lookup` tool and every generation forced to call it.
fn forced_setup(retries: u32) -> ChatSetup {
    let setup = chat_setup(RegisterFauxProviderOptions {
        api: Some("openai-completions".to_owned()),
        ..RegisterFauxProviderOptions::default()
    });
    let lookup = define_tool(ToolRegistration::new(
        "lookup",
        "lookup",
        empty_object_schema(),
        |_, _, _| async {
            Ok(ToolExecutionResult {
                output: Some(vec![UserContentBlock::Text(TextContent::new("found"))]),
                ..ToolExecutionResult::default()
            })
        },
    ));
    add_tool(&setup.registry, lookup, None).unwrap();
    setup.settings.update(|settings| {
        settings.stream = Some(ConversationStreamOptions {
            force_tool: Some(ForcedTool {
                tool: "lookup".to_owned(),
                retries,
            }),
            ..ConversationStreamOptions::default()
        });
    });
    setup
}

/// Answer `message` and record what the request asked; `then` runs first.
fn answer(
    seen: &Seen,
    message: AssistantMessage,
    then: impl Fn() + Send + Sync + 'static,
) -> FauxResponseStep {
    let seen = Arc::clone(seen);
    FauxResponseStep::factory(move |request, options, _, _| {
        let messages = request.messages();
        let last = messages[messages.len().saturating_sub(2)..]
            .iter()
            .map(describe_message)
            .collect();
        seen.lock().unwrap_or_else(PoisonError::into_inner).push((
            options.and_then(|options| options.tool_choice.clone()),
            last,
        ));
        then();
        Ok(message.clone())
    })
}

fn text(text: &str) -> AssistantMessage {
    faux_assistant_message(text, FauxAssistantMessageOptions::default())
}

/// Run one input to its end.
async fn settle(setup: &ChatSetup) -> SubmissionRecord {
    let OpenChat { harness, root } = open_chat(Arc::new(MemoryStorage::new()), setup, None)
        .await
        .unwrap();
    harness.resume().unwrap();
    let settled = root
        .submit(InputSubmissionDraft::new("go"), context())
        .await
        .unwrap()
        .wait(context())
        .await
        .unwrap()
        .into_record();
    harness.close(context()).await.unwrap();
    settled
}

#[tokio::test]
async fn a_missed_forced_call_retries_with_the_native_choice_until_called() {
    let setup = forced_setup(2);
    let seen = Seen::default();
    let call = faux_assistant_message(
        vec![faux_tool_call(
            "lookup",
            serde_json::Map::new(),
            Some("c1".to_owned()),
        )],
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::ToolUse),
            ..FauxAssistantMessageOptions::default()
        },
    );
    // The call lands: the next generation is no longer forced, as a
    // Director lifts its forced call once it is made.
    let settings = Arc::clone(&setup.settings);
    setup.faux.set_responses(vec![
        answer(&seen, text("no tool"), || {}),
        answer(&seen, call, move || {
            settings.update(|settings| settings.stream = None);
        }),
        answer(&seen, text("done"), || {}),
    ]);
    let settled = settle(&setup).await;
    let prompt = format!("user:{}", soft_prompt("lookup"));
    assert_eq!(
        (
            settled.state.status(),
            seen.lock().unwrap_or_else(PoisonError::into_inner).clone()
        ),
        (
            SubmissionStatus::Done,
            vec![
                (None, vec!["user:go".to_owned(), prompt.clone()]),
                (
                    Some(ToolChoice::Tool("lookup".to_owned())),
                    vec!["assistant:no tool".to_owned(), prompt],
                ),
                (
                    None,
                    vec!["assistant:".to_owned(), "result:c1:found".to_owned()],
                ),
            ],
        )
    );
}

#[tokio::test]
async fn a_forced_call_missed_by_every_request_fails_the_run() {
    let setup = forced_setup(1);
    let seen = Seen::default();
    setup.faux.set_responses(vec![
        answer(&seen, text("first"), || {}),
        answer(&seen, text("second"), || {}),
        answer(&seen, text("never sent"), || {}),
    ]);
    let settled = settle(&setup).await;
    let error = to_json(&ForcedToolError::NotCalled {
        tool: "lookup".to_owned(),
        attempts: 2,
    })
    .unwrap();
    let prompt = format!("user:{}", soft_prompt("lookup"));
    assert_eq!(
        (
            settled.state.status(),
            settled.state.reason(),
            settled.state.detail(),
            seen.lock().unwrap_or_else(PoisonError::into_inner).clone(),
        ),
        (
            SubmissionStatus::Unanswered,
            Some("forced_tool"),
            Some(&error),
            vec![
                (None, vec!["user:go".to_owned(), prompt.clone()]),
                (
                    Some(ToolChoice::Tool("lookup".to_owned())),
                    vec!["assistant:first".to_owned(), prompt],
                ),
            ],
        )
    );
}
