//! LAWS.bend H4: every run ends. A model that keeps calling tools
//! stops at the round cap; the same calls whose results change keep
//! running (the same calls with the same results get the repeat recovery
//! of H4.8, `recoveries.rs`); an abort ends a run stuck in a
//! `before_request` hook.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::Duration;

use eukhe_ai::providers::faux::{
    faux_assistant_message, faux_text, faux_tool_call, FauxAssistantMessageOptions,
    FauxResponseStep, RegisterFauxProviderOptions,
};
use eukhe_chord::json::JsonValue;
use eukhe_types::pi_ai::{StopReason, TextContent, UserContentBlock};
use futures::FutureExt;

use crate::harness::define::define_tool;
use crate::harness::tests::chat_support::{chat_setup, open_chat, ChatSetup, OpenChat};
use crate::harness::tests::support::{
    add_hooks, add_tool, context, empty_object_schema, generation_task,
};
use crate::harness::tests::task_support::deferred;
use crate::harness::types::{
    ConversationAbortOptions, GenerationHooks, InputSubmissionDraft, ToolExecutionResult,
    ToolRegistration,
};
use crate::storage::MemoryStorage;
use crate::types::{SubmissionRecord, SubmissionStatus};

/// A tool whose result is `text(n)` at its n-th call.
pub(super) fn tool(name: &str, text: fn(usize) -> String) -> Arc<ToolRegistration> {
    let calls = Arc::new(AtomicUsize::new(0));
    define_tool(ToolRegistration::new(
        name,
        name,
        empty_object_schema(),
        move |_, _, _| {
            let n = calls.fetch_add(1, Ordering::SeqCst);
            async move {
                Ok(ToolExecutionResult {
                    output: Some(vec![UserContentBlock::Text(TextContent::new(text(n)))]),
                    ..ToolExecutionResult::default()
                })
            }
        },
    ))
}

/// `rounds` answers that each call `name` with the same (empty) arguments.
fn calls(name: &str, rounds: usize) -> Vec<FauxResponseStep> {
    (0..rounds)
        .map(|round| {
            faux_assistant_message(
                vec![faux_tool_call(
                    name,
                    serde_json::Map::new(),
                    Some(format!("c{round}")),
                )],
                FauxAssistantMessageOptions {
                    stop_reason: Some(StopReason::ToolUse),
                    ..FauxAssistantMessageOptions::default()
                },
            )
            .into()
        })
        .collect()
}

/// How a run's input settled: its status, reason and detail.
fn settlement(record: &SubmissionRecord) -> (SubmissionStatus, Option<&str>, Option<&JsonValue>) {
    (
        record.state.status(),
        record.state.reason(),
        record.state.detail(),
    )
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
async fn a_run_that_keeps_calling_tools_fails_at_the_round_cap() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    add_tool(&setup.registry, tool("tick", |n| format!("tick {n}")), None).unwrap();
    setup.faux.set_responses(calls("tick", 10));
    setup
        .settings
        .update(|settings| settings.max_tool_rounds = Some(3));
    let settled = settle(&setup).await;
    let detail = JsonValue::from("The run stopped at its tool round cap: 3 rounds (maxToolRounds)");
    assert_eq!(
        settlement(&settled),
        (
            SubmissionStatus::Unanswered,
            Some("run_limit"),
            Some(&detail)
        )
    );
    assert_eq!(setup.faux.state().call_count, 3);
}

/// Calls that poll a job that makes progress are no repeat (H4.8): eight
/// rounds of the same call run, past the repeat cap, as their results
/// change.
#[tokio::test]
async fn the_same_calls_whose_results_change_keep_running() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    add_tool(&setup.registry, tool("tick", |n| format!("tick {n}")), None).unwrap();
    let mut responses = calls("tick", 8);
    responses.push(
        faux_assistant_message(
            vec![faux_text("done")],
            FauxAssistantMessageOptions::default(),
        )
        .into(),
    );
    setup.faux.set_responses(responses);
    let settled = settle(&setup).await;
    assert_eq!(settled.state.status(), SubmissionStatus::Done);
    assert_eq!(setup.faux.state().call_count, 9);
}

/// Esc reaches a run whose `before_request` hook waits forever without
/// looking at its signal (the wait of an `OptChat` lease, a flush, a
/// settled view): the phase driver drops the phase after its grace, so the
/// conversation abort returns and the run ends aborted.
#[tokio::test(start_paused = true)]
async fn an_abort_ends_a_run_stuck_in_a_request_hook() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let reached = deferred::<()>();
    let reach = reached.clone();
    add_hooks(
        &setup.registry,
        generation_task(),
        GenerationHooks {
            before_request: Some(Arc::new(move |_, _, _| {
                reach.resolve(());
                futures::future::pending().boxed()
            })),
            ..GenerationHooks::default()
        },
        None,
    )
    .unwrap();
    setup.faux.set_responses(calls("unused", 1));
    let OpenChat { harness, root } = open_chat(Arc::new(MemoryStorage::new()), &setup, None)
        .await
        .unwrap();
    harness.resume().unwrap();
    let submission = root
        .submit(InputSubmissionDraft::new("go"), context())
        .await
        .unwrap();
    reached.wait().await;
    tokio::time::timeout(
        Duration::from_secs(60),
        root.abort(ConversationAbortOptions::default(), context()),
    )
    .await
    .expect("the abort ends the hook's phase")
    .unwrap();
    let settled = submission.wait(context()).await.unwrap();
    assert_eq!(
        settlement(&settled),
        (SubmissionStatus::Unanswered, Some("aborted"), None)
    );
    assert_eq!(setup.faux.state().call_count, 0);
    harness.close(context()).await.unwrap();
}
