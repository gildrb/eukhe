//! "compaction outcomes".

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::json::JsonValue;
use eukhe_pi_ai::providers::faux::faux_tool_call;
use eukhe_types::pi_ai::{
    CacheRetention, JsonObject as PiJsonObject, Message, ModelThinkingLevel, StopReason,
    ThinkingLevel,
};
use futures::FutureExt;

use super::{
    answer, compact, failure, first_user_text, history, input_tokens, kinds, live, open, result,
    step, summary, text, text_tool, turn, user_text, with_stop, Chat, OpenOptions, MANUAL,
};
use crate::harness::provider::{ProviderState, PROVIDER_DOC};
use crate::harness::tests::chat_support::tools_named;
use crate::harness::tests::support::{add_hooks, add_tool, compaction_task, context};
use crate::harness::types::{
    AgentChange, CompactionDecision, CompactionHooks, CompactionPolicy, CompactionReason,
    CompactionRequest, CompactionResult, ConversationStreamOptions, FieldChange, ToolsChange,
};
use crate::session::SessionError;
use crate::types::TaskOutcome;

/// Hooks whose `before_compact` answers `decide()`.
fn before_compact<F>(decide: F) -> CompactionHooks
where
    F: Fn(&CompactionRequest) -> Result<Option<CompactionDecision>, SessionError>
        + Send
        + Sync
        + 'static,
{
    CompactionHooks {
        before_compact: Some(Arc::new(move |request, _api, _cx| {
            futures::future::ready(decide(request)).boxed()
        })),
    }
}

/// Assert a `{ status: "completed", result: {} }` outcome.
fn assert_nothing(outcome: &TaskOutcome<CompactionResult>) {
    assert_eq!(
        *outcome,
        TaskOutcome::Completed {
            result: CompactionResult::default()
        }
    );
}

fn failure_reason(outcome: &TaskOutcome<CompactionResult>) -> (String, Option<JsonValue>) {
    match outcome {
        TaskOutcome::Failed { error, .. } => (error.message.clone(), error.detail.clone()),
        other => panic!("not failed: {other:?}"),
    }
}

fn reason(reason: &str) -> JsonValue {
    JsonValue::parse(&format!(r#"{{"reason":"{reason}"}}"#)).unwrap()
}

#[tokio::test]
async fn completes_without_a_summary_when_there_is_nothing_to_compact() {
    let chat = open(OpenOptions::default()).await;
    turn(&chat, "hi", "hello").await;
    let outcome = result(&chat, compact(&chat, None).await).await;
    assert_nothing(&outcome);
    assert!(chat.faux.summary_requests().is_empty());
    assert_eq!(live(&chat).await.compactions, None);
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn asks_before_compact_the_first_decision_wins_a_throw_is_reported_and_skipped() {
    let chat = open(OpenOptions::default()).await;
    let seen: Arc<Mutex<Vec<CompactionRequest>>> = Arc::default();
    add_hooks(
        &chat.setup.registry,
        compaction_task(),
        before_compact(|_| Err(SessionError::error("hook broke"))),
        None,
    )
    .unwrap();
    let sink = Arc::clone(&seen);
    add_hooks(
        &chat.setup.registry,
        compaction_task(),
        before_compact(move |request| {
            sink.lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(request.clone());
            Ok(Some(CompactionDecision::Summary("FROM HOOK".to_owned())))
        }),
        None,
    )
    .unwrap();
    add_hooks(
        &chat.setup.registry,
        compaction_task(),
        before_compact(|_| Ok(Some(CompactionDecision::Decline))),
        None,
    )
    .unwrap();
    history(&chat).await;
    let outcome = result(&chat, compact(&chat, Some("why")).await).await;
    assert!(matches!(outcome, TaskOutcome::Completed { .. }));
    assert!(chat.faux.summary_requests().is_empty());
    let messages = chat
        .root
        .context(context(), crate::harness::types::ContextOptions::default())
        .await
        .unwrap()
        .messages;
    assert!(first_user_text(&messages).contains("<summary>\nFROM HOOK\n</summary>"));
    let reports = chat.setup.reports();
    assert_eq!(reports.len(), 1);
    assert_eq!(reports[0].to_string(), "hook broke");
    let compaction = seen.lock().unwrap_or_else(PoisonError::into_inner)[0].clone();
    assert_eq!(compaction.reason, CompactionReason::Manual);
    assert_eq!(compaction.instructions.as_deref(), Some("why"));
    assert_eq!(
        compaction
            .entries
            .iter()
            .map(|record| record.kind.as_str())
            .collect::<Vec<_>>(),
        [
            "pi.user",
            "pi.system",
            "pi.assistant",
            "pi.user",
            "pi.assistant"
        ]
    );
    assert_eq!(
        compaction
            .messages
            .iter()
            .filter(|message| !matches!(message, Message::System(_)))
            .map(|message| user_text(Some(message)))
            .collect::<Vec<_>>(),
        [
            text("u1", 100),
            text("a1", 100),
            text("u2", 100),
            text("a2", 100)
        ]
    );
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn completes_without_a_summary_when_a_hook_declines() {
    let chat = open(OpenOptions::default()).await;
    add_hooks(
        &chat.setup.registry,
        compaction_task(),
        before_compact(|_| Ok(Some(CompactionDecision::Decline))),
        None,
    )
    .unwrap();
    history(&chat).await;
    assert_nothing(&result(&chat, compact(&chat, None).await).await);
    assert!(chat.faux.summary_requests().is_empty());
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn fails_with_no_model_without_a_configured_model() {
    let chat = open(OpenOptions::default()).await;
    history(&chat).await;
    chat.root
        .configure(
            AgentChange {
                model: FieldChange::Clear,
                ..AgentChange::default()
            },
            context(),
        )
        .await
        .unwrap();
    let outcome = result(&chat, compact(&chat, None).await).await;
    assert_eq!(failure_reason(&outcome).1, Some(reason("no_model")));
    assert_eq!(live(&chat).await.compactions, None);
    chat.harness.close(context()).await.unwrap();
}

/// Input tokens a compaction added to the ledger.
async fn compaction_input(chat: &Chat) -> u64 {
    let before = input_tokens(chat).await;
    result(chat, compact(chat, None).await).await;
    input_tokens(chat).await - before
}

fn set_thinking(level: ModelThinkingLevel) -> AgentChange {
    AgentChange {
        thinking_level: FieldChange::Set(level),
        ..AgentChange::default()
    }
}

#[tokio::test]
async fn retries_a_retryable_error_with_the_pinned_request_and_counts_every_attempt_once() {
    let single = open(OpenOptions::default()).await;
    history(&single).await;
    single
        .root
        .configure(set_thinking(ModelThinkingLevel::High), context())
        .await
        .unwrap();
    single.faux.summary(summary("SUMMARY"));
    let once = compaction_input(&single).await;
    assert!(once > 0);
    single.harness.close(context()).await.unwrap();

    let chat = open(OpenOptions::default()).await;
    history(&chat).await;
    chat.root
        .configure(set_thinking(ModelThinkingLevel::High), context())
        .await
        .unwrap();
    chat.set_stream(ConversationStreamOptions {
        timeout_ms: Some(1234.0),
        deferred: Some(eukhe_pi_ai::types::DeferredRequest::Flag(true)),
        ..ConversationStreamOptions::default()
    });
    let root = chat.root.clone();
    let setup = Arc::clone(&chat.setup);
    chat.faux.summary(step(move |_| {
        let (root, setup) = (root.clone(), Arc::clone(&setup));
        async move {
            // Changed during the attempt: the retry still uses the pinned request.
            root.configure(set_thinking(ModelThinkingLevel::Low), context())
                .await
                .unwrap();
            setup.settings.update(|settings| {
                settings.stream = Some(ConversationStreamOptions {
                    timeout_ms: Some(1.0),
                    ..ConversationStreamOptions::default()
                });
            });
            failure("overloaded")
        }
    }));
    chat.faux.summary(summary("SUMMARY"));
    let before = input_tokens(&chat).await;
    let outcome = result(&chat, compact(&chat, None).await).await;
    assert!(matches!(outcome, TaskOutcome::Completed { .. }));
    let twice = input_tokens(&chat).await - before;
    assert_eq!(chat.faux.summary_requests().len(), 2);
    assert_eq!(twice, 2 * once);
    let provider: ProviderState = super::doc(&chat.harness, &PROVIDER_DOC, chat.id())
        .await
        .unwrap();
    for request in chat.faux.summary_requests() {
        let options = request.options.unwrap();
        assert_eq!(options.reasoning, Some(ThinkingLevel::High));
        assert_eq!(options.stream.request.timeout_ms, Some(1234.0));
        assert_eq!(options.stream.cache_retention, Some(CacheRetention::None));
        assert_eq!(
            options.stream.session_id.as_ref(),
            Some(&provider.session_id)
        );
        assert_eq!(options.deferred, None);
    }
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn adds_no_usage_when_a_hook_declines_or_supplies_the_summary() {
    for decision in [
        CompactionDecision::Decline,
        CompactionDecision::Summary("HOOK".to_owned()),
    ] {
        let chat = open(OpenOptions::default()).await;
        add_hooks(
            &chat.setup.registry,
            compaction_task(),
            before_compact(move |_| Ok(Some(decision.clone()))),
            None,
        )
        .unwrap();
        history(&chat).await;
        assert_eq!(compaction_input(&chat).await, 0);
        chat.harness.close(context()).await.unwrap();
    }
}

#[tokio::test]
async fn caps_max_tokens_at_the_models_output_limit_and_sends_no_tools() {
    let chat = open(OpenOptions::default()).await;
    add_tool(&chat.setup.registry, text_tool("read", ""), None).unwrap();
    chat.root
        .configure(
            AgentChange {
                tools: FieldChange::Set(ToolsChange::Exactly(tools_named(&chat.setup, &["read"]))),
                ..AgentChange::default()
            },
            context(),
        )
        .await
        .unwrap();
    history(&chat).await;
    chat.set_policy(CompactionPolicy {
        reserve_tokens: 2000.0,
        ..MANUAL
    });
    chat.faux.summary(summary("SUMMARY"));
    result(&chat, compact(&chat, None).await).await;
    let request = chat.faux.summary_requests()[0].clone();
    // 0.8 * 2000 = 1600, above the model's 900.
    assert_eq!(request.options.unwrap().stream.max_tokens, Some(900));
    assert_eq!(request.messages.len(), 2);
    assert!(!request
        .messages
        .iter()
        .any(|message| matches!(message, Message::System(system) if system.tools_added.is_some())));
    chat.harness.close(context()).await.unwrap();
}

async fn fails_with_model_error(
    response: eukhe_types::pi_ai::AssistantMessage,
    message: &str,
    requests: usize,
) {
    let chat = open(OpenOptions::default()).await;
    history(&chat).await;
    for _ in 0..3 {
        chat.faux.summary(response.clone());
    }
    let outcome = result(&chat, compact(&chat, None).await).await;
    assert_eq!(
        failure_reason(&outcome),
        (message.to_owned(), Some(reason("model_error")))
    );
    // The retry policy allows two retries after the first attempt.
    assert_eq!(chat.faux.summary_requests().len(), requests);
    assert_eq!(live(&chat).await.compactions, None);
    assert!(!kinds(&chat.root)
        .await
        .iter()
        .any(|kind| kind == "pi.compaction"));
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn fails_with_model_error_on_retries_run_out() {
    fails_with_model_error(failure("overloaded"), "Summarization failed: overloaded", 3).await;
}

#[tokio::test]
async fn fails_with_model_error_on_a_non_retryable_error() {
    fails_with_model_error(
        failure("bad request"),
        "Summarization failed: bad request",
        1,
    )
    .await;
}

#[tokio::test]
async fn fails_with_model_error_on_a_length_stop() {
    fails_with_model_error(
        with_stop("partial", StopReason::Length),
        "Summarization hit the token limit; the summary is incomplete",
        1,
    )
    .await;
}

#[tokio::test]
async fn fails_with_model_error_on_a_tool_call() {
    fails_with_model_error(
        with_stop(
            vec![faux_tool_call("read", PiJsonObject::new(), None)],
            StopReason::Stop,
        ),
        "Summarization attempted to call a tool",
        1,
    )
    .await;
}

#[tokio::test]
async fn fails_with_model_error_on_empty_text() {
    fails_with_model_error(answer("  "), "Summarization produced no text", 1).await;
}
