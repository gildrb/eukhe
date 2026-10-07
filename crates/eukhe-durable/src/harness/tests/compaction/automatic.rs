//! "background threshold compaction", "blocking threshold compaction", and
//! "overflow compaction".

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::json::{to_json, JsonValue};
use futures::FutureExt;

use super::{
    answer, compact, compaction_tasks, failure, gated, history, kinds, live, open, result, step,
    submission, submission_id, submit, summary, text, turn, user_text, Chat, OpenOptions,
    BACKGROUND, BLOCKING, MANUAL, OVERFLOW,
};
use crate::harness::events::{watch_events, AgentEvent};
use crate::harness::live::CompactionStatus;
use crate::harness::tests::chat_support::{all_entries, wait_for};
use crate::harness::tests::support::{add_hooks, add_section, compaction_task, context};
use crate::harness::tests::task_support::deferred;
use crate::harness::types::{
    CompactionDecision, CompactionHooks, CompactionPolicy, CompactionReason, CompactionResult,
    ConversationAbortOptions,
};
use crate::types::{AnyTaskRecord, SubmissionStatus, TaskId, TaskOutcome, TaskState};

fn declining() -> CompactionHooks {
    CompactionHooks {
        before_compact: Some(Arc::new(|_, _, _| {
            futures::future::ready(Ok(Some(CompactionDecision::Decline))).boxed()
        })),
    }
}

fn task_id(record: &AnyTaskRecord) -> TaskId<CompactionResult> {
    TaskId::from_number(record.id.get())
}

fn status(task: TaskId, blocking: bool) -> CompactionStatus {
    CompactionStatus {
        task_id: task,
        reason: CompactionReason::Threshold,
        blocking,
        attempt: 1,
        retry: None,
    }
}

fn threshold_input() -> JsonValue {
    JsonValue::parse(r#"{"reason":"threshold"}"#).unwrap()
}

/// Settled status, reason, and detail of an input.
async fn settled_input(
    handle: &crate::harness::SubmissionHandle,
) -> (SubmissionStatus, Option<String>, Option<JsonValue>) {
    let record = handle.wait(context()).await.unwrap();
    (
        record.state.status(),
        record.state.reason().map(str::to_owned),
        record.state.detail().cloned(),
    )
}

fn model_error(detail: Option<&str>) -> (SubmissionStatus, Option<String>, Option<JsonValue>) {
    (
        SubmissionStatus::Unanswered,
        Some("model_error".to_owned()),
        detail.map(JsonValue::from),
    )
}

// ─── Background threshold ─────────────────────────────────────────────────

#[tokio::test]
async fn starts_above_the_background_threshold_without_blocking_the_run_idle_waits_and_esc_ignore_it(
) {
    let chat = open(OpenOptions {
        context_window: Some(2000),
        ..OpenOptions::default()
    })
    .await;
    history(&chat).await;
    chat.set_policy(BACKGROUND);
    let gate = deferred();
    let reached = deferred();
    chat.faux
        .summary(gated(&gate, summary("SUMMARY"), Some(&reached)));
    turn(&chat, &text("u4", 100), &text("a4", 100)).await;
    reached.wait().await;
    let tasks = compaction_tasks(&chat).await;
    let task = &tasks[0];
    assert!(task.background);
    assert_eq!(task.input, threshold_input());
    assert_eq!(task.owner, None);
    assert_eq!(
        live(&chat).await.compactions,
        Some(vec![status(task.id, false)])
    );
    // Background work: neither conversation idle nor Esc waits for or stops it.
    chat.root.wait_for_idle(context()).await.unwrap();
    chat.root
        .abort(ConversationAbortOptions::default(), context())
        .await
        .unwrap();
    let record = chat
        .harness
        .get_task(task.id, context())
        .await
        .unwrap()
        .unwrap();
    assert!(matches!(record.state, TaskState::Running { .. }));
    gate.resolve(());
    let outcome = result(&chat, task_id(task)).await;
    assert!(matches!(outcome, TaskOutcome::Completed { .. }));
    assert_eq!(kinds(&chat.root).await.last().unwrap(), "pi.compaction");
    let messages = chat.root.context(context()).await.unwrap().messages;
    assert!(user_text(messages.first()).contains("SUMMARY"));
    chat.harness.close(context()).await.unwrap();
}

async fn does_not_start(policy: CompactionPolicy) {
    let chat = open(OpenOptions {
        context_window: Some(2000),
        ..OpenOptions::default()
    })
    .await;
    history(&chat).await;
    chat.set_policy(policy);
    turn(&chat, &text("u4", 100), &text("a4", 100)).await;
    assert!(compaction_tasks(&chat).await.is_empty());
    assert!(chat.faux.summary_requests().is_empty());
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn does_not_start_when_disabled() {
    does_not_start(CompactionPolicy {
        enabled: false,
        ..BACKGROUND
    })
    .await;
}

#[tokio::test]
async fn does_not_start_when_background_tokens_is_0() {
    does_not_start(CompactionPolicy {
        background_tokens: 0.0,
        ..BACKGROUND
    })
    .await;
}

#[tokio::test]
async fn does_not_start_when_there_is_no_cut() {
    does_not_start(CompactionPolicy {
        keep_recent_tokens: 100_000.0,
        ..BACKGROUND
    })
    .await;
}

#[tokio::test]
async fn does_not_start_while_another_compaction_is_listed() {
    let chat = open(OpenOptions {
        context_window: Some(2000),
        ..OpenOptions::default()
    })
    .await;
    history(&chat).await;
    let reached = deferred();
    chat.faux
        .summary(gated(&deferred(), summary("SUMMARY"), Some(&reached)));
    let manual = compact(&chat, None).await;
    reached.wait().await;
    chat.set_policy(BACKGROUND);
    turn(&chat, &text("u4", 100), &text("a4", 100)).await;
    assert_eq!(
        compaction_tasks(&chat)
            .await
            .iter()
            .map(|task| task.id)
            .collect::<Vec<_>>(),
        [manual.erase()]
    );
    chat.harness
        .abort_task(manual.erase(), context())
        .await
        .unwrap();
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn stops_through_abort_task_and_conversation_abort_with_background() {
    for stop_task in [true, false] {
        let chat = open(OpenOptions {
            context_window: Some(2000),
            ..OpenOptions::default()
        })
        .await;
        history(&chat).await;
        chat.set_policy(BACKGROUND);
        let reached = deferred();
        chat.faux
            .summary(gated(&deferred(), summary("SUMMARY"), Some(&reached)));
        turn(&chat, &text("u4", 100), &text("a4", 100)).await;
        reached.wait().await;
        let task = compaction_tasks(&chat).await.remove(0);
        if stop_task {
            chat.harness.abort_task(task.id, context()).await.unwrap();
        } else {
            chat.root
                .abort(ConversationAbortOptions { background: true }, context())
                .await
                .unwrap();
        }
        assert!(matches!(
            result(&chat, task_id(&task)).await,
            TaskOutcome::Aborted { .. }
        ));
        assert_eq!(live(&chat).await.compactions, None);
        chat.harness.close(context()).await.unwrap();
    }
}

// ─── Blocking threshold ───────────────────────────────────────────────────

fn sections_of(message: &eukhe_types::pi_ai::Message) -> Vec<(String, Option<String>)> {
    match message {
        eukhe_types::pi_ai::Message::System(system) => system
            .sections
            .iter()
            .flatten()
            .map(|(key, value)| (key.clone(), value.clone()))
            .collect(),
        _ => Vec::new(),
    }
}

#[tokio::test]
async fn waits_for_its_compaction_which_appends_the_summary_before_the_request() {
    let chat = open(OpenOptions {
        context_window: Some(1000),
        ..OpenOptions::default()
    })
    .await;
    history(&chat).await;
    chat.set_policy(BLOCKING);
    // A new section: preparation has a system entry to append, but must not
    // append it before the wait.
    add_section(
        &chat.setup.registry,
        "extra",
        |_, _| async { Ok(Some("EXTRA".to_owned())) }.boxed(),
        None,
        None,
    )
    .unwrap();
    let gate = deferred();
    let reached = deferred();
    chat.faux
        .summary(gated(&gate, summary("SUMMARY"), Some(&reached)));
    chat.faux.agent(answer("a4"));
    let input = submit(&chat, &text("u4", 200)).await;
    reached.wait().await;
    let child = compaction_tasks(&chat).await.remove(0);
    let generation = live(&chat).await.run.unwrap().task_id;
    assert_eq!(child.owner, Some(generation));
    assert!(!child.background);
    assert_eq!(child.input, threshold_input());
    let record = chat
        .harness
        .get_task(generation, context())
        .await
        .unwrap()
        .unwrap();
    let TaskState::Waiting { checkpoint, on, .. } = record.state else {
        panic!("the generation waits");
    };
    assert_eq!(on, [child.id]);
    assert_eq!(checkpoint["phase"], JsonValue::from("prepare"));
    assert_eq!(checkpoint["attempt"], JsonValue::from(1_u32));
    assert_eq!(checkpoint["compacted"], to_json(&child.id).unwrap());
    assert_eq!(
        live(&chat).await.compactions,
        Some(vec![status(child.id, true)])
    );
    // Nothing was appended before the wait.
    assert_eq!(kinds(&chat.root).await.last().unwrap(), "pi.user");
    gate.resolve(());
    assert_eq!(
        input.wait(context()).await.unwrap().state.status(),
        SubmissionStatus::Done
    );
    assert!(matches!(
        result(&chat, task_id(&child)).await,
        TaskOutcome::Completed { .. }
    ));
    let kinds = kinds(&chat.root).await;
    assert_eq!(
        kinds[kinds.len() - 3..],
        ["pi.compaction", "pi.system", "pi.assistant"]
    );
    let request = chat.faux.last_agent_messages();
    assert!(user_text(request.first()).contains("SUMMARY"));
    let systems: Vec<_> = request
        .iter()
        .filter(|message| matches!(message, eukhe_types::pi_ai::Message::System(_)))
        .collect();
    assert_eq!(systems.len(), 1);
    let sections = sections_of(systems[0]);
    assert!(sections.contains(&("preamble".to_owned(), Some("You are helpful.".to_owned()))));
    assert!(sections.contains(&(
        "extra".to_owned(),
        Some("<extra>\nEXTRA\n</extra>".to_owned())
    )));
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn sends_the_request_once_without_a_second_compaction_when_the_kept_part_is_still_above_the_threshold(
) {
    let chat = open(OpenOptions {
        context_window: Some(1000),
        ..OpenOptions::default()
    })
    .await;
    history(&chat).await;
    chat.set_policy(CompactionPolicy {
        keep_recent_tokens: 700.0,
        ..BLOCKING
    });
    chat.faux.summary(summary("SUMMARY"));
    turn(&chat, &text("u4", 400), "a4").await;
    assert_eq!(chat.faux.summary_requests().len(), 1);
    assert_eq!(
        kinds(&chat.root)
            .await
            .iter()
            .filter(|kind| *kind == "pi.compaction")
            .count(),
        1
    );
    chat.harness.close(context()).await.unwrap();
}

async fn sends_the_request_anyway(prepare: impl FnOnce(&Chat)) {
    let chat = open(OpenOptions {
        context_window: Some(1000),
        ..OpenOptions::default()
    })
    .await;
    history(&chat).await;
    chat.set_policy(BLOCKING);
    prepare(&chat);
    turn(&chat, &text("u4", 200), "a4").await;
    assert!(!kinds(&chat.root)
        .await
        .iter()
        .any(|kind| kind == "pi.compaction"));
    assert_eq!(
        user_text(chat.faux.last_agent_messages().first()),
        text("u1", 100)
    );
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn sends_the_request_anyway_when_its_compaction_declines() {
    sends_the_request_anyway(|chat| {
        add_hooks(&chat.setup.registry, compaction_task(), declining(), None).unwrap();
    })
    .await;
}

#[tokio::test]
async fn sends_the_request_anyway_when_its_compaction_fails() {
    sends_the_request_anyway(|chat| chat.faux.summary(failure("bad request"))).await;
}

#[tokio::test]
async fn sends_the_request_anyway_when_its_compaction_is_aborted_directly() {
    let chat = open(OpenOptions {
        context_window: Some(1000),
        ..OpenOptions::default()
    })
    .await;
    history(&chat).await;
    chat.set_policy(BLOCKING);
    let reached = deferred();
    chat.faux
        .summary(gated(&deferred(), summary("SUMMARY"), Some(&reached)));
    chat.faux.agent(answer("a4"));
    let input = submit(&chat, &text("u4", 200)).await;
    reached.wait().await;
    let child = compaction_tasks(&chat).await.remove(0);
    chat.harness.abort_task(child.id, context()).await.unwrap();
    assert_eq!(
        input.wait(context()).await.unwrap().state.status(),
        SubmissionStatus::Done
    );
    assert!(!kinds(&chat.root)
        .await
        .iter()
        .any(|kind| kind == "pi.compaction"));
    chat.harness.close(context()).await.unwrap();
}

/// Start an event stream recording every event.
pub(super) async fn record_events(
    chat: &Chat,
) -> (
    crate::harness::events::AgentEventStream,
    Arc<Mutex<Vec<AgentEvent>>>,
) {
    let events: Arc<Mutex<Vec<AgentEvent>>> = Arc::default();
    let stream = watch_events(&chat.harness, chat.id(), context())
        .await
        .unwrap();
    let sink = Arc::clone(&events);
    stream
        .start(Arc::new(move |batch, _cx| {
            sink.lock()
                .unwrap_or_else(PoisonError::into_inner)
                .extend(batch.iter().cloned());
            async { Ok(()) }.boxed()
        }))
        .unwrap();
    (stream, events)
}

pub(super) fn event_kinds(events: &Mutex<Vec<AgentEvent>>) -> Vec<&'static str> {
    events
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .iter()
        .map(AgentEvent::kind)
        .collect()
}

#[tokio::test]
async fn is_aborted_with_its_generation_by_esc_before_the_generations_abort_handler() {
    let chat = open(OpenOptions {
        context_window: Some(1000),
        ..OpenOptions::default()
    })
    .await;
    history(&chat).await;
    chat.set_policy(BLOCKING);
    let reached = deferred();
    chat.faux
        .summary(gated(&deferred(), summary("SUMMARY"), Some(&reached)));
    let (stream, events) = record_events(&chat).await;
    let input = submit(&chat, &text("u4", 200)).await;
    reached.wait().await;
    let child = compaction_tasks(&chat).await.remove(0);
    chat.root
        .abort(ConversationAbortOptions::default(), context())
        .await
        .unwrap();
    let (status, reason, _) = settled_input(&input).await;
    assert_eq!(
        (status, reason.as_deref()),
        (SubmissionStatus::Unanswered, Some("aborted"))
    );
    let record = chat
        .harness
        .get_task(child.id, context())
        .await
        .unwrap()
        .unwrap();
    assert!(matches!(
        record.state,
        TaskState::Terminal {
            outcome: TaskOutcome::Aborted { .. }
        }
    ));
    wait_for(|| async { event_kinds(&events).contains(&"run_end") }, 5000).await;
    let kinds = event_kinds(&events);
    let position = |kind: &str| kinds.iter().position(|candidate| *candidate == kind);
    assert!(position("compaction_end") < position("run_end"));
    stream.stop().await;
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn wins_over_a_background_compaction_still_in_flight_which_then_settles_stale() {
    let chat = open(OpenOptions {
        context_window: Some(2000),
        ..OpenOptions::default()
    })
    .await;
    history(&chat).await;
    chat.set_policy(BACKGROUND);
    let gate = deferred();
    let reached = deferred();
    chat.faux
        .summary(gated(&gate, summary("BACKGROUND"), Some(&reached)));
    turn(&chat, &text("u4", 100), &text("a4", 100)).await;
    reached.wait().await;
    let background = compaction_tasks(&chat).await.remove(0);
    chat.faux.summary(summary("BLOCKING"));
    turn(&chat, &text("u5", 1000), "a5").await;
    let messages = chat.root.context(context()).await.unwrap().messages;
    assert!(user_text(messages.first()).contains("BLOCKING"));
    gate.resolve(());
    let outcome = result(&chat, task_id(&background)).await;
    let record = submission(&chat, submission_id(&outcome))
        .await
        .status(context())
        .await
        .unwrap();
    assert_eq!(record.state.status(), SubmissionStatus::Unanswered);
    assert_eq!(record.state.reason(), Some("stale"));
    chat.harness.close(context()).await.unwrap();
}

// ─── Overflow ─────────────────────────────────────────────────────────────

const ENABLED: CompactionPolicy = CompactionPolicy {
    enabled: true,
    ..MANUAL
};

#[tokio::test]
async fn compacts_and_retries_with_the_same_attempt_leaving_the_error_out_of_the_retry() {
    let chat = open(OpenOptions::default()).await;
    history(&chat).await;
    chat.set_policy(ENABLED);
    chat.faux.summary(summary("SUMMARY"));
    let attempt: Arc<Mutex<Option<u64>>> = Arc::default();
    chat.faux.agent(failure(OVERFLOW));
    let (harness, id, seen) = (chat.harness.clone(), chat.id(), Arc::clone(&attempt));
    chat.faux.agent(step(move |_| {
        let (harness, seen) = (harness.clone(), Arc::clone(&seen));
        async move {
            let live: crate::harness::live::LiveState =
                super::doc(&harness, &crate::harness::live::LIVE_DOC, id)
                    .await
                    .unwrap_or_default();
            *seen.lock().unwrap_or_else(PoisonError::into_inner) =
                live.generation.map(|generation| generation.attempt);
            answer("fits")
        }
    }));
    let input = submit(&chat, &text("u4", 100)).await;
    assert_eq!(
        input.wait(context()).await.unwrap().state.status(),
        SubmissionStatus::Done
    );
    assert_eq!(
        *attempt.lock().unwrap_or_else(PoisonError::into_inner),
        Some(1)
    );
    let kinds = kinds(&chat.root).await;
    assert_eq!(
        kinds[kinds.len() - 5..],
        [
            "pi.user",
            "pi.assistant",
            "pi.compaction",
            "pi.system",
            "pi.assistant"
        ]
    );
    let compaction = all_entries(&chat.root, context())
        .await
        .unwrap()
        .into_iter()
        .find(|record| record.kind == "pi.compaction")
        .unwrap();
    assert_eq!(
        compaction.data,
        Some(JsonValue::parse(r#"{"reason":"overflow"}"#).unwrap())
    );
    let retry = chat.faux.last_agent_messages();
    assert!(user_text(retry.first()).contains("SUMMARY"));
    assert!(!retry.iter().any(|message| matches!(
        message,
        eukhe_types::pi_ai::Message::Assistant(assistant)
            if assistant.stop_reason == eukhe_types::pi_ai::StopReason::Error
    )));
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn fails_a_second_overflow_with_its_error_entry() {
    let chat = open(OpenOptions::default()).await;
    history(&chat).await;
    chat.set_policy(ENABLED);
    chat.faux.summary(summary("SUMMARY"));
    chat.faux.agent(failure(OVERFLOW));
    chat.faux.agent(failure(OVERFLOW));
    let input = submit(&chat, &text("u4", 100)).await;
    assert_eq!(settled_input(&input).await, model_error(Some(OVERFLOW)));
    let kinds = kinds(&chat.root).await;
    assert_eq!(
        kinds.iter().filter(|kind| *kind == "pi.compaction").count(),
        1
    );
    assert_eq!(kinds.last().unwrap(), "pi.assistant");
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn fails_without_compacting_when_compaction_is_disabled_even_for_a_retryable_looking_overflow(
) {
    let chat = open(OpenOptions::default()).await;
    history(&chat).await;
    chat.faux.agent(failure(&format!("overloaded: {OVERFLOW}")));
    let input = submit(&chat, &text("u4", 100)).await;
    let (status, reason, _) = settled_input(&input).await;
    assert_eq!(
        (status, reason.as_deref()),
        (SubmissionStatus::Unanswered, Some("model_error"))
    );
    assert_eq!(chat.faux.agent_requests().len(), 4);
    assert!(chat.faux.summary_requests().is_empty());
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn fails_after_a_blocking_threshold_compaction_in_the_same_generation() {
    let chat = open(OpenOptions {
        context_window: Some(1000),
        ..OpenOptions::default()
    })
    .await;
    history(&chat).await;
    chat.set_policy(BLOCKING);
    chat.faux.summary(summary("SUMMARY"));
    chat.faux.agent(failure(OVERFLOW));
    let input = submit(&chat, &text("u4", 200)).await;
    let (status, reason, _) = settled_input(&input).await;
    assert_eq!(
        (status, reason.as_deref()),
        (SubmissionStatus::Unanswered, Some("model_error"))
    );
    assert_eq!(chat.faux.summary_requests().len(), 1);
    chat.harness.close(context()).await.unwrap();
}

async fn fails_with_the_overflow_text(prepare: impl FnOnce(&Chat), requests: usize) {
    let chat = open(OpenOptions::default()).await;
    turn(&chat, &text("u1", 100), &text("a1", 100)).await;
    chat.set_policy(ENABLED);
    prepare(&chat);
    chat.faux.agent(failure(OVERFLOW));
    let input = submit(&chat, &text("u4", 100)).await;
    assert_eq!(settled_input(&input).await, model_error(Some(OVERFLOW)));
    assert_eq!(chat.faux.summary_requests().len(), requests);
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn fails_with_the_overflow_text_when_compaction_declines() {
    fails_with_the_overflow_text(
        |chat| {
            add_hooks(&chat.setup.registry, compaction_task(), declining(), None).unwrap();
        },
        0,
    )
    .await;
}

#[tokio::test]
async fn fails_with_the_overflow_text_when_compaction_fails() {
    fails_with_the_overflow_text(|chat| chat.faux.summary(failure("bad request")), 1).await;
}

// Classification finds no cut, so no compaction starts and the ordinary
// failure carries the text.
#[tokio::test]
async fn fails_with_the_overflow_text_when_compaction_cannot_cut() {
    fails_with_the_overflow_text(
        |chat| {
            chat.set_policy(CompactionPolicy {
                keep_recent_tokens: 100_000.0,
                ..ENABLED
            });
        },
        0,
    )
    .await;
}
