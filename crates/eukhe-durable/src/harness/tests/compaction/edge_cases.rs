//! "compaction edge cases" and "compaction pinning, silent overflow, and late
//! policy changes".

use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_pi_ai::providers::faux::{FauxModelDefinition, RegisterFauxProviderOptions};
use eukhe_types::pi_ai::{AssistantMessage, Message, StopReason};
use futures::FutureExt;

use super::automatic::{event_kinds, record_events};
use super::interactions::faulting;
use super::{
    answer, compact, compaction_tasks, doc, failure, first_user_text, gated, history, kinds, live,
    open, result, step, submission, submission_id, submit, summary, text, turn, user_text,
    with_stop, OpenOptions, BACKGROUND, BLOCKING, MANUAL, OVERFLOW,
};
use crate::errors::StorageError;
use crate::harness::events::{watch_events, AgentEvent};
use crate::harness::live::{CompactionStatus, LiveState, LIVE_DOC};
use crate::harness::tests::chat_support::open_chat;
use crate::harness::tests::chat_support::{all_entries, chat_setup, wait_for};
use crate::harness::tests::support::{add_hooks, add_section, compaction_task, context};
use crate::harness::tests::task_support::deferred;
use crate::harness::types::{
    AgentChange, CompactionDecision, CompactionHooks, CompactionPolicy, CompactionReason,
    CompactionResult, FieldChange, ModelRef,
};
use crate::harness::usage::{UsageState, USAGE_DOC};
use crate::session::tests::support::ControlledStorage;
use crate::session::SessionEnd;
use crate::types::{Storage, SubmissionStatus, TaskId, TaskOutcome};

fn task_id(id: crate::types::TaskId) -> TaskId<CompactionResult> {
    TaskId::from_number(id.get())
}

fn small() -> OpenOptions {
    OpenOptions {
        context_window: Some(1000),
        ..OpenOptions::default()
    }
}

fn medium() -> OpenOptions {
    OpenOptions {
        context_window: Some(2000),
        ..OpenOptions::default()
    }
}

#[tokio::test]
async fn keeps_the_one_compaction_limit_through_a_retry_backoff() {
    let chat = open(small()).await;
    history(&chat).await;
    chat.set_policy(BLOCKING);
    let asked = Arc::new(AtomicUsize::new(0));
    let count = Arc::clone(&asked);
    add_hooks(
        &chat.setup.registry,
        compaction_task(),
        CompactionHooks {
            before_compact: Some(Arc::new(move |_, _, _| {
                count.fetch_add(1, Ordering::SeqCst);
                futures::future::ready(Ok(Some(CompactionDecision::Decline))).boxed()
            })),
        },
        None,
    )
    .unwrap();
    chat.faux.agent(failure("overloaded"));
    turn(&chat, &text("u4", 200), "a4").await;
    // One blocking compaction, declined; the retried preparation, still above
    // the threshold, started no other.
    assert_eq!(asked.load(Ordering::SeqCst), 1);
    assert_eq!(chat.faux.agent_requests().len(), 5);
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn does_not_start_a_background_compaction_when_a_manual_one_was_admitted_during_preparation()
{
    let chat = open(medium()).await;
    history(&chat).await;
    chat.set_policy(BACKGROUND);
    let rendering = deferred();
    let release = deferred();
    let hold = Arc::new(AtomicBool::new(true));
    let (render, wait) = (rendering.clone(), release.clone());
    add_section(
        &chat.setup.registry,
        "slow",
        move |_, _| {
            let was_held = hold.swap(false, Ordering::SeqCst);
            let (render, released) = (render.clone(), wait.wait());
            async move {
                if was_held {
                    render.resolve(());
                    released.await;
                }
                Ok(Some("slow".to_owned()))
            }
            .boxed()
        },
        None,
        None,
    )
    .unwrap();
    let reached = deferred();
    chat.faux
        .summary(gated(&deferred(), summary("SUMMARY"), Some(&reached)));
    chat.faux.agent(answer("a4"));
    let input = submit(&chat, &text("u4", 100)).await;
    rendering.wait().await;
    let manual = compact(&chat, None).await;
    reached.wait().await;
    release.resolve(());
    assert_eq!(
        input.wait(context()).await.unwrap().state.status(),
        SubmissionStatus::Done
    );
    assert_eq!(
        compaction_tasks(&chat)
            .await
            .iter()
            .map(|task| task.id)
            .collect::<Vec<_>>(),
        [manual.erase()]
    );
    // A background compaction would have sent its own summarization request.
    assert_eq!(chat.faux.summary_requests().len(), 1);
    chat.harness
        .abort_task(manual.erase(), context())
        .await
        .unwrap();
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn starts_no_background_compaction_after_a_blocking_one_in_the_same_generation() {
    let chat = open(medium()).await;
    history(&chat).await;
    // Blocking at 1500, background at 200: the kept part stays above the
    // background threshold.
    chat.set_policy(CompactionPolicy {
        background_tokens: 1300.0,
        keep_recent_tokens: 400.0,
        ..BACKGROUND
    });
    chat.faux.summary(summary("SUMMARY"));
    turn(&chat, &text("u4", 1000), "a4").await;
    assert_eq!(chat.faux.summary_requests().len(), 1);
    assert!(compaction_tasks(&chat).await.is_empty());
    chat.harness.close(context()).await.unwrap();
}

// TS replaces `models.completeSimple` with a throwing function. Rust
// `Models` cannot throw there; the closest observable fault is an uncaught
// summarize error, here the negative `maxTokens` pinned from a policy
// changed after preparation, which the phase rejects.
#[tokio::test]
async fn sends_the_request_anyway_when_its_blocking_compaction_faults() {
    let chat = open(small()).await;
    history(&chat).await;
    chat.set_policy(BLOCKING);
    let changed = Arc::new(AtomicBool::new(false));
    let setup = Arc::clone(&chat.setup);
    add_section(
        &chat.setup.registry,
        "policy",
        move |_, _| {
            // Rendering runs after preparation read the policy; the compaction
            // reads this one.
            if !changed.swap(true, Ordering::SeqCst) {
                super::set_policy(&setup, faulting(BLOCKING));
            }
            async { Ok(Some("p".to_owned())) }.boxed()
        },
        None,
        None,
    )
    .unwrap();
    turn(&chat, &text("u4", 200), "a4").await;
    assert!(!kinds(&chat.root)
        .await
        .iter()
        .any(|kind| kind == "pi.compaction"));
    assert_eq!(live(&chat).await.compactions, None);
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn fails_an_overflow_run_with_its_text_when_its_compaction_is_aborted_directly_or_itself_overflows(
) {
    for abort in [true, false] {
        let chat = open(OpenOptions::default()).await;
        history(&chat).await;
        chat.set_policy(CompactionPolicy {
            enabled: true,
            ..MANUAL
        });
        let reached = deferred();
        if abort {
            chat.faux
                .summary(gated(&deferred(), summary("SUMMARY"), Some(&reached)));
        } else {
            chat.faux
                .summary(failure("prompt is too long for the summary"));
        }
        chat.faux.agent(failure(OVERFLOW));
        let input = submit(&chat, &text("u4", 100)).await;
        if abort {
            reached.wait().await;
            let child = compaction_tasks(&chat).await.remove(0);
            chat.harness.abort_task(child.id, context()).await.unwrap();
        }
        let settled = input.wait(context()).await.unwrap();
        assert_eq!(settled.state.status(), SubmissionStatus::Unanswered);
        assert_eq!(settled.state.reason(), Some("model_error"));
        assert_eq!(
            settled.state.detail(),
            Some(&eukhe_chord::json::JsonValue::from(OVERFLOW))
        );
        assert_eq!(live(&chat).await.compactions, None);
        chat.harness.close(context()).await.unwrap();
    }
}

#[tokio::test]
async fn treats_a_length_stop_as_an_ordinary_answer_not_an_overflow() {
    let chat = open(OpenOptions::default()).await;
    history(&chat).await;
    chat.set_policy(CompactionPolicy {
        enabled: true,
        ..MANUAL
    });
    chat.faux.agent(AssistantMessage {
        error_message: Some(OVERFLOW.to_owned()),
        ..with_stop("cut short", StopReason::Length)
    });
    let input = submit(&chat, "go").await;
    assert_eq!(
        input.wait(context()).await.unwrap().state.status(),
        SubmissionStatus::Done
    );
    assert!(chat.faux.summary_requests().is_empty());
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn orders_the_events_of_a_summary_placed_at_once() {
    let chat = open(OpenOptions::default()).await;
    history(&chat).await;
    let (stream, events) = record_events(&chat).await;
    chat.faux.summary(summary("SUMMARY"));
    result(&chat, compact(&chat, None).await).await;
    wait_for(
        || async { event_kinds(&events).contains(&"compaction_end") },
        5000,
    )
    .await;
    let kinds = event_kinds(&events);
    let end = kinds
        .iter()
        .position(|kind| *kind == "compaction_end")
        .unwrap();
    assert_eq!(
        kinds[end - 2..end + 3],
        [
            "message_start",
            "message_end",
            "compaction_end",
            "submission",
            "usage_changed"
        ]
    );
    stream.stop().await;
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn puts_compaction_start_last_in_the_batch_of_the_preparation_commit() {
    let chat = open(medium()).await;
    history(&chat).await;
    chat.set_policy(BACKGROUND);
    let batches: Arc<Mutex<Vec<Vec<&'static str>>>> = Arc::default();
    let stream = watch_events(&chat.harness, chat.id(), context())
        .await
        .unwrap();
    let sink = Arc::clone(&batches);
    stream
        .start(Arc::new(move |batch, _| {
            sink.lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(batch.iter().map(AgentEvent::kind).collect());
            async { Ok(()) }.boxed()
        }))
        .unwrap();
    // A new section makes the preparation commit append a system entry next
    // to the compaction's status.
    add_section(
        &chat.setup.registry,
        "extra",
        |_, _| async { Ok(Some("extra".to_owned())) }.boxed(),
        None,
        None,
    )
    .unwrap();
    chat.faux
        .summary(gated(&deferred(), summary("SUMMARY"), None));
    turn(&chat, &text("u4", 100), "a4").await;
    let find = || {
        batches
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .iter()
            .find(|batch| batch.contains(&"compaction_start"))
            .cloned()
    };
    wait_for(|| async { find().is_some() }, 5000).await;
    assert_eq!(
        find().unwrap(),
        ["message_start", "message_end", "compaction_start"]
    );
    stream.stop().await;
    let task = compaction_tasks(&chat).await.remove(0);
    chat.harness.abort_task(task.id, context()).await.unwrap();
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn keeps_a_background_summary_queued_through_a_retry_backoff_while_a_blocking_compaction_wins(
) {
    let chat = open(medium()).await;
    history(&chat).await;
    chat.set_policy(BACKGROUND);
    chat.set_retry(2, 300.0);
    let summary_gate = deferred();
    let summary_reached = deferred();
    chat.faux.summary(gated(
        &summary_gate,
        summary("BACKGROUND"),
        Some(&summary_reached),
    ));
    chat.faux.summary(summary("BLOCKING"));
    let failed = deferred();
    let signal = failed.clone();
    chat.faux.agent(step(move |_| {
        signal.resolve(());
        async { failure("overloaded") }
    }));
    chat.faux.agent(answer("a4"));
    let input = submit(&chat, &text("u4", 100)).await;
    failed.wait().await;
    summary_reached.wait().await;
    // During the backoff: the background summary queues, and the thresholds
    // drop so the retry blocks.
    wait_for(
        || async {
            live(&chat)
                .await
                .generation
                .is_some_and(|generation| generation.retry.is_some())
        },
        5000,
    )
    .await;
    let background = compaction_tasks(&chat).await.remove(0);
    summary_gate.resolve(());
    let queued = result(&chat, task_id(background.id)).await;
    let handle = submission(&chat, submission_id(&queued)).await;
    assert_eq!(
        handle.status(context()).await.unwrap().state.status(),
        SubmissionStatus::Queued
    );
    chat.set_policy(CompactionPolicy {
        reserve_tokens: 1500.0,
        keep_recent_tokens: 50.0,
        ..BACKGROUND
    });
    assert_eq!(
        input.wait(context()).await.unwrap().state.status(),
        SubmissionStatus::Done
    );
    assert!(first_user_text(&chat.faux.last_agent_messages()).contains("BLOCKING"));
    let settled = handle.wait(context()).await.unwrap();
    assert_eq!(settled.state.status(), SubmissionStatus::Unanswered);
    assert_eq!(settled.state.reason(), Some("stale"));
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn summarizes_the_previous_summary_in_a_second_compaction() {
    let chat = open(OpenOptions::default()).await;
    history(&chat).await;
    chat.faux.summary(summary("FIRST"));
    result(&chat, compact(&chat, None).await).await;
    turn(&chat, &text("u4", 100), &text("a4", 100)).await;
    turn(&chat, &text("u5", 100), &text("a5", 100)).await;
    chat.faux.summary(summary("SECOND"));
    result(&chat, compact(&chat, None).await).await;
    let prompt = user_text(chat.faux.summary_requests()[1].messages.get(1));
    assert!(prompt.starts_with(
        "<conversation>\n[User]: The conversation history before this point was compacted"
    ));
    assert!(prompt.contains("FIRST"));
    let messages = chat
        .root
        .context(context(), crate::harness::types::ContextOptions::default())
        .await
        .unwrap()
        .messages;
    assert!(first_user_text(&messages).contains("SECOND"));
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn leaves_no_usage_submission_or_summary_when_the_classifying_commit_fails_which_fails_the_harness(
) {
    let storage = ControlledStorage::new();
    let chat = open(OpenOptions {
        storage: Some(Arc::clone(&storage) as Arc<dyn Storage>),
        ..OpenOptions::default()
    })
    .await;
    history(&chat).await;
    let before = super::usage(&chat).await.models.get("faux/faux-1").copied();
    let failing = Arc::clone(&storage);
    chat.faux.summary(step(move |_| {
        failing.fail_next_commit(StorageError::failed(std::io::Error::other("disk gone")));
        async { summary("SUMMARY") }
    }));
    let id = compact(&chat, None).await;
    let end = chat.harness.closed().await;
    assert!(
        matches!(&end, SessionEnd::Failed { error } if error.to_string() == "disk gone"),
        "{end:?}"
    );
    chat.harness.close(context()).await.unwrap();
    // Nothing of the failed commit landed: the task is still live, without usage, entry, or submission.
    storage.reopen();
    assert!(storage
        .submission_by_request(chat.id(), &format!("compaction:{id}"), context())
        .await
        .unwrap()
        .is_none());
    let record = storage.task(id.erase(), context()).await.unwrap();
    assert_ne!(
        record.map(|record| record.state.status()),
        Some(crate::types::TaskStatus::Terminal)
    );
    let reopened = open_chat(Arc::clone(&storage) as Arc<dyn Storage>, &chat.setup, None)
        .await
        .unwrap();
    let usage: UsageState = doc(&reopened.harness, &USAGE_DOC, reopened.root.id())
        .await
        .expect("pi.usage exists");
    assert_eq!(usage.models.get("faux/faux-1").copied(), before);
    assert!(!kinds(&reopened.root)
        .await
        .iter()
        .any(|kind| kind == "pi.compaction"));
    reopened.harness.close(context()).await.unwrap();
}

// ─── Pinning, silent overflow, and late policy changes ────────────────────

#[tokio::test]
async fn keeps_the_pinned_model_through_a_retry_and_advances_the_live_attempt() {
    let setup = chat_setup(RegisterFauxProviderOptions {
        models: Some(
            ["faux-1", "faux-2"]
                .into_iter()
                .map(|id| FauxModelDefinition {
                    context_window: Some(100_000),
                    max_tokens: Some(900),
                    ..FauxModelDefinition::new(id)
                })
                .collect(),
        ),
        ..RegisterFauxProviderOptions::default()
    });
    let chat = open(OpenOptions {
        setup: Some(setup),
        ..OpenOptions::default()
    })
    .await;
    history(&chat).await;
    let attempt: Arc<Mutex<Option<u64>>> = Arc::default();
    let root = chat.root.clone();
    chat.faux.summary(step(move |_| {
        let root = root.clone();
        async move {
            // Switched during the attempt: the retry still uses the pinned model.
            root.configure(
                AgentChange {
                    model: FieldChange::Set(ModelRef {
                        provider: "faux".to_owned(),
                        model_id: "faux-2".to_owned(),
                    }),
                    ..AgentChange::default()
                },
                context(),
            )
            .await
            .unwrap();
            failure("overloaded")
        }
    }));
    let (harness, id, seen) = (chat.harness.clone(), chat.id(), Arc::clone(&attempt));
    chat.faux.summary(step(move |_| {
        let (harness, seen) = (harness.clone(), Arc::clone(&seen));
        async move {
            let state: LiveState = doc(&harness, &LIVE_DOC, id).await.unwrap_or_default();
            *seen.lock().unwrap_or_else(PoisonError::into_inner) = state
                .compactions
                .and_then(|list| list.first().map(|status| status.attempt));
            summary("SUMMARY")
        }
    }));
    assert!(matches!(
        result(&chat, compact(&chat, None).await).await,
        TaskOutcome::Completed { .. }
    ));
    assert_eq!(
        chat.faux
            .summary_requests()
            .iter()
            .map(|request| request.model.as_str())
            .collect::<Vec<_>>(),
        ["faux-1", "faux-1"]
    );
    assert_eq!(
        *attempt.lock().unwrap_or_else(PoisonError::into_inner),
        Some(2)
    );
    let models = super::usage(&chat).await.models;
    assert_eq!(
        models.keys().map(String::as_str).collect::<Vec<_>>(),
        ["faux/faux-1"]
    );
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn shows_a_late_joiner_a_compaction_that_is_summarizing() {
    let chat = open(OpenOptions::default()).await;
    history(&chat).await;
    let reached = deferred();
    chat.faux
        .summary(gated(&deferred(), summary("SUMMARY"), Some(&reached)));
    let id = compact(&chat, None).await;
    reached.wait().await;
    let stream = watch_events(&chat.harness, chat.id(), context())
        .await
        .unwrap();
    assert_eq!(
        stream.snapshot().compactions,
        [CompactionStatus {
            task_id: id.erase(),
            reason: CompactionReason::Manual,
            blocking: false,
            attempt: 1,
            retry: None,
        }]
    );
    stream.stop().await;
    chat.harness
        .abort_task(id.erase(), context())
        .await
        .unwrap();
    chat.harness.close(context()).await.unwrap();
}

async fn treats_silent_overflow_as_an_ordinary_answer(response: AssistantMessage) {
    let chat = open(OpenOptions {
        context_window: Some(300),
        ..OpenOptions::default()
    })
    .await;
    history(&chat).await;
    // Thresholds out of reach, so only overflow classification could compact.
    chat.set_policy(CompactionPolicy {
        enabled: true,
        reserve_tokens: -100_000.0,
        keep_recent_tokens: 150.0,
        background_tokens: 0.0,
    });
    chat.faux.agent(response);
    let input = submit(&chat, "go").await;
    assert_eq!(
        input.wait(context()).await.unwrap().state.status(),
        SubmissionStatus::Done
    );
    let last = all_entries(&chat.root, context())
        .await
        .unwrap()
        .pop()
        .unwrap();
    let Some(Message::Assistant(message)) = last.model.and_then(|model| model.into_iter().next())
    else {
        panic!("an assistant entry");
    };
    assert!(message.usage.input >= 300);
    assert!(chat.faux.summary_requests().is_empty());
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn treats_silent_overflow_as_an_ordinary_answer_a_stop_whose_input_exceeds_the_window() {
    treats_silent_overflow_as_an_ordinary_answer(answer("fine")).await;
}

#[tokio::test]
async fn treats_silent_overflow_as_an_ordinary_answer_a_length_stop_that_fills_the_window_without_output(
) {
    treats_silent_overflow_as_an_ordinary_answer(with_stop("", StopReason::Length)).await;
}

#[tokio::test]
async fn sends_the_request_when_a_blocking_compaction_finds_nothing_under_a_policy_changed_after_preparation(
) {
    let chat = open(small()).await;
    history(&chat).await;
    chat.set_policy(BLOCKING);
    let changed = Arc::new(AtomicBool::new(false));
    let setup = Arc::clone(&chat.setup);
    add_section(
        &chat.setup.registry,
        "policy",
        move |_, _| {
            // Rendering runs after preparation read the policy; the compaction
            // reads this one.
            if !changed.swap(true, Ordering::SeqCst) {
                super::set_policy(
                    &setup,
                    CompactionPolicy {
                        keep_recent_tokens: 100_000.0,
                        ..BLOCKING
                    },
                );
            }
            async { Ok(Some("p".to_owned())) }.boxed()
        },
        None,
        None,
    )
    .unwrap();
    turn(&chat, &text("u4", 200), "a4").await;
    assert!(compaction_tasks(&chat).await.is_empty());
    assert!(chat.faux.summary_requests().is_empty());
    assert!(!kinds(&chat.root)
        .await
        .iter()
        .any(|kind| kind == "pi.compaction"));
    chat.harness.close(context()).await.unwrap();
}
