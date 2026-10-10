//! "compaction recovery" and "blocked compaction".

use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::json::{to_json, JsonValue};
use eukhe_pi_ai::providers::faux::RegisterFauxProviderOptions;
use futures::FutureExt;

use super::automatic::{event_kinds, record_events};
use super::{
    answer, compact, failure, gated, history, kinds, live, open_scripted, result, script,
    set_policy, set_retry, submission, submission_id, submit, summary, text, usage, Chat, Script,
    BLOCKING, MANUAL, OVERFLOW,
};
use crate::harness::live::{CompactionStatus, LIVE_DOC};
use crate::harness::tests::chat_support::{
    all_entries, chat_setup, open_chat, wait_for, ChatSetup, OpenChat,
};
use crate::harness::tests::support::{add_hooks, compaction_task, context};
use crate::harness::tests::task_support::{aborted, deferred};
use crate::harness::types::{
    CompactionHooks, CompactionPolicy, CompactionReason, TaskBlockedReason, TaskInspectionState,
};
use crate::storage::sqlite::{open_native_sqlite_storage, NativeSqliteStorageOptions};
use crate::tasks::{define_task, TaskDefinition};
use crate::types::{Storage, SubmissionStatus, TaskOptions, TaskOutcome, TaskOwnership, TaskState};

async fn sqlite(path: &Path) -> Arc<dyn Storage> {
    Arc::new(
        open_native_sqlite_storage(path, NativeSqliteStorageOptions::default())
            .await
            .unwrap(),
    )
}

fn sqlite_path(directory: &tempfile::TempDir) -> PathBuf {
    directory.path().join("session.sqlite")
}

async fn reopen(path: &Path, setup: Arc<ChatSetup>, faux: Script) -> Chat {
    let OpenChat { harness, root } = open_chat(sqlite(path).await, &setup, None).await.unwrap();
    harness.resume().unwrap();
    Chat {
        harness,
        root,
        setup,
        faux,
    }
}

async fn first(path: &Path) -> Chat {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let chat = open_scripted(setup, sqlite(path).await, |setup| {
        set_policy(setup, MANUAL);
        set_retry(setup, 2, 1.0);
    })
    .await;
    history(&chat).await;
    chat
}

#[tokio::test]
async fn repeats_nothing_after_reopen_once_the_summary_is_placed() {
    let directory = tempfile::tempdir().unwrap();
    let path = sqlite_path(&directory);
    let mut chat = first(&path).await;
    chat.faux.summary(summary("SUMMARY"));
    result(&chat, compact(&chat, None).await).await;
    let entries = all_entries(&chat.root, context()).await.unwrap();
    let ledger = usage(&chat).await;
    chat.harness.close(context()).await.unwrap();
    chat = reopen(&path, chat.setup, chat.faux).await;
    chat.harness.wait_for_idle(context()).await.unwrap();
    assert_eq!(chat.faux.summary_requests().len(), 1);
    assert_eq!(all_entries(&chat.root, context()).await.unwrap(), entries);
    assert_eq!(usage(&chat).await, ledger);
    let inspection = chat.harness.inspect(context()).await.unwrap();
    assert!(inspection.tasks.is_empty());
    assert!(inspection.submissions.is_empty());
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn fails_an_overflow_run_with_its_text_when_its_compaction_fails_after_reopen() {
    let directory = tempfile::tempdir().unwrap();
    let path = sqlite_path(&directory);
    let mut chat = first(&path).await;
    chat.set_policy(CompactionPolicy {
        enabled: true,
        ..MANUAL
    });
    let reached = deferred();
    chat.faux
        .summary(gated(&deferred(), summary("SUMMARY"), Some(&reached)));
    chat.faux.agent(failure(OVERFLOW));
    let input = submit(&chat, &text("u4", 100)).await;
    reached.wait().await;
    let generation = live(&chat).await.run.unwrap().task_id;
    let record = chat
        .harness
        .get_task(generation, context())
        .await
        .unwrap()
        .unwrap();
    let TaskState::Waiting { checkpoint, .. } = record.state else {
        panic!("the generation waits");
    };
    assert_eq!(checkpoint["phase"], JsonValue::from("prepare"));
    assert_eq!(checkpoint["overflow"], JsonValue::from(OVERFLOW));
    chat.harness.close(context()).await.unwrap();
    chat = reopen(&path, chat.setup, chat.faux).await;
    chat.faux.summary(failure("bad request"));
    let settled = submission(&chat, input.id())
        .await
        .wait(context())
        .await
        .unwrap();
    assert_eq!(settled.state.status(), SubmissionStatus::Unanswered);
    assert_eq!(settled.state.reason(), Some("model_error"));
    assert_eq!(settled.state.detail(), Some(&JsonValue::from(OVERFLOW)));
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn reruns_select_and_its_hook_after_a_crash_in_select() {
    let directory = tempfile::tempdir().unwrap();
    let path = sqlite_path(&directory);
    let mut chat = first(&path).await;
    let calls = Arc::new(Mutex::new(0_usize));
    let reached = deferred();
    let (count, reach) = (Arc::clone(&calls), reached.clone());
    add_hooks(
        &chat.setup.registry,
        compaction_task(),
        CompactionHooks {
            before_compact: Some(Arc::new(move |_, _, hook_context| {
                let call = {
                    let mut calls = count.lock().unwrap_or_else(PoisonError::into_inner);
                    *calls += 1;
                    *calls
                };
                let signal = hook_context.abort_signal();
                let reach = reach.clone();
                async move {
                    if call == 1 {
                        reach.resolve(());
                        if let Some(signal) = signal {
                            return Err(aborted(&signal).await);
                        }
                    }
                    Ok(None)
                }
                .boxed()
            })),
        },
        None,
    )
    .unwrap();
    let id = compact(&chat, None).await;
    reached.wait().await;
    chat.harness.close(context()).await.unwrap();
    chat = reopen(&path, chat.setup, chat.faux).await;
    chat.faux.summary(summary("SUMMARY"));
    assert!(matches!(
        result(&chat, id).await,
        TaskOutcome::Completed { .. }
    ));
    assert_eq!(*calls.lock().unwrap_or_else(PoisonError::into_inner), 2);
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn resends_an_interrupted_summarization_once_and_counts_only_the_answered_attempt() {
    let directory = tempfile::tempdir().unwrap();
    let path = sqlite_path(&directory);
    let mut chat = first(&path).await;
    let reached = deferred();
    chat.faux
        .summary(gated(&deferred(), summary("SUMMARY"), Some(&reached)));
    let id = compact(&chat, None).await;
    reached.wait().await;
    let before = usage(&chat).await.models["faux/faux-1"];
    let record = chat.harness.get_task(id, context()).await.unwrap().unwrap();
    let TaskState::Running { checkpoint } = record.state else {
        panic!("summarizing");
    };
    assert_eq!(checkpoint["phase"], JsonValue::from("summarize"));
    chat.harness.close(context()).await.unwrap();
    chat = reopen(&path, chat.setup, chat.faux).await;
    chat.faux.summary(summary("SUMMARY"));
    assert!(matches!(
        result(&chat, id).await,
        TaskOutcome::Completed { .. }
    ));
    let requests = chat.faux.summary_requests();
    assert_eq!(requests.len(), 2);
    // The resent request is the same, except for message timestamps.
    let untimed = |messages: &[eukhe_types::pi_ai::Message]| {
        messages
            .iter()
            .map(|message| {
                let mut value = to_json(message).unwrap();
                if let JsonValue::Object(object) = &mut value {
                    std::sync::Arc::make_mut(object).remove("timestamp");
                }
                value
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(
        untimed(&requests[1].messages),
        untimed(&requests[0].messages)
    );
    let after = usage(&chat).await.models["faux/faux-1"];
    assert!(after.input > before.input);
    assert_eq!(after.output - before.output, 2);
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn resumes_a_retry_backoff_after_reopen() {
    let directory = tempfile::tempdir().unwrap();
    let path = sqlite_path(&directory);
    let mut chat = first(&path).await;
    let now = Arc::new(Mutex::new(chat.setup.now()));
    let clock = Arc::clone(&now);
    chat.setup
        .set_now(move || *clock.lock().unwrap_or_else(PoisonError::into_inner));
    chat.set_retry(2, 60_000.0);
    chat.faux.summary(failure("overloaded"));
    let id = compact(&chat, None).await;
    wait_for(
        || async {
            live(&chat)
                .await
                .compactions
                .and_then(|list| list.first().cloned())
                .is_some_and(|status| status.retry.is_some())
        },
        5000,
    )
    .await;
    let record = chat.harness.get_task(id, context()).await.unwrap().unwrap();
    let TaskState::Running { checkpoint } = record.state else {
        panic!("in backoff");
    };
    assert_eq!(checkpoint["phase"], JsonValue::from("retry"));
    assert_eq!(checkpoint["attempt"], JsonValue::from(1_u32));
    chat.harness.close(context()).await.unwrap();
    *now.lock().unwrap_or_else(PoisonError::into_inner) += 120_000.0;
    chat = reopen(&path, chat.setup, chat.faux).await;
    chat.faux.summary(summary("SUMMARY"));
    assert!(matches!(
        result(&chat, id).await,
        TaskOutcome::Completed { .. }
    ));
    assert_eq!(chat.faux.summary_requests().len(), 2);
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn keeps_a_generation_waiting_on_its_blocking_compaction_across_reopen() {
    let directory = tempfile::tempdir().unwrap();
    let path = sqlite_path(&directory);
    let mut chat = first(&path).await;
    let reached = deferred();
    chat.faux
        .summary(gated(&deferred(), summary("SUMMARY"), Some(&reached)));
    // The faux model window is 128k; this blocking threshold needs a small
    // context window.
    chat.set_policy(CompactionPolicy {
        reserve_tokens: 128_000.0 - 700.0,
        ..BLOCKING
    });
    let input = submit(&chat, &text("u4", 200)).await;
    reached.wait().await;
    chat.harness.close(context()).await.unwrap();
    chat = reopen(&path, chat.setup, chat.faux).await;
    chat.faux.summary(summary("SUMMARY"));
    chat.faux.agent(answer("a4"));
    assert_eq!(
        submission(&chat, input.id())
            .await
            .wait(context())
            .await
            .unwrap()
            .state
            .status(),
        SubmissionStatus::Done
    );
    let kinds = kinds(&chat.root).await;
    assert_eq!(
        kinds[kinds.len() - 3..],
        ["pi.compaction", "pi.system", "pi.assistant"]
    );
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn keeps_a_queued_summary_across_reopen_and_places_it_at_the_next_boundary() {
    let directory = tempfile::tempdir().unwrap();
    let path = sqlite_path(&directory);
    let mut chat = first(&path).await;
    let reached = deferred();
    chat.faux
        .agent(gated(&deferred(), answer("never"), Some(&reached)));
    let input = submit(&chat, "busy").await;
    reached.wait().await;
    chat.faux.summary(summary("SUMMARY"));
    let outcome = result(&chat, compact(&chat, None).await).await;
    chat.harness.close(context()).await.unwrap();
    chat = reopen(&path, chat.setup, chat.faux).await;
    chat.faux.agent(answer("answered"));
    assert_eq!(
        submission(&chat, input.id())
            .await
            .wait(context())
            .await
            .unwrap()
            .state
            .status(),
        SubmissionStatus::Done
    );
    assert_eq!(
        submission(&chat, submission_id(&outcome))
            .await
            .wait(context())
            .await
            .unwrap()
            .state
            .status(),
        SubmissionStatus::Done
    );
    chat.harness.close(context()).await.unwrap();
}

// ─── Blocked compaction ───────────────────────────────────────────────────

#[tokio::test]
async fn survives_reopen_blocked_and_is_orphaned_on_abort_with_its_status_removed() {
    let directory = tempfile::tempdir().unwrap();
    let path = sqlite_path(&directory);
    let setup = Arc::new(chat_setup(RegisterFauxProviderOptions::default()));
    let OpenChat { harness, root } = open_chat(sqlite(&path).await, &setup, None).await.unwrap();
    // A compaction stored by a newer version than this process registers, for
    // example after a downgrade.
    let newer = define_task(TaskDefinition::<JsonValue, JsonValue, JsonValue, ()>::new(
        "pi.compaction",
        2,
        |_| Ok(JsonValue::parse(r#"{"phase":"select"}"#).unwrap()),
        |_, _, _| async { Ok(()) },
    ));
    let root_id = root.id();
    let id = root
        .commit(
            move |tx| async move {
                let task_id = tx
                    .create_task(
                        newer.erase().as_definition_ref(),
                        JsonValue::parse(r#"{"reason":"manual"}"#).unwrap(),
                        TaskOptions {
                            ownership: TaskOwnership::Conversation,
                            conversation_id: None,
                            background: None,
                            abandon_on_restart: None,
                        },
                    )
                    .await?;
                let live = tx.doc(&LIVE_DOC, root_id).await?;
                let status = CompactionStatus {
                    task_id,
                    reason: CompactionReason::Manual,
                    blocking: false,
                    attempt: 1,
                    retry: None,
                };
                live.set("compactions", to_json(&vec![status])?)?;
                Ok(task_id)
            },
            context(),
        )
        .await
        .unwrap();
    harness.close(context()).await.unwrap();
    let OpenChat { harness, root } = open_chat(sqlite(&path).await, &setup, None).await.unwrap();
    harness.resume().unwrap();
    let faux = script(&setup);
    let chat = Chat {
        harness,
        root,
        setup,
        faux,
    };
    let (stream, events) = record_events(&chat).await;
    let inspection = chat.harness.inspect(context()).await.unwrap();
    let state = inspection
        .tasks
        .into_iter()
        .find(|task| task.record.id == id)
        .map(|task| task.state)
        .unwrap();
    assert!(matches!(
        state,
        TaskInspectionState::Blocked {
            reason: TaskBlockedReason::TaskTooOld,
            error: None
        }
    ));
    chat.harness.abort_task(id, context()).await.unwrap();
    let settled = chat.harness.wait_for_task(id, context()).await.unwrap();
    assert_eq!(
        settled.outcome,
        TaskOutcome::Orphaned {
            reason: "task_too_old".to_owned()
        }
    );
    assert_eq!(live(&chat).await.compactions, None);
    wait_for(
        || async { event_kinds(&events).contains(&"compaction_end") },
        5000,
    )
    .await;
    stream.stop().await;
    chat.harness.close(context()).await.unwrap();
}
