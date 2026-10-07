//! `describe("task runtime")`.

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::Duration;

use eukhe_chord::context::{AbortController, Context};
use eukhe_types::pi_ai::Message;
use futures::FutureExt;
use tokio::task::JoinHandle;

use super::{
    assert_rejects, complete, completed_outcome, error_name, held_gate, joined, lock, one_step,
    open_root, open_root_with, queue_blocker, reason, shared, start, text_of, with_signal,
    OpenedRoot, Shared, StepRuntime, Text,
};
use crate::documents::{DocDefinition, RewindableConversationDoc, SessionDoc};
use crate::harness::tests::support::{context, user};
use crate::harness::tests::task_support::{deferred, eventually, flush, OpenTasksOptions};
use crate::harness::Harness;
use crate::session::tests::support::{ControlledStorage, Gate};
use crate::session::{DocumentWatch, SessionError, SessionResult, WatchEnd, WatchListener};
use crate::types::{
    DocumentObserverExt, DocumentReaderExt, EntryDraft, RewindableFork, TaskOutcomeStatus,
};

static NOTES: SessionDoc<Text> = match SessionDoc::define(DocDefinition {
    kind: "test.task-notes",
    version: 1,
    initial: Text::default,
    migrate: None,
    checkpoint_when: None,
}) {
    Ok(token) => token,
    Err(_) => panic!("test.task-notes has a valid version"),
};

static ABSENT: SessionDoc<Text> = match SessionDoc::define(DocDefinition {
    kind: "test.task-absent",
    version: 1,
    initial: Text::default,
    migrate: None,
    checkpoint_when: None,
}) {
    Ok(token) => token,
    Err(_) => panic!("test.task-absent has a valid version"),
};

async fn write_notes(harness: &Harness, token: &'static SessionDoc<Text>, text: &'static str) {
    harness
        .commit(
            move |tx| async move {
                tx.doc(token, ()).await?.set("text", text)?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
}

#[tokio::test]
async fn rejects_runtime_operations_after_the_invocation_ends_and_stops_its_watches() {
    let captured: Shared<Option<StepRuntime>> = shared(None);
    let handler_context: Shared<Option<Context>> = shared(None);
    let watch_slot: Shared<Option<DocumentWatch>> = shared(None);
    let absent: Shared<Option<bool>> = shared(None);
    let delivered = shared(Vec::<String>::new());
    let watcher = one_step::<(), _, _>("test.watcher", {
        let (captured, handler_context, watch_slot, absent, delivered) = (
            captured.clone(),
            handler_context.clone(),
            watch_slot.clone(),
            absent.clone(),
            delivered.clone(),
        );
        move |_task, runtime: StepRuntime, cx: Context| {
            *lock(&captured) = Some(runtime.clone());
            *lock(&handler_context) = Some(cx.clone());
            let (watch_slot, absent, delivered) =
                (watch_slot.clone(), absent.clone(), delivered.clone());
            async move {
                let missing = runtime.watch_doc(&ABSENT, (), &cx).await?;
                *lock(&absent) = Some(missing.is_none());
                let watch = runtime
                    .watch_doc(&NOTES, (), &cx)
                    .await?
                    .expect("notes exist");
                let listener: WatchListener<_> = Arc::new(move |value, _ops, _cx| {
                    lock(&delivered).push(text_of(value).unwrap_or_else(|| "retired".to_owned()));
                    async { Ok(()) }.boxed()
                });
                watch.start(listener)?;
                *lock(&watch_slot) = Some(watch);
                complete(&runtime, (), &cx).await
            }
        }
    });
    let OpenedRoot { harness, root, .. } = open_root(&[watcher.erase()]).await;
    write_notes(&harness, &NOTES, "hello").await;
    let id = start(&root, &watcher).await;
    harness.resume().unwrap();
    harness.wait_for_task(id, context()).await.unwrap();
    assert_eq!(*lock(&absent), Some(true));
    // The watch stops when the step after the phase ends the invocation; later commits deliver nothing.
    let watch = lock(&watch_slot).clone().expect("the handler watched");
    assert_eq!(watch.closed().await, WatchEnd::Stopped);
    write_notes(&harness, &NOTES, "after").await;
    flush().await;
    assert!(lock(&delivered).is_empty());
    let runtime = lock(&captured).clone().expect("the handler ran");
    let ended = "invocation has ended";
    assert_rejects(
        runtime
            .commit(|_tx, _current| async { Ok(None) }, context())
            .await,
        ended,
    );
    assert_rejects(runtime.memo::<i64>("x", context()).await, ended);
    assert_rejects(runtime.memo_or("x", &1, context()).await, ended);
    assert_rejects(runtime.sleep(0.0, context()).await, ended);
    assert_rejects(runtime.watch_doc(&NOTES, (), context()).await, ended);
    // The handler's own context is cancelled by now; the ended invocation still wins.
    let handler_context = lock(&handler_context).clone().expect("the handler ran");
    assert_rejects(runtime.agent(&handler_context).await, ended);
    assert_rejects(runtime.now(), ended);
    assert_rejects(runtime.report(SessionError::error("late")), ended);
    harness.close(context()).await.unwrap();
}

static RUNTIME_NOTES: RewindableConversationDoc<Text> = match RewindableConversationDoc::define(
    DocDefinition {
        kind: "test.runtime-notes",
        version: 1,
        initial: Text::default,
        migrate: None,
        checkpoint_when: None,
    },
    RewindableFork::AsOf,
) {
    Ok(token) => token,
    Err(_) => panic!("test.runtime-notes has a valid version"),
};

/// What the reader saw: `[snapshot, snapshotAsOf, entries at first, messages at second, now]`.
type ReaderSeen = (Option<String>, Option<String>, usize, usize, f64);

#[tokio::test]
async fn reads_committed_documents_and_context_through_the_runtime_and_forwards_the_clock_and_reports(
) {
    let captured: Shared<Option<StepRuntime>> = shared(None);
    let seen: Shared<Option<ReaderSeen>> = shared(None);
    let reader = one_step::<(), _, _>("test.reader", {
        let (captured, seen) = (captured.clone(), seen.clone());
        move |_task, runtime: StepRuntime, cx: Context| {
            *lock(&captured) = Some(runtime.clone());
            let seen = seen.clone();
            async move {
                let conversation = runtime.conversation_id();
                let view = runtime.context(conversation, &cx, None).await?;
                let ids: Vec<_> = view.entries.iter().map(|entry| entry.id).collect();
                let (first, second) = (ids[0], ids[1]);
                let current = text_of(runtime.snapshot(&RUNTIME_NOTES, conversation, &cx).await?);
                let as_of = text_of(
                    runtime
                        .snapshot_as_of(&RUNTIME_NOTES, conversation, first, &cx)
                        .await?,
                );
                let entries = runtime
                    .context(conversation, &cx, Some(first))
                    .await?
                    .entries
                    .len();
                let messages = runtime
                    .context(conversation, &cx, Some(second))
                    .await?
                    .messages
                    .len();
                let now = runtime.now()?;
                *lock(&seen) = Some((current, as_of, entries, messages, now));
                runtime.report(SessionError::error("reported"))?;
                complete(&runtime, (), &cx).await
            }
        }
    });
    let OpenedRoot {
        harness,
        root,
        reports,
        ..
    } = open_root_with(
        Arc::new(crate::storage::MemoryStorage::new()),
        &[reader.erase()],
        OpenTasksOptions {
            now: Some(Arc::new(|| 1234.0)),
            ..OpenTasksOptions::default()
        },
    )
    .await;
    let root_id = root.id();
    for text in ["one", "two"] {
        root.commit(
            move |tx| async move {
                tx.doc(&RUNTIME_NOTES, root_id).await?.set("text", text)?;
                tx.append_entry(
                    root_id,
                    EntryDraft {
                        model: Some(vec![Message::User(user(text))]),
                        ..EntryDraft::new("message")
                    },
                )
                .await?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    }
    let id = start(&root, &reader).await;
    harness.resume().unwrap();
    harness.wait_for_task(id, context()).await.unwrap();
    assert_eq!(
        lock(&seen).take(),
        Some((Some("two".to_owned()), Some("one".to_owned()), 1, 2, 1234.0))
    );
    let reported: Vec<String> = reports.all().iter().map(ToString::to_string).collect();
    assert_eq!(reported, ["reported"]);
    // The step after the phase ends the invocation.
    flush().await;
    let captured = lock(&captured).clone().expect("the handler ran");
    assert_rejects(
        captured.snapshot(&RUNTIME_NOTES, root_id, context()).await,
        "invocation has ended",
    );
    assert_rejects(
        captured.context(root_id, context(), None).await,
        "invocation has ended",
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn orders_runtime_commits_against_the_step_one_queued_before_it_lands_one_after_it_rejects() {
    let storage = ControlledStorage::new();
    let before: Shared<Option<JoinHandle<SessionResult<()>>>> = shared(None);
    let after: Shared<Option<JoinHandle<SessionResult<()>>>> = shared(None);
    let held: Shared<Option<Gate>> = shared(None);
    let harness_ref: Shared<Option<Harness>> = shared(None);
    let detached = one_step::<String, _, _>("test.detached", {
        let (storage, before, after, held, harness_ref) = (
            Arc::clone(&storage),
            before.clone(),
            after.clone(),
            held.clone(),
            harness_ref.clone(),
        );
        move |_task, runtime: StepRuntime<String>, _cx: Context| {
            // Hold the line, queue a commit without awaiting it, and return; the step queues behind that commit.
            *lock(&held) = Some(storage.hold_commits());
            let harness = lock(&harness_ref).take().expect("the Harness is open");
            queue_blocker(&harness, runtime.conversation_id());
            *lock(&before) = Some(tokio::spawn(complete(
                &runtime,
                "before".to_owned(),
                context(),
            )));
            // Queued after the handler returned, so after the step.
            let after = after.clone();
            drop(tokio::spawn(async move {
                tokio::task::yield_now().await;
                *lock(&after) = Some(tokio::spawn(complete(
                    &runtime,
                    "after".to_owned(),
                    context(),
                )));
            }));
            async { Ok(()) }
        }
    });
    let OpenedRoot { harness, root, .. } = open_root_with(
        storage.clone(),
        &[detached.erase()],
        OpenTasksOptions::default(),
    )
    .await;
    *lock(&harness_ref) = Some(harness.clone());
    let id = start(&root, &detached).await;
    harness.resume().unwrap();
    held_gate(&held).await;
    eventually(|| std::future::ready(lock(&after).is_some())).await;
    lock(&held).as_ref().expect("held").release();
    let before = lock(&before).take().expect("queued before");
    joined(before).await.unwrap();
    assert_eq!(
        super::outcome(&harness, id).await,
        completed_outcome(&"before")
    );
    let after = lock(&after).take().expect("queued after");
    let error = joined(after)
        .await
        .expect_err("the step ended the invocation");
    let message = error.to_string();
    assert!(
        message.contains("invocation has ended") || message.contains("is terminal"),
        "{message}"
    );
    harness.close(context()).await.unwrap();
}

static LATE_NOTES: SessionDoc<Text> = match SessionDoc::define(DocDefinition {
    kind: "test.late-watch",
    version: 1,
    initial: Text::default,
    migrate: None,
    checkpoint_when: None,
}) {
    Ok(token) => token,
    Err(_) => panic!("test.late-watch has a valid version"),
};

#[tokio::test]
async fn stops_a_watch_whose_acquisition_finishes_after_the_invocation_ended() {
    let storage = ControlledStorage::new();
    let watching: Shared<Option<JoinHandle<SessionResult<Option<DocumentWatch>>>>> = shared(None);
    let held: Shared<Option<Gate>> = shared(None);
    let harness_ref: Shared<Option<Harness>> = shared(None);
    let late = one_step::<(), _, _>("test.late-watch", {
        let (storage, watching, held, harness_ref) = (
            Arc::clone(&storage),
            watching.clone(),
            held.clone(),
            harness_ref.clone(),
        );
        move |_task, runtime: StepRuntime, _cx: Context| {
            *lock(&held) = Some(storage.hold_commits());
            let harness = lock(&harness_ref).take().expect("the Harness is open");
            queue_blocker(&harness, runtime.conversation_id());
            // Starts after the handler returned, so its line job queues behind the step that ends the invocation.
            let watching = watching.clone();
            drop(tokio::spawn(async move {
                tokio::task::yield_now().await;
                *lock(&watching) =
                    Some(tokio::spawn(runtime.watch_doc(&LATE_NOTES, (), context())));
            }));
            async { Ok(()) }
        }
    });
    let OpenedRoot { harness, root, .. } = open_root_with(
        storage.clone(),
        &[late.erase()],
        OpenTasksOptions::default(),
    )
    .await;
    *lock(&harness_ref) = Some(harness.clone());
    write_notes(&harness, &LATE_NOTES, "x").await;
    let id = start(&root, &late).await;
    harness.resume().unwrap();
    held_gate(&held).await;
    eventually(|| std::future::ready(lock(&watching).is_some())).await;
    lock(&held).as_ref().expect("held").release();
    let watching = lock(&watching).take().expect("the watch started");
    assert_rejects(joined(watching).await, "invocation has ended");
    assert_eq!(
        super::outcome(&harness, id).await.status(),
        TaskOutcomeStatus::Faulted
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test(start_paused = true)]
async fn sleeps_until_the_harness_clock_reaches_the_deadline_rechecking_after_each_timer() {
    let clock = Arc::new(AtomicU64::new(1_000_f64.to_bits()));
    let woke = deferred::<()>();
    let sleeper = one_step::<(), _, _>("test.sleeper", {
        let woke = woke.clone();
        move |_task, runtime: StepRuntime, cx: Context| {
            let woke = woke.clone();
            async move {
                runtime.sleep(900.0, &cx).await?;
                runtime.sleep(1_005.0, &cx).await?;
                woke.resolve(());
                complete(&runtime, (), &cx).await
            }
        }
    });
    let now = Arc::clone(&clock);
    let OpenedRoot { harness, root, .. } = open_root_with(
        Arc::new(crate::storage::MemoryStorage::new()),
        &[sleeper.erase()],
        OpenTasksOptions {
            now: Some(Arc::new(move || f64::from_bits(now.load(Ordering::SeqCst)))),
            ..OpenTasksOptions::default()
        },
    )
    .await;
    let id = start(&root, &sleeper).await;
    harness.resume().unwrap();
    // The clock stands still, so timers keep firing without waking the task.
    tokio::time::sleep(Duration::from_millis(30)).await;
    flush().await;
    assert!(!woke.is_settled());
    clock.store(1_005_f64.to_bits(), Ordering::SeqCst);
    harness.wait_for_task(id, context()).await.unwrap();
    harness.close(context()).await.unwrap();
}

/// Runs on real (unpaused) time: both sleeps end through cancellation long
/// before their 60 s deadline, and paused time would auto-advance to it.
#[tokio::test]
async fn rejects_a_sleep_when_the_invocation_is_signalled_or_the_sleeps_own_context_is_cancelled() {
    let results = shared(Vec::<String>::new());
    let sleeping = deferred::<()>();
    let signalled = one_step::<(), _, _>("test.sleep-signalled", {
        let (results, sleeping) = (results.clone(), sleeping.clone());
        move |_task, runtime: StepRuntime, cx: Context| {
            sleeping.resolve(());
            let results = results.clone();
            async move {
                let until = runtime.now()? + 60_000.0;
                runtime.sleep(until, &cx).await.inspect_err(|error| {
                    lock(&results).push(format!("signalled:{}", error_name(error)));
                })
            }
        }
    });
    let cancelled = one_step::<(), _, _>("test.sleep-cancelled", {
        let results = results.clone();
        move |_task, runtime: StepRuntime, cx: Context| {
            let results = results.clone();
            async move {
                let controller = AbortController::new();
                let until = runtime.now()? + 60_000.0;
                let sleep = runtime.sleep(until, &with_signal(&controller.signal()));
                controller.abort(Some(reason("stop sleeping")));
                if let Err(error) = sleep.await {
                    lock(&results).push(format!("cancelled:{error}"));
                }
                complete(&runtime, (), &cx).await
            }
        }
    });
    let OpenedRoot { harness, root, .. } = open_root(&[signalled.erase(), cancelled.erase()]).await;
    let signalled_id = start(&root, &signalled).await;
    let cancelled_id = start(&root, &cancelled).await;
    harness.resume().unwrap();
    harness
        .wait_for_task(cancelled_id, context())
        .await
        .unwrap();
    sleeping.wait().await;
    harness
        .abort_task(signalled_id.erase(), context())
        .await
        .unwrap();
    assert_eq!(
        super::outcome(&harness, signalled_id).await,
        super::aborted_outcome("test")
    );
    assert_eq!(
        *lock(&results),
        ["cancelled:stop sleeping", "signalled:AbortError"]
    );
    harness.close(context()).await.unwrap();
}
