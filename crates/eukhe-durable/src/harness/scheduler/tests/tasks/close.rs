//! `describe("task close")`.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use eukhe_chord::context::Context;
use serde::{Deserialize, Serialize};
use tokio::task::JoinHandle;

use super::{
    advance, assert_rejects, complete, held_gate, joined, json, lock, mark_durably, one_step,
    one_step_with_abort, open_root_with, queue_blocker, release_gate, shared, start, task_writes,
    OpenedRoot, Shared, StepRuntime, Text,
};
use crate::documents::{DocDefinition, SessionDoc};
use crate::harness::registry::Registry;
use crate::harness::tests::support::{add_task, context, create_models, create_registry};
use crate::harness::tests::task_support::{deferred, eventually, flush, OpenTasksOptions};
use crate::harness::types::{HarnessOptions, RegistryReader, RegistrySnapshot};
use crate::harness::{Harness, RootOptions, TaskAbortResult};
use crate::session::tests::support::{ControlledStorage, Gate};
use crate::session::{SessionError, SessionResult, Unsubscribe, WatchEnd};
use crate::storage::MemoryStorage;
use crate::tasks::{define_task, TaskDefinition, TaskRuntime};
use crate::types::{DocumentObserverExt, StorageWrite, TaskState, TaskStatus};

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "phase", rename_all = "camelCase")]
enum Two {
    One,
    Two,
}

#[tokio::test]
async fn stops_without_outcomes_and_starts_no_fresh_phase_or_abort_invocation_while_closing() {
    let reached = deferred::<()>();
    let proceed = deferred::<()>();
    let phases = shared(Vec::<String>::new());
    let abort_ran = Arc::new(AtomicBool::new(false));
    let two = define_task(
        TaskDefinition::<(), Two, (), ()>::new("test.two", 1, |(): &()| Ok(Two::One), {
            let abort_ran = Arc::clone(&abort_ran);
            move |_task, _runtime, _cx| {
                abort_ran.store(true, Ordering::SeqCst);
                async { Ok(()) }
            }
        })
        .phase("one", {
            let (phases, reached, proceed) = (phases.clone(), reached.clone(), proceed.clone());
            move |_task, runtime: TaskRuntime<(), Two, (), ()>, cx: Context| {
                lock(&phases).push("one".to_owned());
                let reached = reached.clone();
                let proceed = proceed.wait();
                async move {
                    advance(&runtime, Two::Two, &cx).await?;
                    reached.resolve(());
                    // Ignores signals and returns normally once released; the closing rule wins over the next phase.
                    proceed.await;
                    Ok(())
                }
            }
        })
        .phase("two", {
            let phases = phases.clone();
            move |_task, _runtime, _cx| {
                lock(&phases).push("two".to_owned());
                async { Ok(()) }
            }
        }),
    );
    let storage = ControlledStorage::new();
    let OpenedRoot { harness, root, .. } =
        open_root_with(storage.clone(), &[two.erase()], OpenTasksOptions::default()).await;
    let id = super::create(&root, &two, &()).await;
    harness.resume().unwrap();
    reached.wait().await;
    let aborting = mark_durably(&harness, id.erase()).await;
    let record = harness.get_task(id, context()).await.unwrap().unwrap();
    let commits = storage.commits().len();
    let closing = tokio::spawn(harness.close(context()));
    proceed.resolve(());
    joined(closing).await.unwrap();
    assert_eq!(joined(aborting).await.unwrap(), TaskAbortResult::Marked);
    assert_eq!(storage.commits().len(), commits);
    assert_eq!(*lock(&phases), ["one"]);
    assert!(!abort_ran.load(Ordering::SeqCst));
    assert!(record.abort_requested);
    assert_eq!(
        record.state,
        TaskState::Running {
            checkpoint: json(r#"{"phase":"two"}"#)
        }
    );
    assert_rejects(
        harness.commit(|_tx| async { Ok(()) }, context()).await,
        "closed",
    );
}

static CLOSE_NOTES: SessionDoc<Text> = match SessionDoc::define(DocDefinition {
    kind: "test.close-notes",
    version: 1,
    initial: Text::default,
    migrate: None,
    checkpoint_when: None,
}) {
    Ok(token) => token,
    Err(_) => panic!("test.close-notes has a valid version"),
};

/// The listener runs as a task spawned when the signal aborts (Rust signals
/// have no synchronous listeners); its commit is still issued after close
/// sealed admission.
#[tokio::test]
async fn seals_admission_before_signalling_handlers_and_stops_watches_before_joining_them() {
    let reached = deferred::<()>();
    let from_listener: Shared<Option<SessionResult<()>>> = shared(None);
    let harness_ref: Shared<Option<Harness>> = shared(None);
    let watch_end: Shared<Option<WatchEnd>> = shared(None);
    let stubborn = one_step::<(), _, _>("test.stubborn", {
        let (reached, from_listener, harness_ref, watch_end) = (
            reached.clone(),
            from_listener.clone(),
            harness_ref.clone(),
            watch_end.clone(),
        );
        move |_task, runtime: StepRuntime, _cx: Context| {
            let (reached, from_listener, harness_ref, watch_end) = (
                reached.clone(),
                from_listener.clone(),
                harness_ref.clone(),
                watch_end.clone(),
            );
            async move {
                // Uses a context close does not cancel, then waits for the watch to close.
                let watch = runtime
                    .watch_doc(&CLOSE_NOTES, (), context())
                    .await?
                    .expect("notes exist");
                let signal = runtime.signal();
                let harness = lock(&harness_ref).take().expect("the Harness is open");
                drop(tokio::spawn(async move {
                    signal.cancelled().await;
                    let result = harness.commit(|_tx| async { Ok(()) }, context()).await;
                    *lock(&from_listener) = Some(result);
                }));
                reached.resolve(());
                *lock(&watch_end) = Some(watch.closed().await);
                Ok(())
            }
        }
    });
    let OpenedRoot { harness, root, .. } = open_root_with(
        Arc::new(MemoryStorage::new()),
        &[stubborn.erase()],
        OpenTasksOptions::default(),
    )
    .await;
    *lock(&harness_ref) = Some(harness.clone());
    harness
        .commit(
            |tx| async move {
                tx.doc(&CLOSE_NOTES, ()).await?.set("text", "x")?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    start(&root, &stubborn).await;
    harness.resume().unwrap();
    reached.wait().await;
    harness.close(context()).await.unwrap();
    eventually(|| std::future::ready(lock(&from_listener).is_some())).await;
    assert_rejects(lock(&from_listener).take().unwrap(), "closed");
    assert_eq!(lock(&watch_end).take(), Some(WatchEnd::SessionClosed));
}

/// Install a run handler that holds commits and queues a blocker commit.
fn hold_and_block(
    storage: &Arc<ControlledStorage>,
    held: &Shared<Option<Gate>>,
    harness_ref: &Shared<Option<Harness>>,
    runtime: &StepRuntime,
) {
    *lock(held) = Some(storage.hold_commits());
    let harness = lock(harness_ref).take().expect("the Harness is open");
    queue_blocker(&harness, runtime.conversation_id());
}

#[tokio::test]
async fn writes_no_fault_when_close_seals_while_the_step_after_a_failed_phase_is_queued() {
    let storage = ControlledStorage::new();
    let held: Shared<Option<Gate>> = shared(None);
    let harness_ref: Shared<Option<Harness>> = shared(None);
    let throws = one_step::<(), _, _>("test.close-fault", {
        let (storage, held, harness_ref) =
            (Arc::clone(&storage), held.clone(), harness_ref.clone());
        move |_task, runtime: StepRuntime, _cx: Context| {
            hold_and_block(&storage, &held, &harness_ref, &runtime);
            async { Err(SessionError::error("would fault")) }
        }
    });
    let OpenedRoot { harness, root, .. } = open_root_with(
        storage.clone(),
        &[throws.erase()],
        OpenTasksOptions::default(),
    )
    .await;
    *lock(&harness_ref) = Some(harness.clone());
    let id = start(&root, &throws).await;
    harness.resume().unwrap();
    held_gate(&held).await;
    flush().await;
    let closing = tokio::spawn(harness.close(context()));
    release_gate(&held);
    joined(closing).await.unwrap();
    let statuses: Vec<TaskStatus> = task_writes(&storage.commits(), id.erase())
        .iter()
        .map(|record| record.state.status())
        .collect();
    assert_eq!(statuses, [TaskStatus::Pending, TaskStatus::Running]);
}

#[tokio::test]
async fn starts_no_abort_handler_whose_reservation_settles_while_closing() {
    let ran = Arc::new(AtomicBool::new(false));
    let marked = one_step_with_abort::<(), _, _, _, _>(
        "test.close-abort-reservation",
        |_task, _runtime, _cx| async { Ok(()) },
        {
            let ran = Arc::clone(&ran);
            move |_runtime, _cx| {
                ran.store(true, Ordering::SeqCst);
                async { Ok(()) }
            }
        },
    );
    let storage = ControlledStorage::new();
    let OpenedRoot { harness, root, .. } = open_root_with(
        storage.clone(),
        &[marked.erase()],
        OpenTasksOptions::default(),
    )
    .await;
    let id = start(&root, &marked).await;
    assert_eq!(
        harness.abort_task(id.erase(), context()).await.unwrap(),
        TaskAbortResult::Marked
    );
    let held = storage.hold_commits();
    harness.resume().unwrap();
    held.entered().await;
    let closing = tokio::spawn(harness.close(context()));
    held.release();
    joined(closing).await.unwrap();
    assert!(!ran.load(Ordering::SeqCst));
    let writes = last_task_writes(&storage);
    assert_eq!(writes.len(), 1, "{writes:?}");
    assert_eq!(writes[0].id, id.erase());
    assert!(writes[0].abort_requested);
    assert_eq!(writes[0].state.status(), TaskStatus::Running);
}

/// Task records of the last commit.
fn last_task_writes(storage: &ControlledStorage) -> Vec<crate::types::AnyTaskRecord> {
    storage
        .last_commit()
        .into_iter()
        .filter_map(|write| match write {
            StorageWrite::Task { value } => Some(value),
            _ => None,
        })
        .collect()
}

#[tokio::test]
async fn rejects_a_runtime_commit_that_was_queued_on_the_line_when_close_sealed_it() {
    let storage = ControlledStorage::new();
    let queued: Shared<Option<JoinHandle<SessionResult<()>>>> = shared(None);
    let held: Shared<Option<Gate>> = shared(None);
    let harness_ref: Shared<Option<Harness>> = shared(None);
    let proceed = deferred::<()>();
    let queued_task = one_step::<(), _, _>("test.close-queued-commit", {
        let (storage, queued, held, harness_ref, proceed) = (
            Arc::clone(&storage),
            queued.clone(),
            held.clone(),
            harness_ref.clone(),
            proceed.clone(),
        );
        move |_task, runtime: StepRuntime, _cx: Context| {
            hold_and_block(&storage, &held, &harness_ref, &runtime);
            *lock(&queued) = Some(tokio::spawn(complete(&runtime, (), context())));
            // Ignores the close signal, so the invocation is still alive when the queued commit reaches the line.
            let proceed = proceed.wait();
            async move {
                proceed.await;
                Ok(())
            }
        }
    });
    let OpenedRoot { harness, root, .. } = open_root_with(
        storage.clone(),
        &[queued_task.erase()],
        OpenTasksOptions::default(),
    )
    .await;
    *lock(&harness_ref) = Some(harness.clone());
    let id = start(&root, &queued_task).await;
    harness.resume().unwrap();
    held_gate(&held).await;
    flush().await;
    let closing = tokio::spawn(harness.close(context()));
    release_gate(&held);
    let queued = lock(&queued).take().expect("the handler queued a commit");
    assert_rejects(joined(queued).await, "Harness is closed");
    proceed.resolve(());
    joined(closing).await.unwrap();
    assert_eq!(task_writes(&storage.commits(), id.erase()).len(), 2);
}

/// Registry reader that closes the Harness from inside the step's snapshot
/// refresh, once armed.
struct ClosingReader {
    registry: Registry,
    harness: Shared<Option<Harness>>,
    closing: Shared<Option<JoinHandle<SessionResult<()>>>>,
    close_on_snapshot: Arc<AtomicBool>,
}

impl RegistryReader for ClosingReader {
    fn snapshot(&self) -> RegistrySnapshot {
        if self.close_on_snapshot.swap(false, Ordering::SeqCst) {
            let harness = lock(&self.harness).take().expect("the Harness is open");
            *lock(&self.closing) = Some(tokio::spawn(harness.close(context())));
        }
        self.registry.snapshot()
    }

    fn subscribe(&self, listener: Arc<dyn Fn() + Send + Sync>) -> Unsubscribe {
        self.registry.subscribe(listener)
    }
}

#[tokio::test]
async fn starts_no_next_phase_when_close_seals_during_a_step_that_decided_to_continue() {
    let phases = shared(Vec::<String>::new());
    let registry = create_registry();
    let harness_slot: Shared<Option<Harness>> = shared(None);
    let closing: Shared<Option<JoinHandle<SessionResult<()>>>> = shared(None);
    let close_on_snapshot = Arc::new(AtomicBool::new(false));
    // The step refreshes the snapshot after progress, inside its line callback and after its closing check.
    let reader = ClosingReader {
        registry: registry.clone(),
        harness: harness_slot.clone(),
        closing: closing.clone(),
        close_on_snapshot: Arc::clone(&close_on_snapshot),
    };
    let two = define_task(
        TaskDefinition::<(), Two, (), ()>::new(
            "test.close-in-step",
            1,
            |(): &()| Ok(Two::One),
            |_task, _runtime, _cx| async { Ok(()) },
        )
        .phase("one", {
            let (phases, close_on_snapshot) = (phases.clone(), Arc::clone(&close_on_snapshot));
            move |_task, runtime: TaskRuntime<(), Two, (), ()>, cx: Context| {
                lock(&phases).push("one".to_owned());
                let close_on_snapshot = Arc::clone(&close_on_snapshot);
                async move {
                    advance(&runtime, Two::Two, &cx).await?;
                    close_on_snapshot.store(true, Ordering::SeqCst);
                    Ok(())
                }
            }
        })
        .phase("two", {
            let phases = phases.clone();
            move |_task, _runtime, _cx| {
                lock(&phases).push("two".to_owned());
                async { Ok(()) }
            }
        }),
    );
    add_task(&registry, two.erase(), None).unwrap();
    let harness = Harness::open(
        Arc::new(MemoryStorage::new()),
        HarnessOptions::new(create_models(), Arc::new(reader)),
        context(),
    )
    .await
    .unwrap();
    *lock(&harness_slot) = Some(harness.clone());
    let root = harness
        .root(RootOptions::default(), context())
        .await
        .unwrap();
    super::create(&root, &two, &()).await;
    harness.resume().unwrap();
    eventually(|| std::future::ready(lock(&closing).is_some())).await;
    let closing = lock(&closing).take().expect("the step closed the Harness");
    joined(closing).await.unwrap();
    assert_eq!(*lock(&phases), ["one"]);
}

#[tokio::test]
async fn joins_a_reservation_that_settles_while_closing_without_starting_its_handler() {
    let ran = Arc::new(AtomicBool::new(false));
    let never = one_step::<(), _, _>("test.close-reservation", {
        let ran = Arc::clone(&ran);
        move |_task, _runtime, _cx| {
            ran.store(true, Ordering::SeqCst);
            async { Ok(()) }
        }
    });
    let storage = ControlledStorage::new();
    let OpenedRoot { harness, root, .. } = open_root_with(
        storage.clone(),
        &[never.erase()],
        OpenTasksOptions::default(),
    )
    .await;
    let id = start(&root, &never).await;
    let held = storage.hold_commits();
    harness.resume().unwrap();
    held.entered().await;
    let closing = tokio::spawn(harness.close(context()));
    held.release();
    joined(closing).await.unwrap();
    assert!(!ran.load(Ordering::SeqCst));
    let writes = last_task_writes(&storage);
    assert_eq!(writes.len(), 1, "{writes:?}");
    assert_eq!(writes[0].id, id.erase());
    assert_eq!(writes[0].state.status(), TaskStatus::Running);
}
