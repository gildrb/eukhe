//! `describe("task abort")`.

use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::Arc;

use eukhe_chord::context::{AbortController, Context};
use eukhe_chord::json::JsonValue;
use futures::future::BoxFuture;
use futures::FutureExt;
use serde::{Deserialize, Serialize};
use tokio::task::JoinHandle;

use super::{
    abort_requested, abort_with, aborted_outcome, advance, assert_rejects, complete, faulted,
    gated, held_gate, joined, lock, mark_durably, one_step, one_step_with_abort, open_root,
    open_root_with, reason, release_gate, shared, start, with_signal, OpenedRoot, Shared, StepRun,
    StepRuntime,
};
use crate::harness::tests::support::context;
use crate::harness::tests::task_support::{
    aborted, aborted_with, deferred, eventually, flush, OpenTasksOptions,
};
use crate::harness::{Harness, TaskAbortResult};
use crate::session::tests::support::{ControlledStorage, Gate};
use crate::session::{SessionError, SessionResult};
use crate::tasks::{define_task, NextTaskState, TaskDefinition, TaskRuntime, TaskRuntimeBackend};
use crate::types::{JoinPolicy, TaskId, TaskStatus};

/// What the `test.marked` abort handler saw of its task.
#[derive(Debug, PartialEq)]
struct AbortSaw {
    abort_requested: bool,
    memos: Option<JsonValue>,
}

#[tokio::test]
async fn rejects_the_runs_commits_and_memo_writes_after_the_mark_and_settles_through_a_fresh_abort_invocation(
) {
    let reached = deferred::<()>();
    let errors = shared(Vec::<String>::new());
    let memo_read: Shared<Option<Option<i64>>> = shared(None);
    let abort_runtimes = shared(Vec::<Arc<dyn TaskRuntimeBackend>>::new());
    let run_runtime: Shared<Option<Arc<dyn TaskRuntimeBackend>>> = shared(None);
    let abort_saw: Shared<Option<AbortSaw>> = shared(None);
    let marked = one_step_with_abort::<(), _, _, _, _>(
        "test.marked",
        {
            let (reached, errors, memo_read, run_runtime) = (
                reached.clone(),
                errors.clone(),
                memo_read.clone(),
                run_runtime.clone(),
            );
            move |_task, runtime: StepRuntime, cx: Context| {
                *lock(&run_runtime) = Some(Arc::clone(runtime.backend()));
                let (reached, errors, memo_read) =
                    (reached.clone(), errors.clone(), memo_read.clone());
                async move {
                    runtime.memo_or("kept", &1, &cx).await?;
                    reached.resolve(());
                    // Keep working after the signal: every later write of this run must reject.
                    aborted(&runtime.signal()).await;
                    *lock(&memo_read) = Some(runtime.memo::<i64>("kept", context()).await?);
                    if let Err(error) = runtime.memo_or("late", &2, context()).await {
                        lock(&errors).push(error.to_string());
                    }
                    if let Err(error) = complete(&runtime, (), context()).await {
                        lock(&errors).push(error.to_string());
                    }
                    Ok(())
                }
            }
        },
        {
            let (abort_runtimes, abort_saw) = (abort_runtimes.clone(), abort_saw.clone());
            move |runtime: StepRuntime, cx: Context| {
                lock(&abort_runtimes).push(Arc::clone(runtime.backend()));
                let abort_saw = abort_saw.clone();
                async move {
                    runtime
                        .commit(
                            move |_tx, current| async move {
                                *lock(&abort_saw) = Some(AbortSaw {
                                    abort_requested: current.abort_requested,
                                    memos: current.memos.map(JsonValue::Object),
                                });
                                Ok(Some(aborted_with("mark")))
                            },
                            &cx,
                        )
                        .await
                }
            }
        },
    );
    let OpenedRoot { harness, root, .. } = open_root(&[marked.erase()]).await;
    let id = start(&root, &marked).await;
    harness.resume().unwrap();
    reached.wait().await;
    assert_eq!(
        harness.abort_task(id.erase(), context()).await.unwrap(),
        TaskAbortResult::Marked
    );
    assert_eq!(super::outcome(&harness, id).await, aborted_outcome("mark"));
    assert_eq!(*lock(&memo_read), Some(Some(1)));
    let mark = format!("Task {id} has a durable abort mark");
    assert_eq!(*lock(&errors), [mark.clone(), mark]);
    assert_eq!(
        lock(&abort_saw).take(),
        Some(AbortSaw {
            abort_requested: true,
            memos: Some(super::json(r#"{"kept":1}"#)),
        })
    );
    let abort_runtimes = lock(&abort_runtimes).clone();
    assert_eq!(abort_runtimes.len(), 1);
    let run_runtime = lock(&run_runtime).clone().expect("the run started");
    assert!(!Arc::ptr_eq(&abort_runtimes[0], &run_runtime));
    harness.close(context()).await.unwrap();
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "phase", rename_all = "camelCase")]
enum Two {
    One,
    Two,
}

#[tokio::test]
async fn starts_no_further_phase_after_a_mark_that_lands_during_a_phase_with_progress() {
    let reached = deferred::<()>();
    let proceed = deferred::<()>();
    let phases = shared(Vec::<String>::new());
    let two = define_task(
        TaskDefinition::<(), Two, (), ()>::new("test.mark-boundary", 1, |(): &()| Ok(Two::One), {
            let phases = phases.clone();
            move |_task, runtime, cx: Context| {
                lock(&phases).push("abort".to_owned());
                async move { abort_with(&runtime, "boundary", &cx).await }
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
                    // Ignores the signal and returns normally after the mark.
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
    let OpenedRoot { harness, root, .. } = open_root(&[two.erase()]).await;
    let id = super::create(&root, &two, &()).await;
    harness.resume().unwrap();
    reached.wait().await;
    let aborting = mark_durably(&harness, id.erase()).await;
    proceed.resolve(());
    assert_eq!(joined(aborting).await.unwrap(), TaskAbortResult::Marked);
    assert_eq!(
        super::outcome(&harness, id).await,
        aborted_outcome("boundary")
    );
    assert_eq!(*lock(&phases), ["one", "abort"]);
    harness.close(context()).await.unwrap();
}

/// The body runs as a spawned task ([`super::as_task`]) so the second
/// `abort_task` enqueues like the TS microtask continuation.
#[tokio::test]
async fn signals_and_joins_the_run_before_returning_then_runs_the_abort_handler() {
    super::as_task(signals_and_joins_body()).await;
}

async fn signals_and_joins_body() {
    let reached = deferred::<()>();
    let run_ended = Arc::new(AtomicBool::new(false));
    let signalled = one_step::<(), _, _>("test.signalled", {
        let (reached, run_ended) = (reached.clone(), Arc::clone(&run_ended));
        move |_task, runtime: StepRuntime, _cx: Context| {
            reached.resolve(());
            let run_ended = Arc::clone(&run_ended);
            async move {
                let error = aborted(&runtime.signal()).await;
                run_ended.store(true, Ordering::SeqCst);
                Err(error)
            }
        }
    });
    let OpenedRoot { harness, root, .. } = open_root(&[signalled.erase()]).await;
    let id = start(&root, &signalled).await;
    harness.resume().unwrap();
    reached.wait().await;
    assert_eq!(
        harness.abort_task(id.erase(), context()).await.unwrap(),
        TaskAbortResult::Marked
    );
    assert!(run_ended.load(Ordering::SeqCst));
    assert_eq!(
        harness.abort_task(id.erase(), context()).await.unwrap(),
        TaskAbortResult::Marked
    );
    assert_eq!(super::outcome(&harness, id).await, aborted_outcome("test"));
    harness.close(context()).await.unwrap();
}

/// The `run` phase of the waiting tasks: wait on the task in `first`.
fn wait_on_first(
    first: &Shared<Option<TaskId>>,
) -> impl Fn(StepRun, StepRuntime, Context) -> BoxFuture<'static, SessionResult<()>>
       + Send
       + Sync
       + 'static {
    let first = first.clone();
    move |_task, runtime, cx| {
        let on = vec![lock(&first).expect("the dependency exists")];
        async move {
            runtime
                .commit(
                    move |_tx, _current| async move {
                        Ok(Some(NextTaskState::Waiting {
                            checkpoint: super::Step::Run,
                            on,
                            policy: JoinPolicy::AllSettled,
                        }))
                    },
                    &cx,
                )
                .await
        }
        .boxed()
    }
}

async fn status(harness: &Harness, id: TaskId) -> Option<TaskStatus> {
    harness
        .get_task(id, context())
        .await
        .unwrap()
        .map(|record| record.state.status())
}

#[tokio::test]
async fn aborts_waiting_work_before_its_wait_ends_and_faults_abort_handlers_that_throw_or_settle_nothing(
) {
    let gate = deferred::<()>();
    let first = gated("test.dependency", &gate);
    let first_id: Shared<Option<TaskId>> = shared(None);
    let lazy = one_step_with_abort::<(), _, _, _, _>(
        "test.lazy-abort",
        wait_on_first(&first_id),
        |_runtime, _cx| async { Ok(()) },
    );
    let throwing = one_step_with_abort::<(), _, _, _, _>(
        "test.throwing-abort",
        wait_on_first(&first_id),
        |_runtime, _cx| async { Err(SessionError::error("abort failed")) },
    );
    let OpenedRoot { harness, root, .. } =
        open_root(&[first.erase(), lazy.erase(), throwing.erase()]).await;
    let first_task = start(&root, &first).await.erase();
    *lock(&first_id) = Some(first_task);
    let lazy_id = start(&root, &lazy).await.erase();
    let throwing_id = start(&root, &throwing).await.erase();
    harness.resume().unwrap();
    eventually(|| async { status(&harness, throwing_id).await == Some(TaskStatus::Waiting) }).await;
    eventually(|| async { status(&harness, lazy_id).await == Some(TaskStatus::Waiting) }).await;
    harness.abort_task(lazy_id, context()).await.unwrap();
    harness.abort_task(throwing_id, context()).await.unwrap();
    assert_eq!(
        super::outcome(&harness, lazy_id).await,
        faulted(&format!(
            "Abort handler of task {lazy_id} returned without a terminal outcome"
        ))
    );
    assert_eq!(
        super::outcome(&harness, throwing_id).await,
        faulted("abort failed")
    );
    assert_eq!(
        status(&harness, first_task).await,
        Some(TaskStatus::Running)
    );
    gate.resolve(());
    harness.wait_for_task(first_task, context()).await.unwrap();
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn does_not_signal_a_running_abort_handler_when_aborted_again_and_a_cancelled_caller_leaves_the_mark_durable(
) {
    let reached = deferred::<()>();
    let proceed = deferred::<()>();
    let run_release = deferred::<()>();
    let abort_signalled: Shared<Option<bool>> = shared(None);
    let aborts = Arc::new(AtomicUsize::new(0));
    let run = one_step_with_abort::<(), _, _, _, _>(
        "test.abort-again",
        {
            let run_release = run_release.clone();
            move |_task, _runtime, _cx| {
                // Ignores the signal, so the first caller is still joining when it gives up.
                let released = run_release.wait();
                async move {
                    released.await;
                    Ok(())
                }
            }
        },
        {
            let (reached, proceed, abort_signalled, aborts) = (
                reached.clone(),
                proceed.clone(),
                abort_signalled.clone(),
                Arc::clone(&aborts),
            );
            move |runtime: StepRuntime, cx: Context| {
                aborts.fetch_add(1, Ordering::SeqCst);
                reached.resolve(());
                let proceed = proceed.wait();
                let abort_signalled = abort_signalled.clone();
                async move {
                    proceed.await;
                    *lock(&abort_signalled) = Some(runtime.signal().aborted());
                    abort_with(&runtime, "once", &cx).await
                }
            }
        },
    );
    let OpenedRoot { harness, root, .. } = open_root(&[run.erase()]).await;
    let id = start(&root, &run).await;
    harness.resume().unwrap();
    flush().await;
    // This caller gives up while joining; the mark and the abort invocation are unaffected.
    let controller = AbortController::new();
    let cancelled =
        tokio::spawn(harness.abort_task(id.erase(), &with_signal(&controller.signal())));
    while !abort_requested(&harness, id.erase()).await {
        flush().await;
    }
    controller.abort(Some(reason("caller gave up")));
    assert_rejects(joined(cancelled).await, "caller gave up");
    run_release.resolve(());
    reached.wait().await;
    assert_eq!(
        harness.abort_task(id.erase(), context()).await.unwrap(),
        TaskAbortResult::Marked
    );
    proceed.resolve(());
    assert_eq!(super::outcome(&harness, id).await, aborted_outcome("once"));
    assert_eq!(*lock(&abort_signalled), Some(false));
    assert_eq!(aborts.load(Ordering::SeqCst), 1);
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn keeps_a_terminal_outcome_committed_by_an_abort_handler_that_throws_afterwards() {
    let run = one_step_with_abort::<(), _, _, _, _>(
        "test.abort-then-throw",
        |_task, runtime: StepRuntime, _cx: Context| async move { Err(aborted(&runtime.signal()).await) },
        |runtime: StepRuntime, cx: Context| async move {
            abort_with(&runtime, "done", &cx).await?;
            Err(SessionError::error("after terminal"))
        },
    );
    let OpenedRoot { harness, root, .. } = open_root(&[run.erase()]).await;
    let id = start(&root, &run).await;
    harness.resume().unwrap();
    flush().await;
    harness.abort_task(id.erase(), context()).await.unwrap();
    assert_eq!(super::outcome(&harness, id).await, aborted_outcome("done"));
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn never_starts_phase_one_when_the_abort_lands_while_the_reservation_settles() {
    let ran = Arc::new(AtomicBool::new(false));
    let reserved = one_step::<(), _, _>("test.reserved", {
        let ran = Arc::clone(&ran);
        move |_task, runtime: StepRuntime, _cx: Context| {
            ran.store(true, Ordering::SeqCst);
            async move { Err(aborted(&runtime.signal()).await) }
        }
    });
    let storage = ControlledStorage::new();
    let OpenedRoot { harness, root, .. } = open_root_with(
        storage.clone(),
        &[reserved.erase()],
        OpenTasksOptions::default(),
    )
    .await;
    let id = start(&root, &reserved).await;
    let held = storage.hold_commits();
    harness.resume().unwrap();
    held.entered().await;
    // The reservation commit is in storage; the abort mark commit queues behind it.
    let aborting = tokio::spawn(harness.abort_task(id.erase(), context()));
    flush().await;
    held.release();
    assert_eq!(joined(aborting).await.unwrap(), TaskAbortResult::Marked);
    assert_eq!(super::outcome(&harness, id).await, aborted_outcome("test"));
    assert!(!ran.load(Ordering::SeqCst));
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn lets_an_abort_mark_win_over_a_fault_that_races_it() {
    let storage = ControlledStorage::new();
    let marking: Shared<Option<JoinHandle<SessionResult<TaskAbortResult>>>> = shared(None);
    let held: Shared<Option<Gate>> = shared(None);
    let harness_ref: Shared<Option<Harness>> = shared(None);
    let racing = one_step::<(), _, _>("test.racing-fault", {
        let (storage, marking, held, harness_ref) = (
            Arc::clone(&storage),
            marking.clone(),
            held.clone(),
            harness_ref.clone(),
        );
        move |task, _runtime: StepRuntime, _cx: Context| {
            let gate = storage.hold_commits();
            let entered = gate.entered();
            *lock(&held) = Some(gate);
            let harness = lock(&harness_ref).take().expect("the Harness is open");
            *lock(&marking) = Some(tokio::spawn(harness.abort_task(task.id.erase(), context())));
            async move {
                entered.await;
                // The mark is in storage but not committed when the handler throws, so the fault commit queues behind it.
                Err(SessionError::error("would fault"))
            }
        }
    });
    let OpenedRoot { harness, root, .. } = open_root_with(
        storage.clone(),
        &[racing.erase()],
        OpenTasksOptions::default(),
    )
    .await;
    *lock(&harness_ref) = Some(harness.clone());
    let id = start(&root, &racing).await;
    harness.resume().unwrap();
    held_gate(&held).await;
    flush().await;
    release_gate(&held);
    assert_eq!(super::outcome(&harness, id).await, aborted_outcome("test"));
    let marking = lock(&marking)
        .take()
        .expect("the handler started the abort");
    assert_eq!(joined(marking).await.unwrap(), TaskAbortResult::Marked);
    harness.close(context()).await.unwrap();
}
