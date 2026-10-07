//! TS `describe("task crash recovery")`.
//!
//! Crash simulation: the crashed Harness is abandoned without close, its held
//! storage commit never lands, and its blocked handlers never return. A new
//! Harness then opens the same storage. The crashed Harness stays in scope
//! until the test ends, so its blocked handler futures stay pending.

use std::sync::Arc;

use super::{create_in, until, Log, Step};
use crate::harness::tests::support::context;
use crate::harness::tests::task_support::{
    aborted_with, deferred, flush, open_tasks, OpenTasksOptions,
};
use crate::harness::Harness;
use crate::session::tests::support::ControlledStorage;
use crate::tasks::{define_task, AnyTask, TaskDefinition};
use crate::types::{Storage, TaskId, TaskOutcome, TaskQuery, TaskState, TaskStatus};

/// A task whose run ignores its signal and whose abort handler blocks while
/// `block_abort` is set.
fn crash_task(log: &Log, block_abort: bool) -> AnyTask {
    let run_log = log.clone();
    let abort_log = log.clone();
    define_task(
        TaskDefinition::<(), Step, (), ()>::new(
            "test.crash",
            1,
            |()| Ok(Step::Run),
            move |_task, runtime, cx| {
                let log = abort_log.clone();
                async move {
                    log.push("abort");
                    if block_abort {
                        std::future::pending::<()>().await;
                    }
                    runtime
                        .commit(
                            |_tx, _current| async move { Ok(Some(aborted_with("recovered"))) },
                            &cx,
                        )
                        .await
                }
            },
        )
        .phase("run", move |_task, _runtime, _cx| {
            let log = run_log.clone();
            async move {
                log.push("run");
                std::future::pending::<()>().await;
                Ok(())
            }
        }),
    )
    .erase()
}

fn storage_of(storage: &Arc<ControlledStorage>) -> Arc<dyn Storage> {
    Arc::clone(storage) as Arc<dyn Storage>
}

async fn recover(storage: &Arc<ControlledStorage>, log: &Log) -> (Harness, TaskId) {
    storage.crash();
    let harness = open_tasks(
        storage_of(storage),
        &[crash_task(log, false)],
        OpenTasksOptions::default(),
    )
    .await
    .harness;
    let page = harness
        .commit(
            |tx| async move {
                tx.scan_tasks(
                    TaskQuery {
                        kind: Some("test.crash".to_owned()),
                        ..TaskQuery::default()
                    },
                    1,
                    None,
                )
                .await
            },
            context(),
        )
        .await
        .unwrap();
    let id = page.items[0].id;
    (harness, id)
}

async fn crashed_run(log: &Log) -> (Arc<ControlledStorage>, Harness, TaskId) {
    let storage = ControlledStorage::new();
    let harness = open_tasks(
        storage_of(&storage),
        &[crash_task(log, true)],
        OpenTasksOptions::default(),
    )
    .await
    .harness;
    let id = create_in(&harness, &crash_task(log, true)).await;
    harness.resume().unwrap();
    until(|| log.len() == 1).await;
    (storage, harness, id)
}

fn recovered_outcome() -> TaskOutcome {
    TaskOutcome::Aborted {
        reason: Some("recovered".to_owned()),
        result: None,
    }
}

#[tokio::test]
async fn crash_while_the_mark_commit_is_in_storage_the_run_resumes() {
    let log = Log::default();
    let (storage, harness, id) = crashed_run(&log).await;
    let held = storage.hold_commits();
    drop(tokio::spawn(harness.abort_task(id, context())));
    held.entered().await;
    let (recovered, _) = recover(&storage, &log).await;
    let record = recovered.get_task(id, context()).await.unwrap().unwrap();
    assert!(!record.abort_requested);
    assert!(matches!(record.state, TaskState::Pending { .. }));
    recovered.resume().unwrap();
    until(|| log.len() == 2).await;
    assert_eq!(log.all(), ["run", "run"]);
    drop(harness);
}

#[tokio::test]
async fn crash_after_the_mark_before_the_run_joins_only_the_abort_handler_runs() {
    let log = Log::default();
    let (storage, harness, id) = crashed_run(&log).await;
    // The run ignores its signal, so abortTask never finishes joining it.
    let joining = tokio::spawn(harness.abort_task(id, context()));
    while !harness
        .get_task(id, context())
        .await
        .unwrap()
        .is_some_and(|record| record.abort_requested)
    {
        flush().await;
    }
    flush().await;
    assert!(!joining.is_finished());
    let (recovered, _) = recover(&storage, &log).await;
    let record = recovered.get_task(id, context()).await.unwrap().unwrap();
    assert!(record.abort_requested);
    assert!(matches!(record.state, TaskState::Pending { .. }));
    recovered.resume().unwrap();
    assert_eq!(
        recovered
            .wait_for_task(id, context())
            .await
            .unwrap()
            .outcome,
        recovered_outcome()
    );
    assert_eq!(log.all(), ["run", "abort"]);
    recovered.close(context()).await.unwrap();
    drop(harness);
}

#[tokio::test]
async fn crash_while_the_abort_handler_runs_a_fresh_abort_invocation_settles_the_task() {
    let log = Log::default();
    let storage = ControlledStorage::new();
    let crash = crash_task(&log, true);
    let harness = open_tasks(
        storage_of(&storage),
        std::slice::from_ref(&crash),
        OpenTasksOptions::default(),
    )
    .await
    .harness;
    let id = create_in(&harness, &crash).await;
    harness.abort_task(id, context()).await.unwrap();
    harness.resume().unwrap();
    until(|| log.len() == 1).await;
    assert_eq!(log.all(), ["abort"]);
    assert_eq!(
        harness
            .get_task(id, context())
            .await
            .unwrap()
            .unwrap()
            .state
            .status(),
        TaskStatus::Running
    );
    let (recovered, _) = recover(&storage, &log).await;
    recovered.resume().unwrap();
    assert_eq!(
        recovered
            .wait_for_task(id, context())
            .await
            .unwrap()
            .outcome,
        recovered_outcome()
    );
    assert_eq!(log.all(), ["abort", "abort"]);
    recovered.close(context()).await.unwrap();
    drop(harness);
}

#[tokio::test]
async fn crash_while_the_abort_outcome_is_in_storage_the_abort_handler_runs_again() {
    let log = Log::default();
    let storage = ControlledStorage::new();
    let reached = deferred::<()>();
    let proceed = deferred::<()>();
    let crash = {
        let log = log.clone();
        let reached = reached.clone();
        let proceed = proceed.clone();
        define_task(
            TaskDefinition::<(), Step, (), ()>::new(
                "test.crash",
                1,
                |()| Ok(Step::Run),
                move |_task, runtime, cx| {
                    let log = log.clone();
                    let reached = reached.clone();
                    let proceed = proceed.wait();
                    async move {
                        log.push("abort");
                        reached.resolve(());
                        proceed.await;
                        runtime
                            .commit(
                                |_tx, _current| async move { Ok(Some(aborted_with("lost"))) },
                                &cx,
                            )
                            .await
                    }
                },
            )
            .phase("run", |_task, _runtime, _cx| async { Ok(()) }),
        )
        .erase()
    };
    let harness = open_tasks(
        storage_of(&storage),
        std::slice::from_ref(&crash),
        OpenTasksOptions::default(),
    )
    .await
    .harness;
    let id = create_in(&harness, &crash).await;
    harness.abort_task(id, context()).await.unwrap();
    harness.resume().unwrap();
    reached.wait().await;
    let held = storage.hold_commits();
    proceed.resolve(());
    held.entered().await;
    let (recovered, _) = recover(&storage, &log).await;
    recovered.resume().unwrap();
    assert_eq!(
        recovered
            .wait_for_task(id, context())
            .await
            .unwrap()
            .outcome,
        recovered_outcome()
    );
    assert_eq!(log.all(), ["abort", "abort"]);
    recovered.close(context()).await.unwrap();
    drop(harness);
}

#[tokio::test]
async fn crash_after_the_terminal_outcome_nothing_runs_again() {
    let log = Log::default();
    let storage = ControlledStorage::new();
    let crash = crash_task(&log, false);
    let harness = open_tasks(
        storage_of(&storage),
        std::slice::from_ref(&crash),
        OpenTasksOptions::default(),
    )
    .await
    .harness;
    let id = create_in(&harness, &crash).await;
    harness.abort_task(id, context()).await.unwrap();
    harness.resume().unwrap();
    harness.wait_for_task(id, context()).await.unwrap();
    let (recovered, _) = recover(&storage, &log).await;
    recovered.resume().unwrap();
    flush().await;
    assert_eq!(log.all(), ["abort"]);
    assert_eq!(
        recovered
            .get_task(id, context())
            .await
            .unwrap()
            .map(|record| record.state),
        Some(TaskState::Terminal {
            outcome: recovered_outcome(),
        })
    );
    recovered.close(context()).await.unwrap();
    drop(harness);
}

#[tokio::test]
async fn crash_while_the_reservation_commit_is_in_storage_the_task_is_still_pending() {
    let log = Log::default();
    let storage = ControlledStorage::new();
    let crash = crash_task(&log, false);
    let harness = open_tasks(
        storage_of(&storage),
        std::slice::from_ref(&crash),
        OpenTasksOptions::default(),
    )
    .await
    .harness;
    let id = create_in(&harness, &crash).await;
    let held = storage.hold_commits();
    harness.resume().unwrap();
    held.entered().await;
    let (recovered, _) = recover(&storage, &log).await;
    assert_eq!(
        recovered
            .get_task(id, context())
            .await
            .unwrap()
            .map(|record| record.state.status()),
        Some(TaskStatus::Pending)
    );
    assert!(log.all().is_empty());
    recovered.abort_task(id, context()).await.unwrap();
    recovered.resume().unwrap();
    recovered.wait_for_task(id, context()).await.unwrap();
    assert_eq!(log.all(), ["abort"]);
    recovered.close(context()).await.unwrap();
    drop(harness);
}
