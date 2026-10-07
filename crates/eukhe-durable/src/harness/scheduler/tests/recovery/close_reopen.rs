//! TS `describe("task recovery")`.

use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

use serde::{Deserialize, Serialize};

use super::{create_in, sqlite, sqlite_path, until, Log, Step};
use crate::harness::tests::support::context;
use crate::harness::tests::task_support::{
    aborted, aborted_with, completed, deferred, flush, open_tasks, Deferred, OpenTasksOptions,
};
use crate::harness::TaskAbortResult;
use crate::session::tests::support::json;
use crate::tasks::{define_task, AnyTask, NextTaskState, TaskDefinition};
use crate::types::{TaskOptions, TaskOutcome, TaskOwnership, TaskState};

/// Fake external service whose operations are idempotent by request key.
#[derive(Clone, Default)]
struct TransferService(Arc<Mutex<TransferLedger>>);

#[derive(Default)]
struct TransferLedger {
    applied: HashMap<String, u64>,
    calls: usize,
}

impl TransferService {
    fn apply(&self, key: &str, amount: u64) -> u64 {
        let mut ledger = self.0.lock().unwrap_or_else(PoisonError::into_inner);
        ledger.calls += 1;
        *ledger.applied.entry(key.to_owned()).or_insert(amount * 10)
    }

    fn calls(&self) -> usize {
        self.0.lock().unwrap_or_else(PoisonError::into_inner).calls
    }

    fn applied(&self) -> usize {
        self.0
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .applied
            .len()
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct TransferInput {
    amount: u64,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "phase", rename_all = "lowercase")]
enum TransferState {
    Prepare,
    Apply { key: String },
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct Receipt {
    receipt: u64,
}

/// Intent/effect/outcome task: `prepare` commits the intent, `apply` performs
/// the effect and commits the outcome. While `interrupt` is set, the first
/// `apply` blocks after the effect until the invocation is signalled.
fn transfer_task(service: &TransferService, interrupt: &Arc<AtomicBool>) -> AnyTask {
    let service = service.clone();
    let interrupt = Arc::clone(interrupt);
    define_task(
        TaskDefinition::<TransferInput, TransferState, Receipt, ()>::new(
            "test.transfer",
            1,
            |_| Ok(TransferState::Prepare),
            |_task, runtime, cx| async move {
                runtime
                    .commit(
                        |_tx, _current| async move { Ok(Some(aborted_without_reason())) },
                        &cx,
                    )
                    .await
            },
        )
        .phase("prepare", |task, runtime, cx| async move {
            runtime
                .memo_or("requested", &task.input.amount, &cx)
                .await?;
            let key = format!("transfer-{}", task.id);
            runtime
                .commit(
                    move |_tx, _current| async move {
                        Ok(Some(NextTaskState::Running {
                            checkpoint: TransferState::Apply { key },
                        }))
                    },
                    &cx,
                )
                .await
        })
        .phase("apply", move |task, runtime, cx| {
            let service = service.clone();
            let interrupt = Arc::clone(&interrupt);
            async move {
                let TransferState::Apply { key } = &task.checkpoint else {
                    unreachable!("the apply phase runs apply checkpoints");
                };
                let receipt = service.apply(key, task.input.amount);
                if interrupt.swap(false, Ordering::SeqCst) {
                    return Err(aborted(&runtime.signal()).await);
                }
                runtime
                    .commit(
                        move |_tx, _current| async move { Ok(Some(completed(Receipt { receipt }))) },
                        &cx,
                    )
                    .await
            }
        }),
    )
    .erase()
}

/// TS `{ status: "aborted" }`.
fn aborted_without_reason<S>() -> NextTaskState<S, Receipt> {
    NextTaskState::Terminal {
        outcome: TaskOutcome::Aborted {
            reason: None,
            result: None,
        },
    }
}

#[tokio::test]
async fn resumes_an_intent_effect_outcome_task_interrupted_after_its_intent_across_close_and_reopen(
) {
    let (_directory, path) = sqlite_path();
    let service = TransferService::default();
    let transfer = transfer_task(&service, &Arc::new(AtomicBool::new(true)));

    let first = open_tasks(
        sqlite(&path).await,
        std::slice::from_ref(&transfer),
        OpenTasksOptions::default(),
    )
    .await;
    let root = first
        .harness
        .root(crate::harness::RootOptions::default(), context())
        .await
        .unwrap();
    let definition = transfer.as_definition_ref();
    let id = root
        .commit(
            move |tx| async move {
                tx.create_task(
                    definition,
                    json(r#"{"amount":7}"#),
                    TaskOptions {
                        ownership: TaskOwnership::Conversation,
                        conversation_id: None,
                        background: None,
                    },
                )
                .await
            },
            context(),
        )
        .await
        .unwrap();
    first.harness.resume().unwrap();
    until(|| service.calls() == 1).await;
    first.harness.close(context()).await.unwrap();

    let second = open_tasks(
        sqlite(&path).await,
        std::slice::from_ref(&transfer),
        OpenTasksOptions::default(),
    )
    .await;
    // Open reconciled `running` to `pending` and kept the checkpoint and memos; nothing ran yet.
    let record = second
        .harness
        .get_task(id, context())
        .await
        .unwrap()
        .unwrap();
    assert!(!record.abort_requested);
    assert_eq!(
        record
            .memos
            .as_deref()
            .and_then(|memos| memos.get("requested")),
        Some(&json("7"))
    );
    assert_eq!(
        record.state,
        TaskState::Pending {
            checkpoint: json(&format!(r#"{{"phase":"apply","key":"transfer-{id}"}}"#)),
        }
    );
    assert_eq!(service.calls(), 1);
    second.harness.resume().unwrap();
    let receipt = second.harness.wait_for_task(id, context()).await.unwrap();
    assert_eq!(
        receipt.outcome,
        TaskOutcome::Completed {
            result: json(r#"{"receipt":70}"#),
        }
    );
    assert_eq!(service.calls(), 2);
    assert_eq!(service.applied(), 1);
    second.harness.close(context()).await.unwrap();

    let third = open_tasks(
        sqlite(&path).await,
        std::slice::from_ref(&transfer),
        OpenTasksOptions::default(),
    )
    .await;
    assert_eq!(
        third.harness.get_task(id, context()).await.unwrap(),
        Some(receipt.into_record())
    );
    third.harness.close(context()).await.unwrap();
}

/// TS `Abortable`: the run ignores its signal until `run_release`; the abort
/// handler blocks while `abort_gate` is set.
fn abortable_task(
    log: &Log,
    abort_gate: &Arc<AtomicBool>,
    abort_reached: &Deferred,
    run_release: &Deferred,
) -> AnyTask {
    let run_log = log.clone();
    let abort_log = log.clone();
    let abort_reached = abort_reached.clone();
    let run_release = run_release.clone();
    let abort_gate = Arc::clone(abort_gate);
    define_task(
        TaskDefinition::<(), Step, (), ()>::new(
            "test.abortable",
            1,
            |()| Ok(Step::Run),
            move |_task, runtime, cx| {
                let log = abort_log.clone();
                let abort_reached = abort_reached.clone();
                let block = abort_gate.load(Ordering::SeqCst);
                async move {
                    log.push("abort");
                    if block {
                        abort_reached.resolve(());
                        return Err(aborted(&runtime.signal()).await);
                    }
                    runtime
                        .commit(
                            |_tx, _current| async move { Ok(Some(aborted_with("stop"))) },
                            &cx,
                        )
                        .await
                }
            },
        )
        .phase("run", move |_task, _runtime, _cx| {
            let log = run_log.clone();
            let release = run_release.wait();
            async move {
                log.push("run");
                // Ignores the abort signal until released, so the mark is durable while the run is active.
                release.await;
                Ok(())
            }
        }),
    )
    .erase()
}

#[tokio::test]
async fn resumes_abort_work_after_close_at_every_direct_task_abort_stage() {
    let (_directory, path) = sqlite_path();
    let log = Log::default();
    let abort_gate = Arc::new(AtomicBool::new(true));
    let abort_reached = deferred::<()>();
    let run_release = deferred::<()>();
    let abortable = abortable_task(&log, &abort_gate, &abort_reached, &run_release);
    let tasks = std::slice::from_ref(&abortable);

    // Stage 1: the mark is committed while the run invocation is still active.
    let opened = open_tasks(sqlite(&path).await, tasks, OpenTasksOptions::default()).await;
    let id = create_in(&opened.harness, &abortable).await;
    opened.harness.resume().unwrap();
    until(|| log.len() == 1).await;
    let aborting = tokio::spawn(opened.harness.abort_task(id, context()));
    while !opened
        .harness
        .get_task(id, context())
        .await
        .unwrap()
        .is_some_and(|record| record.abort_requested)
    {
        flush().await;
    }
    let closing = tokio::spawn(opened.harness.close(context()));
    run_release.resolve(());
    closing.await.unwrap().unwrap();
    assert_eq!(aborting.await.unwrap().unwrap(), TaskAbortResult::Marked);
    assert_eq!(log.all(), ["run"]);

    // Stage 2: reopen dispatches the abort invocation, never the run; close while it is active.
    let opened = open_tasks(sqlite(&path).await, tasks, OpenTasksOptions::default()).await;
    let record = opened
        .harness
        .get_task(id, context())
        .await
        .unwrap()
        .unwrap();
    assert!(record.abort_requested);
    assert!(matches!(record.state, TaskState::Pending { .. }));
    opened.harness.resume().unwrap();
    abort_reached.wait().await;
    opened.harness.close(context()).await.unwrap();
    assert_eq!(log.all(), ["run", "abort"]);

    // Stage 3: a fresh abort invocation settles the task.
    abort_gate.store(false, Ordering::SeqCst);
    let opened = open_tasks(sqlite(&path).await, tasks, OpenTasksOptions::default()).await;
    opened.harness.resume().unwrap();
    assert_eq!(
        opened
            .harness
            .wait_for_task(id, context())
            .await
            .unwrap()
            .outcome,
        TaskOutcome::Aborted {
            reason: Some("stop".to_owned()),
            result: None,
        }
    );
    opened.harness.close(context()).await.unwrap();
    assert_eq!(log.all(), ["run", "abort", "abort"]);

    // Stage 4: the terminal receipt survives reopen and nothing runs again.
    let opened = open_tasks(sqlite(&path).await, tasks, OpenTasksOptions::default()).await;
    opened.harness.resume().unwrap();
    flush().await;
    assert_eq!(
        opened.harness.abort_task(id, context()).await.unwrap(),
        TaskAbortResult::Terminal
    );
    opened.harness.close(context()).await.unwrap();
    assert_eq!(log.all(), ["run", "abort", "abort"]);
}
