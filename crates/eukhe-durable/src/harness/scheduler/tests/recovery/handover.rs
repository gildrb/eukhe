//! TS `describe("definition handover")`.

use std::sync::{Arc, Mutex, OnceLock, PoisonError};

use serde::{Deserialize, Serialize};

use super::{create_in, until, Log};
use crate::harness::scheduler::DefinitionKept;
use crate::harness::tests::support::{add_task, context, create_registry, Installed};
use crate::harness::tests::task_support::{
    aborted_with, completed, deferred, flush, open_tasks, Deferred, OpenTasksOptions, OpenedTasks,
};
use crate::harness::Harness;
use crate::session::tests::support::{json, ControlledStorage, Gate};
use crate::session::{SessionError, SessionResult};
use crate::storage::MemoryStorage;
use crate::tasks::{define_task, AnyTask, Migrated, NextTaskState, TaskDefinition, TaskRuntime};
use crate::types::{EntryDraft, Storage, StorageWrite, TaskId, TaskOutcome, TaskState, TaskStatus};

#[derive(Clone, Copy, Debug, PartialEq, Serialize, Deserialize)]
#[serde(tag = "phase", rename_all = "lowercase")]
enum Handover {
    A,
    B,
    C,
}

/// TS `Gates`.
#[derive(Clone, Default)]
struct Gates {
    a: Option<Deferred>,
    b: Option<Deferred>,
    on_end: Option<Arc<dyn Fn() + Send + Sync>>,
}

type HandoverMigrate = Box<
    dyn Fn(
            &eukhe_chord::json::JsonValue,
            &eukhe_chord::json::JsonValue,
            u64,
        ) -> SessionResult<Migrated<(), Handover>>
        + Send
        + Sync,
>;

/// TS `handoverTask(label, version, log, { gates, migrate })`.
fn handover_task(
    label: &str,
    version: u64,
    log: &Log,
    gates: Gates,
    migrate: Option<HandoverMigrate>,
) -> AnyTask {
    let Gates { a, b, on_end } = gates;
    let advance = |phase: &'static str, next: Handover, gate: Option<Deferred>| {
        let label = label.to_owned();
        let log = log.clone();
        let on_end = on_end.clone();
        move |_task, runtime: TaskRuntime<(), Handover, (), ()>, cx| {
            let label = label.clone();
            let log = log.clone();
            let gate = gate.as_ref().map(Deferred::wait);
            let on_end = on_end.clone();
            async move {
                log.push(format!("{label}:{phase} start"));
                if let Some(gate) = gate {
                    gate.await;
                }
                runtime
                    .commit(
                        move |_tx, _current| async move {
                            Ok(Some(NextTaskState::Running { checkpoint: next }))
                        },
                        &cx,
                    )
                    .await?;
                // Leave room for a wrongly dispatched successor before this invocation ends.
                flush().await;
                if let Some(on_end) = on_end {
                    on_end();
                }
                log.push(format!("{label}:{phase} end"));
                Ok(())
            }
        }
    };
    let c_label = label.to_owned();
    let c_log = log.clone();
    let abort_label = label.to_owned();
    let abort_log = log.clone();
    let mut definition = TaskDefinition::<(), Handover, (), ()>::new(
        "test.handover",
        version,
        |()| Ok(Handover::A),
        move |_task, runtime, cx| {
            let label = abort_label.clone();
            let log = abort_log.clone();
            async move {
                log.push(format!("{label}:abort"));
                runtime
                    .commit(
                        move |_tx, _current| async move { Ok(Some(aborted_with(&label))) },
                        &cx,
                    )
                    .await
            }
        },
    )
    .phase("a", advance("a", Handover::B, a))
    .phase("b", advance("b", Handover::C, b))
    .phase("c", move |_task, runtime, cx| {
        let label = c_label.clone();
        let log = c_log.clone();
        async move {
            log.push(format!("{label}:c"));
            runtime
                .commit(|_tx, _current| async move { Ok(Some(completed(()))) }, &cx)
                .await
        }
    });
    if let Some(migrate) = migrate {
        definition = definition.migrate(migrate);
    }
    define_task(definition).erase()
}

/// TS `startHandover(log, gates, storage)`.
async fn start_handover(
    log: &Log,
    gates: Gates,
    storage: Arc<dyn Storage>,
) -> (OpenedTasks, Installed, TaskId) {
    let registry = create_registry();
    let old = add_task(&registry, handover_task("old", 1, log, gates, None), None).unwrap();
    let opened = open_tasks(
        storage,
        &[],
        OpenTasksOptions {
            registry: Some(registry),
            ..OpenTasksOptions::default()
        },
    )
    .await;
    let id = create_in(
        &opened.harness,
        &handover_task("old", 1, log, Gates::default(), None),
    )
    .await;
    opened.harness.resume().unwrap();
    until(|| log.len() == 1).await;
    (opened, old, id)
}

fn memory() -> Arc<dyn Storage> {
    Arc::new(MemoryStorage::new())
}

fn gate_a(gate: &Deferred) -> Gates {
    Gates {
        a: Some(gate.clone()),
        ..Gates::default()
    }
}

#[tokio::test]
async fn hands_over_at_the_next_phase_boundary_to_a_same_version_replacement_without_overlap() {
    let log = Log::default();
    let gate = deferred::<()>();
    let (opened, _old, id) = start_handover(&log, gate_a(&gate), memory()).await;
    // The same extension name replaces the old one in place.
    add_task(
        &opened.registry,
        handover_task("new", 1, &log, Gates::default(), None),
        None,
    )
    .unwrap();
    gate.resolve(());
    opened.harness.wait_for_task(id, context()).await.unwrap();
    assert_eq!(
        log.all(),
        [
            "old:a start",
            "old:a end",
            "new:b start",
            "new:b end",
            "new:c"
        ]
    );
    opened.harness.close(context()).await.unwrap();
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
#[serde(tag = "phase", rename_all = "lowercase")]
enum Memoed {
    A,
    B,
}

#[tokio::test]
async fn keeps_the_memos_across_a_handover() {
    let log = Log::default();
    let gate = deferred::<()>();
    let reached = deferred::<()>();
    let memo_task = |label: &str| {
        let a_label = label.to_owned();
        let b_label = label.to_owned();
        let gate = gate.clone();
        let reached = reached.clone();
        let log = log.clone();
        define_task(
            TaskDefinition::<(), Memoed, String, ()>::new(
                "test.handover-memo",
                1,
                |()| Ok(Memoed::A),
                |_task, _runtime, _cx| async { Ok(()) },
            )
            .phase("a", move |_task, runtime, cx| {
                let label = a_label.clone();
                let gate = gate.wait();
                let reached = reached.clone();
                async move {
                    runtime.memo_or("picked", &label, &cx).await?;
                    reached.resolve(());
                    gate.await;
                    runtime
                        .commit(
                            |_tx, _current| async move {
                                Ok(Some(NextTaskState::Running {
                                    checkpoint: Memoed::B,
                                }))
                            },
                            &cx,
                        )
                        .await
                }
            })
            .phase("b", move |_task, runtime, cx| {
                let label = b_label.clone();
                let log = log.clone();
                async move {
                    // The candidate loses to the memo the old definition stored.
                    let picked = runtime.memo_or("picked", &label, &cx).await?;
                    log.push(format!("{label}:b {picked}"));
                    runtime
                        .commit(
                            move |_tx, _current| async move { Ok(Some(completed(picked))) },
                            &cx,
                        )
                        .await
                }
            }),
        )
        .erase()
    };
    let registry = create_registry();
    add_task(&registry, memo_task("old"), None).unwrap();
    let harness = open_tasks(
        memory(),
        &[],
        OpenTasksOptions {
            registry: Some(registry.clone()),
            ..OpenTasksOptions::default()
        },
    )
    .await
    .harness;
    let id = create_in(&harness, &memo_task("old")).await;
    harness.resume().unwrap();
    reached.wait().await;
    add_task(&registry, memo_task("new"), None).unwrap();
    gate.resolve(());
    let receipt = harness.wait_for_task(id, context()).await.unwrap();
    assert_eq!(
        receipt.outcome,
        TaskOutcome::Completed {
            result: json(r#""old""#),
        }
    );
    assert_eq!(log.all(), ["new:b old"]);
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn hands_over_to_a_newer_version_with_a_migration() {
    let log = Log::default();
    let gate = deferred::<()>();
    let (opened, _old, id) = start_handover(&log, gate_a(&gate), memory()).await;
    // The same extension name replaces the old one in place.
    add_task(
        &opened.registry,
        handover_task(
            "v2",
            2,
            &log,
            Gates::default(),
            Some(Box::new(|_, _, _| {
                Ok(Migrated {
                    input: (),
                    checkpoint: Handover::C,
                })
            })),
        ),
        None,
    )
    .unwrap();
    gate.resolve(());
    let receipt = opened.harness.wait_for_task(id, context()).await.unwrap();
    assert_eq!(receipt.version, 2);
    assert_eq!(log.all(), ["old:a start", "old:a end", "v2:c"]);
    opened.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn hands_over_to_a_newer_version_whose_migration_fails_and_leaves_the_task_blocked() {
    let log = Log::default();
    let gate = deferred::<()>();
    let (opened, _old, id) = start_handover(&log, gate_a(&gate), memory()).await;
    // The same extension name replaces the old one in place.
    add_task(
        &opened.registry,
        handover_task(
            "broken",
            2,
            &log,
            Gates::default(),
            Some(Box::new(|_, _, _| {
                Err(SessionError::error("broken migration"))
            })),
        ),
        None,
    )
    .unwrap();
    gate.resolve(());
    until(|| opened.reports.len() == 1).await;
    flush().await;
    let record = opened
        .harness
        .get_task(id, context())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(record.version, 1);
    assert_eq!(
        record.state,
        TaskState::Pending {
            checkpoint: json(r#"{"phase":"b"}"#),
        }
    );
    assert_eq!(log.all(), ["old:a start", "old:a end"]);
    opened.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn keeps_running_under_the_old_definition_when_the_replacement_is_missing_or_cannot_take_the_task(
) {
    let log = Log::default();
    let gate_a = deferred::<()>();
    let gate_b = deferred::<()>();
    let (opened, old, id) = start_handover(
        &log,
        Gates {
            a: Some(gate_a.clone()),
            b: Some(gate_b.clone()),
            on_end: None,
        },
        memory(),
    )
    .await;
    old.dispose();
    gate_a.resolve(());
    until(|| log.contains("old:b start")).await;
    // A newer definition without a migration cannot take the task either.
    add_task(
        &opened.registry,
        handover_task("incompatible", 2, &log, Gates::default(), None),
        None,
    )
    .unwrap();
    gate_b.resolve(());
    opened.harness.wait_for_task(id, context()).await.unwrap();
    assert_eq!(
        log.all(),
        [
            "old:a start",
            "old:a end",
            "old:b start",
            "old:b end",
            "old:c"
        ]
    );
    let causes: Vec<Option<&'static str>> = opened
        .reports
        .all()
        .iter()
        .map(|report| match report {
            SessionError::Other(error) => error
                .downcast_ref::<DefinitionKept>()
                .map(DefinitionKept::cause),
            _ => None,
        })
        .collect();
    assert_eq!(causes, [Some("missing_task"), Some("incompatible_task")]);
    opened.harness.close(context()).await.unwrap();
}

type HandoverRuntime = TaskRuntime<(), Handover, (), ()>;

/// What the TS `Old` task of the queued-commit test shares with the test.
struct OldShared {
    gate: Deferred,
    storage: Arc<ControlledStorage>,
    held: Arc<Mutex<Option<Gate>>>,
    old_runtime: Arc<Mutex<Option<HandoverRuntime>>>,
    harness_ref: Arc<OnceLock<Harness>>,
}

/// TS `Old`: phase `a` records its runtime, advances to `b` once `gate`
/// opens, then holds commits and queues an unrelated commit.
fn queued_old_task(shared: OldShared) -> AnyTask {
    let OldShared {
        gate,
        storage,
        held,
        old_runtime,
        harness_ref,
    } = shared;
    define_task(
        TaskDefinition::<(), Handover, (), ()>::new(
            "test.handover",
            1,
            |()| Ok(Handover::A),
            |_task, _runtime, _cx| async { Ok(()) },
        )
        .phase("a", move |task, runtime, cx| {
            *old_runtime.lock().unwrap_or_else(PoisonError::into_inner) = Some(runtime.clone());
            let gate = gate.wait();
            let storage = Arc::clone(&storage);
            let held = Arc::clone(&held);
            let harness = harness_ref.get().expect("harness is set").clone();
            async move {
                gate.await;
                runtime
                    .commit(
                        |_tx, _current| async move {
                            Ok(Some(NextTaskState::Running {
                                checkpoint: Handover::B,
                            }))
                        },
                        &cx,
                    )
                    .await?;
                // Hold the line with an unrelated commit so the handover commit queues behind it.
                *held.lock().unwrap_or_else(PoisonError::into_inner) = Some(storage.hold_commits());
                let conversation_id = task.conversation_id;
                drop(tokio::spawn(harness.commit(
                    move |tx| async move {
                        tx.append_entry(conversation_id, EntryDraft::new("blocker"))
                            .await?;
                        Ok(())
                    },
                    &cx,
                )));
                Ok(())
            }
        })
        .phase("b", |_task, _runtime, _cx| async { Ok(()) })
        .phase("c", |_task, _runtime, _cx| async { Ok(()) }),
    )
    .erase()
}

#[tokio::test]
async fn rejects_a_runtime_commit_of_the_old_invocation_queued_behind_its_handover_commit() {
    let log = Log::default();
    let gate = deferred::<()>();
    let storage = ControlledStorage::new();
    let held: Arc<Mutex<Option<Gate>>> = Arc::default();
    let old_runtime: Arc<Mutex<Option<HandoverRuntime>>> = Arc::default();
    let harness_ref: Arc<OnceLock<Harness>> = Arc::default();
    let registry = create_registry();
    let old = queued_old_task(OldShared {
        gate: gate.clone(),
        storage: Arc::clone(&storage),
        held: Arc::clone(&held),
        old_runtime: Arc::clone(&old_runtime),
        harness_ref: Arc::clone(&harness_ref),
    });
    add_task(&registry, old.clone(), None).unwrap();
    let opened = open_tasks(
        Arc::clone(&storage) as Arc<dyn Storage>,
        &[],
        OpenTasksOptions {
            registry: Some(registry.clone()),
            ..OpenTasksOptions::default()
        },
    )
    .await;
    let harness = opened.harness;
    assert!(harness_ref.set(harness.clone()).is_ok());
    let id = create_in(&harness, &old).await;
    harness.resume().unwrap();
    until(|| {
        old_runtime
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .is_some()
    })
    .await;
    // The same extension name replaces the old one in place.
    add_task(
        &registry,
        handover_task("new", 1, &log, Gates::default(), None),
        None,
    )
    .unwrap();
    gate.resolve(());
    until(|| {
        held.lock()
            .unwrap_or_else(PoisonError::into_inner)
            .is_some()
    })
    .await;
    let entered = held
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .as_ref()
        .map(Gate::entered)
        .expect("held");
    entered.await;
    flush().await;
    // Queued behind the handover commit while the invocation has not ended yet.
    let runtime = old_runtime
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
        .expect("old runtime");
    let late = tokio::spawn(runtime.commit(
        |_tx, _current| async move { Ok(Some(completed(()))) },
        context(),
    ));
    held.lock()
        .unwrap_or_else(PoisonError::into_inner)
        .as_ref()
        .expect("held")
        .release();
    let error = late.await.unwrap().expect_err("the late commit rejects");
    assert!(
        error.to_string().contains("invocation has ended"),
        "{error}"
    );
    harness.wait_for_task(id, context()).await.unwrap();
    assert_eq!(log.all(), ["new:b start", "new:b end", "new:c"]);
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn preserves_an_abort_mark_that_races_the_handover_commit_the_new_definition_aborts() {
    let log = Log::default();
    let gate = deferred::<()>();
    let storage = ControlledStorage::new();
    let held: Arc<Mutex<Option<Gate>>> = Arc::default();
    // The progress commit landed; hold the next commit, the handover, and queue the abort mark behind it.
    let gates = {
        let storage = Arc::clone(&storage);
        let held = Arc::clone(&held);
        Gates {
            a: Some(gate.clone()),
            b: None,
            on_end: Some(Arc::new(move || {
                held.lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .get_or_insert_with(|| storage.hold_commits());
            })),
        }
    };
    let (opened, _old, id) =
        start_handover(&log, gates, Arc::clone(&storage) as Arc<dyn Storage>).await;
    // The same extension name replaces the old one in place.
    add_task(
        &opened.registry,
        handover_task("new", 1, &log, Gates::default(), None),
        None,
    )
    .unwrap();
    gate.resolve(());
    until(|| {
        held.lock()
            .unwrap_or_else(PoisonError::into_inner)
            .is_some()
    })
    .await;
    let entered = held
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .as_ref()
        .map(Gate::entered)
        .expect("held");
    entered.await;
    let aborting = tokio::spawn(opened.harness.abort_task(id, context()));
    held.lock()
        .unwrap_or_else(PoisonError::into_inner)
        .as_ref()
        .expect("held")
        .release();
    assert_eq!(
        aborting.await.unwrap().unwrap(),
        crate::harness::TaskAbortResult::Marked
    );
    assert_eq!(
        opened
            .harness
            .wait_for_task(id, context())
            .await
            .unwrap()
            .outcome,
        TaskOutcome::Aborted {
            reason: Some("new".to_owned()),
            result: None,
        }
    );
    let states: Vec<String> = storage
        .commits()
        .iter()
        .flatten()
        .filter_map(|write| match write {
            StorageWrite::Task { value } if value.id == id => Some(format!(
                "{}{}",
                status_name(value.state.status()),
                if value.abort_requested { "+mark" } else { "" }
            )),
            _ => None,
        })
        .collect();
    // created, reserved, progress, handover, mark, abort reservation, aborted
    assert_eq!(
        states,
        [
            "pending",
            "running",
            "running",
            "pending",
            "pending+mark",
            "running+mark",
            "terminal+mark",
        ]
    );
    assert_eq!(log.all(), ["old:a start", "old:a end", "new:abort"]);
    opened.harness.close(context()).await.unwrap();
}

fn status_name(status: TaskStatus) -> &'static str {
    match status {
        TaskStatus::Pending => "pending",
        TaskStatus::Running => "running",
        TaskStatus::Waiting => "waiting",
        TaskStatus::Completing => "completing",
        TaskStatus::Terminal => "terminal",
    }
}
