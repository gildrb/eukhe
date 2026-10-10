//! Port of `test/harness-cancellation-barrier.test.ts`: work below a
//! cancelled owner.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::json::JsonValue;
use futures::FutureExt;

use crate::harness::tests::commit_hook::CommitHooked;
use crate::harness::tests::support::context;
use crate::harness::tests::task_support::{
    aborted, deferred, eventually, flush, open_tasks, OpenTasksOptions,
};
use crate::harness::types::TaskInspectionState;
use crate::harness::RootOptions;
use crate::session::Session;
use crate::storage::MemoryStorage;
use crate::tasks::{define_task, NextTaskState, Task, TaskDefinition};
use crate::types::{
    ConversationId, ConversationOwnership, JoinPolicy, Storage, StorageWrite, TaskAbortReason,
    TaskId, TaskOptions, TaskOutcome, TaskOutcomeError, TaskOutcomeStatus, TaskOwnership,
    TaskState, TaskStatus,
};

type NullTask = Task<JsonValue, JsonValue, JsonValue, ()>;

fn json(text: &str) -> JsonValue {
    JsonValue::parse(text).expect("valid JSON literal")
}

fn aborted_state() -> NextTaskState<JsonValue, JsonValue> {
    NextTaskState::Terminal {
        outcome: TaskOutcome::Aborted {
            reason: None,
            result: None,
        },
    }
}

/// TS `Dormant` (or a copy named `name`): runs until aborted; its abort
/// handler ends it `aborted`.
fn dormant(name: &'static str) -> NullTask {
    define_task(
        TaskDefinition::<JsonValue, JsonValue, JsonValue, ()>::new(
            name,
            1,
            |_: &JsonValue| Ok(json(r#"{"phase":"work"}"#)),
            |_task, runtime, cx| async move {
                runtime
                    .commit(|_tx, _current| async { Ok(Some(aborted_state())) }, &cx)
                    .await
            },
        )
        .phase("work", |_task, runtime, _cx| async move {
            aborted(&runtime.signal()).await;
            Ok(())
        }),
    )
}

fn owned_by(task_id: TaskId) -> TaskOptions {
    TaskOptions {
        ownership: TaskOwnership::Task { task_id },
        conversation_id: None,
        background: None,
        abandon_on_restart: None,
    }
}

fn in_conversation(conversation_id: ConversationId) -> TaskOptions {
    TaskOptions {
        ownership: TaskOwnership::Conversation,
        conversation_id: Some(conversation_id),
        background: None,
        abandon_on_restart: None,
    }
}

/// `session.commit((tx) => tx.createTask(task, null, options))`.
async fn create(session: &Session, task: &NullTask, options: TaskOptions) -> TaskId {
    let definition = task.as_definition_ref();
    session
        .commit(
            move |tx| async move { tx.create_task(definition, JsonValue::Null, options).await },
            context(),
        )
        .await
        .unwrap()
}

/// An ownerless conversation created through a Session over `storage`.
async fn ownerless(session: &Session) -> ConversationId {
    session
        .commit(
            |tx| async move {
                Ok(tx
                    .create_conversation(ConversationOwnership::Ownerless)
                    .await?
                    .id)
            },
            context(),
        )
        .await
        .unwrap()
}

#[tokio::test]
#[expect(clippy::too_many_lines, reason = "one TS case, ported whole")]
async fn does_not_start_its_next_phase_while_the_cascade_that_marks_it_has_not_committed() {
    // TS `HoldMarks`: holds every commit that abort-marks `target`, while set, until released.
    let target: Arc<Mutex<Option<TaskId>>> = Arc::default();
    let held = deferred::<()>();
    let release = deferred::<()>();
    let storage = {
        let (target, held, release) = (Arc::clone(&target), held.clone(), release.clone());
        CommitHooked::new(
            Arc::new(MemoryStorage::new()),
            Arc::new(move |writes: &[StorageWrite]| {
                let id = *target.lock().unwrap_or_else(PoisonError::into_inner);
                let marks = writes.iter().any(|write| {
                    matches!(write, StorageWrite::Task { value }
                        if Some(value.id) == id && value.abort_requested)
                });
                let (held, release) = (held.clone(), release.clone());
                async move {
                    if marks {
                        held.resolve(());
                        release.wait().await;
                    }
                    Ok(())
                }
                .boxed()
            }),
        )
    };
    let entered = deferred::<()>();
    let advance = deferred::<()>();
    let ran_next = Arc::new(AtomicBool::new(false));
    let child_task: NullTask = {
        let (entered, advance, ran_next) =
            (entered.clone(), advance.clone(), Arc::clone(&ran_next));
        define_task(
            TaskDefinition::<JsonValue, JsonValue, JsonValue, ()>::new(
                "test.child",
                1,
                |_: &JsonValue| Ok(json(r#"{"phase":"first"}"#)),
                |_task, runtime, cx| async move {
                    runtime
                        .commit(|_tx, _current| async { Ok(Some(aborted_state())) }, &cx)
                        .await
                },
            )
            .phase("first", move |_task, runtime, cx| {
                let (entered, advance) = (entered.clone(), advance.clone());
                async move {
                    entered.resolve(());
                    advance.wait().await;
                    runtime
                        .commit(
                            |_tx, _current| async {
                                Ok(Some(NextTaskState::Running {
                                    checkpoint: json(r#"{"phase":"next"}"#),
                                }))
                            },
                            &cx,
                        )
                        .await
                }
            })
            .phase("next", move |_task, runtime, _cx| {
                let ran_next = Arc::clone(&ran_next);
                async move {
                    ran_next.store(true, Ordering::SeqCst);
                    aborted(&runtime.signal()).await;
                    Ok(())
                }
            }),
        )
    };
    let parent_task = dormant("test.dormant");
    let opened = open_tasks(
        Arc::clone(&storage) as Arc<dyn Storage>,
        &[parent_task.erase(), child_task.erase()],
        OpenTasksOptions::default(),
    )
    .await;
    let harness = opened.harness;
    let root = harness
        .root(RootOptions::default(), context())
        .await
        .unwrap();
    let parent = {
        let definition = parent_task.as_definition_ref();
        root.commit(
            move |tx| async move {
                tx.create_task(
                    definition,
                    JsonValue::Null,
                    TaskOptions {
                        ownership: TaskOwnership::Conversation,
                        conversation_id: None,
                        background: None,
                        abandon_on_restart: None,
                    },
                )
                .await
            },
            context(),
        )
        .await
        .unwrap()
    };
    let child = {
        let definition = child_task.as_definition_ref();
        root.commit(
            move |tx| async move {
                tx.create_task(definition, JsonValue::Null, owned_by(parent))
                    .await
            },
            context(),
        )
        .await
        .unwrap()
    };
    *target.lock().unwrap_or_else(PoisonError::into_inner) = Some(child);
    harness.resume().unwrap();
    entered.wait().await;
    let aborting = tokio::spawn(harness.abort_task(parent, context()));
    held.wait().await;
    // The parent's request is durable, the cascade's mark of the child is not: its phase must not advance.
    advance.resolve(());
    for _ in 0..5 {
        flush().await;
    }
    assert!(!ran_next.load(Ordering::SeqCst));
    release.resolve(());
    assert_eq!(
        harness
            .wait_for_task(child, context())
            .await
            .unwrap()
            .outcome
            .status(),
        TaskOutcomeStatus::Aborted
    );
    aborting.await.unwrap().unwrap();
    assert!(!ran_next.load(Ordering::SeqCst));
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn lets_a_fail_fast_request_in_the_same_pass_override_a_restart_mark() {
    let storage = Arc::new(MemoryStorage::new());
    let session = Session::new(Arc::clone(&storage) as Arc<dyn Storage>);
    let dormant = dormant("test.dormant");
    let conversation = ownerless(&session).await;
    let parent = create(&session, &dormant, in_conversation(conversation)).await;
    let failed = create(&session, &dormant, owned_by(parent)).await;
    let child = create(&session, &dormant, owned_by(parent)).await;
    // A restart-abandoned owner that waits failFast on a failed child and a live one.
    let mut owner = storage.task(parent, context()).await.unwrap().unwrap();
    let mut failed_record = storage.task(failed, context()).await.unwrap().unwrap();
    owner.abort_requested = true;
    owner.abort_reason = Some(TaskAbortReason::Restart);
    owner.state = TaskState::Waiting {
        checkpoint: json(r#"{"phase":"work"}"#),
        on: vec![failed, child],
        policy: JoinPolicy::FailFast,
    };
    failed_record.state = TaskState::Terminal {
        outcome: TaskOutcome::Failed {
            error: TaskOutcomeError {
                message: "failed".to_owned(),
                detail: None,
            },
            result: None,
        },
    };
    storage
        .commit(
            &[
                StorageWrite::Task { value: owner },
                StorageWrite::Task {
                    value: failed_record,
                },
            ],
            context(),
        )
        .await
        .unwrap();
    // The child's definition is missing: a restart mark would keep it waiting, a request orphans it.
    let harness = open_tasks(storage, &[], OpenTasksOptions::default())
        .await
        .harness;
    harness.resume().unwrap();
    let terminal = |harness: &crate::harness::Harness| {
        let harness = harness.clone();
        async move {
            harness
                .get_task(child, context())
                .await
                .unwrap()
                .is_some_and(|record| record.state.status() == TaskStatus::Terminal)
        }
    };
    eventually(|| terminal(&harness)).await;
    let record = harness.get_task(child, context()).await.unwrap().unwrap();
    assert!(
        matches!(
            record.state.outcome(),
            Some(TaskOutcome::Orphaned { reason }) if reason == "missing_task"
        ),
        "{:?}",
        record.state
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn upgrades_restart_marks_down_the_tree_when_an_abort_is_requested_above_them() {
    let storage = Arc::new(MemoryStorage::new());
    let session = Session::new(Arc::clone(&storage) as Arc<dyn Storage>);
    let dormant = dormant("test.dormant");
    let missing = self::dormant("test.missing");
    let conversation = ownerless(&session).await;
    let top = create(&session, &dormant, in_conversation(conversation)).await;
    let middle = create(
        &session,
        &dormant,
        TaskOptions {
            abandon_on_restart: Some(true),
            ..owned_by(top)
        },
    )
    .await;
    let leaf = create(&session, &missing, owned_by(middle)).await;
    // Only Dormant is registered: the leaf waits for its definition under the restart cascade.
    let harness = open_tasks(storage, &[dormant.erase()], OpenTasksOptions::default())
        .await
        .harness;
    harness.resume().unwrap();
    let restart = |harness: &crate::harness::Harness| {
        let harness = harness.clone();
        async move {
            harness
                .get_task(leaf, context())
                .await
                .unwrap()
                .is_some_and(|record| record.abort_reason == Some(TaskAbortReason::Restart))
        }
    };
    eventually(|| restart(&harness)).await;
    let blocked = |harness: &crate::harness::Harness| {
        let harness = harness.clone();
        async move {
            harness
                .inspect(context())
                .await
                .unwrap()
                .tasks
                .into_iter()
                .find(|task| task.record.id == leaf)
                .is_some_and(|task| matches!(task.state, TaskInspectionState::Blocked { .. }))
        }
    };
    eventually(|| blocked(&harness)).await;
    assert_ne!(
        harness
            .get_task(leaf, context())
            .await
            .unwrap()
            .unwrap()
            .state
            .status(),
        TaskStatus::Terminal
    );
    // A request on the top task reaches the leaf two levels down, which is then orphaned.
    harness.abort_task(top, context()).await.unwrap();
    for (id, status) in [
        (leaf, TaskOutcomeStatus::Orphaned),
        (middle, TaskOutcomeStatus::Aborted),
        (top, TaskOutcomeStatus::Aborted),
    ] {
        let settled = harness.wait_for_task(id, context()).await.unwrap();
        assert_eq!(settled.outcome.status(), status);
    }
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn marks_a_flagged_task_that_holds_its_outcome_aborting_its_owned_work_and_keeps_the_outcome()
{
    let storage = Arc::new(MemoryStorage::new());
    let session = Session::new(Arc::clone(&storage) as Arc<dyn Storage>);
    let dormant = dormant("test.dormant");
    let conversation = ownerless(&session).await;
    let holder = create(
        &session,
        &dormant,
        TaskOptions {
            abandon_on_restart: Some(true),
            ..in_conversation(conversation)
        },
    )
    .await;
    let child = create(&session, &dormant, owned_by(holder)).await;
    let mut record = storage.task(holder, context()).await.unwrap().unwrap();
    record.state = TaskState::Completing {
        outcome: TaskOutcome::Completed {
            result: JsonValue::Null,
        },
    };
    storage
        .commit(&[StorageWrite::Task { value: record }], context())
        .await
        .unwrap();
    let harness = open_tasks(storage, &[dormant.erase()], OpenTasksOptions::default())
        .await
        .harness;
    harness.resume().unwrap();
    assert_eq!(
        harness
            .wait_for_task(child, context())
            .await
            .unwrap()
            .outcome
            .status(),
        TaskOutcomeStatus::Aborted
    );
    let settled = harness.wait_for_task(holder, context()).await.unwrap();
    assert_eq!(settled.abort_reason, Some(TaskAbortReason::Restart));
    assert_eq!(settled.outcome.status(), TaskOutcomeStatus::Completed);
    harness.close(context()).await.unwrap();
}
