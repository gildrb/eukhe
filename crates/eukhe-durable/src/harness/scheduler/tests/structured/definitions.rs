//! `describe("definitions and waits")`.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::json::{from_json, to_json};
use serde::{Deserialize, Serialize};

use super::{
    create, inspected, json, open_memory_nodes, outcome_of, owned, spawn_and_finish, state, status,
    until_status, wait_on, Behavior, Opened, Script, OWN_CONVERSATION,
};
use crate::harness::tests::support::{add_task, context};
use crate::harness::types::{TaskBlockedReason, TaskInspectionState};
use crate::harness::TaskAbortResult;
use crate::session::SessionError;
use crate::tasks::{define_task, AnyTask, Migrated, NextTaskState, Task, TaskDefinition};
use crate::types::{JoinPolicy, TaskId, TaskOutcome, TaskOutcomeStatus, TaskStatus};

/// Input of `test.versioned`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct VersionedInput {
    on: Vec<TaskId>,
}

/// Checkpoint of `test.versioned`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "phase", rename_all = "camelCase")]
enum VersionedCheckpoint {
    Wait,
    Resume,
    Migrated,
}

type Versioned = Task<VersionedInput, VersionedCheckpoint, String, ()>;

fn completed<S>(result: &str) -> NextTaskState<S, String> {
    NextTaskState::Terminal {
        outcome: TaskOutcome::Completed {
            result: result.to_owned(),
        },
    }
}

fn aborted<S>() -> NextTaskState<S, String> {
    NextTaskState::Terminal {
        outcome: TaskOutcome::Aborted {
            reason: None,
            result: None,
        },
    }
}

/// A waiter of its own kind, so its definition can be removed or replaced.
fn versioned(version: u64) -> Versioned {
    let definition = TaskDefinition::<VersionedInput, VersionedCheckpoint, String, ()>::new(
        "test.versioned",
        version,
        |_| Ok(VersionedCheckpoint::Wait),
        |_, runtime, cx| async move {
            runtime
                .commit(|_, _| async { Ok(Some(aborted())) }, &cx)
                .await
        },
    )
    .phase("wait", |task, runtime, cx| async move {
        let on = task.input.on;
        runtime
            .commit(
                move |_, _| async move {
                    Ok(Some(NextTaskState::Waiting {
                        checkpoint: VersionedCheckpoint::Resume,
                        on,
                        policy: JoinPolicy::AllSettled,
                    }))
                },
                &cx,
            )
            .await
    })
    .phase("resume", |_, runtime, cx| async move {
        runtime
            .commit(|_, _| async { Ok(Some(completed("v1"))) }, &cx)
            .await
    })
    .phase("migrated", |_, runtime, cx| async move {
        runtime
            .commit(|_, _| async { Ok(Some(completed("v2"))) }, &cx)
            .await
    });
    define_task(if version == 2 {
        definition.migrate(|input, _, _| {
            Ok(Migrated {
                input: from_json(input)?,
                checkpoint: VersionedCheckpoint::Migrated,
            })
        })
    } else {
        definition
    })
}

/// `root.commit((tx) => tx.createTask(versioned(1), { on }, OWN_CONVERSATION))`.
async fn start_waiter(opened: &Opened, on: TaskId) -> TaskId {
    opened
        .root
        .commit(
            move |tx| async move {
                let input = to_json(&VersionedInput { on: vec![on] })?;
                tx.create_task(
                    versioned(1).erase().as_definition_ref(),
                    input,
                    OWN_CONVERSATION,
                )
                .await
            },
            context(),
        )
        .await
        .unwrap()
}

#[tokio::test]
async fn keeps_a_waiting_task_blocked_without_its_definition_and_resumes_it_migrated_under_a_newer_one(
) {
    let script = Script::new();
    let opened = open_memory_nodes(&script).await;
    let (harness, registry) = (&opened.harness, &opened.registry);
    let registration = add_task(registry, versioned(1).erase(), None).unwrap();
    let other = script.start(&opened.root, "other").await;
    let waiter = start_waiter(&opened, other).await;
    until_status(harness, waiter, TaskStatus::Waiting).await;
    registration.dispose();
    script.open("other");
    harness.wait_for_task(other, context()).await.unwrap();
    assert!(matches!(
        inspected(harness, waiter).await,
        Some(TaskInspectionState::Blocked {
            reason: TaskBlockedReason::MissingTask,
            error: None,
        })
    ));
    assert_eq!(status(harness, waiter).await, TaskStatus::Waiting);
    add_task(registry, versioned(2).erase(), None).unwrap();
    assert_eq!(
        harness
            .wait_for_task(waiter, context())
            .await
            .unwrap()
            .outcome,
        TaskOutcome::Completed {
            result: json(r#""v2""#)
        }
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn orphans_an_aborted_waiting_task_without_its_definition_at_once_leaving_the_task_it_waits_on_running(
) {
    let script = Script::new();
    let opened = open_memory_nodes(&script).await;
    let (harness, registry) = (&opened.harness, &opened.registry);
    let registration = add_task(registry, versioned(1).erase(), None).unwrap();
    let other = script.start(&opened.root, "other").await;
    let waiter = start_waiter(&opened, other).await;
    until_status(harness, waiter, TaskStatus::Waiting).await;
    registration.dispose();
    assert_eq!(
        harness.abort_task(waiter, context()).await.unwrap(),
        TaskAbortResult::Marked
    );
    assert_eq!(
        state(harness, waiter).await.outcome(),
        Some(&TaskOutcome::Orphaned {
            reason: "missing_task".to_owned()
        })
    );
    assert_eq!(status(harness, other).await, TaskStatus::Running);
    script.open("other");
    harness.close(context()).await.unwrap();
}

/// Checkpoint of `test.holder`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "phase", rename_all = "camelCase")]
enum HolderCheckpoint {
    Run,
}

/// `test.holder` of `version`: spawns `child`, then completes with `held`.
fn holder(node: &AnyTask, version: u64) -> Task<(), HolderCheckpoint, String, ()> {
    let node = node.clone();
    define_task(
        TaskDefinition::<(), HolderCheckpoint, String, ()>::new(
            "test.holder",
            version,
            |()| Ok(HolderCheckpoint::Run),
            |_, runtime, cx| async move {
                runtime
                    .commit(|_, _| async { Ok(Some(aborted())) }, &cx)
                    .await
            },
        )
        .phase("run", move |task, runtime, cx| {
            let node = node.clone();
            async move {
                let owner = task.id.erase();
                runtime
                    .commit(
                        move |tx, _| async move {
                            create(&tx, &node, "child", owned(owner)).await?;
                            Ok(None)
                        },
                        &cx,
                    )
                    .await?;
                runtime
                    .commit(|_, _| async { Ok(Some(completed("held"))) }, &cx)
                    .await
            }
        })
        .migrate(|_, _, _| Err(SessionError::error("never migrates"))),
    )
}

#[tokio::test]
async fn never_migrates_a_held_outcome_a_newer_definition_leaves_it_and_its_version_alone() {
    let script = Script::new();
    let Opened {
        harness,
        root,
        registry,
        reports,
    } = open_memory_nodes(&script).await;
    add_task(&registry, holder(script.node(), 1).erase(), None).unwrap();
    let task = holder(script.node(), 1).erase();
    let parent = root
        .commit(
            move |tx| async move {
                tx.create_task(task.as_definition_ref(), to_json(&())?, OWN_CONVERSATION)
                    .await
            },
            context(),
        )
        .await
        .unwrap();
    until_status(&harness, parent, TaskStatus::Completing).await;
    // The same extension name replaces the old one in place.
    add_task(&registry, holder(script.node(), 2).erase(), None).unwrap();
    script.open("child");
    let settled_parent = harness.wait_for_task(parent, context()).await.unwrap();
    assert_eq!(
        settled_parent.outcome,
        TaskOutcome::Completed {
            result: json(r#""held""#)
        }
    );
    assert_eq!(settled_parent.version, 1);
    assert!(reports.all().is_empty(), "{:?}", reports.all());
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn treats_a_held_task_as_live_outcomes_rejects_and_a_task_waiting_on_it_resumes_at_its_final_commit(
) {
    let script = Script::new();
    let Opened { harness, root, .. } = open_memory_nodes(&script).await;
    spawn_and_finish(&script, "held", "child");
    let held = script.start(&root, "held").await;
    until_status(&harness, held, TaskStatus::Completing).await;
    let rejection = Arc::new(Mutex::new(String::new()));
    let sink = Arc::clone(&rejection);
    script.script(
        "reader",
        Behavior::default().run(move |_, runtime, cx| {
            let sink = Arc::clone(&sink);
            async move {
                let read = match runtime.outcomes(&[held], &cx).await {
                    Ok(_) => "resolved".to_owned(),
                    Err(error) => error.to_string(),
                };
                *sink.lock().unwrap_or_else(PoisonError::into_inner) = read;
                runtime
                    .commit(
                        move |_, _| async move {
                            Ok(Some(wait_on(vec![held], JoinPolicy::AllSettled, 1)))
                        },
                        &cx,
                    )
                    .await
            }
        }),
    );
    let reader = script.start(&root, "reader").await;
    until_status(&harness, reader, TaskStatus::Waiting).await;
    assert_eq!(
        *rejection.lock().unwrap_or_else(PoisonError::into_inner),
        format!("Task {held} is not terminal")
    );
    script.open("child");
    assert_eq!(
        outcome_of(&harness, reader).await,
        TaskOutcomeStatus::Completed
    );
    assert!(script.logged("resume:reader"));
    harness.close(context()).await.unwrap();
}
