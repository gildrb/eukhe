//! `describe("completing")`.

use eukhe_chord::json::JsonValue;

use super::{
    create, end, in_conversation, inspected, json, open_memory_nodes, outcome_of,
    owned_conversation, running, spawn_and_finish, state, status, until, until_status, Behavior,
    End, Opened, Script, TASK_NOTES,
};
use crate::harness::tests::support::context;
use crate::harness::tests::task_support::settled;
use crate::harness::types::TaskInspectionState;
use crate::harness::TaskAbortResult;
use crate::session::SessionError;
use crate::types::{TaskOutcome, TaskOutcomeStatus, TaskState, TaskStatus};

/// `{ status: "completed", result: "parent" }`.
fn completed_parent() -> TaskOutcome {
    TaskOutcome::Completed {
        result: json(r#""parent""#),
    }
}

#[tokio::test]
async fn holds_a_finished_task_until_its_owned_work_drains_waiters_and_task_documents_wait_for_the_final_commit(
) {
    let script = Script::new();
    let Opened { harness, root, .. } = open_memory_nodes(&script).await;
    script.script(
        "parent",
        Behavior::default().run(|script, runtime, cx| async move {
            let owner = runtime.task_id().erase();
            runtime
                .commit(
                    move |tx, _| async move {
                        tx.doc(&TASK_NOTES, owner).await?.set("text", "notes")?;
                        let child = script.spawn(&tx, owner, "child").await?;
                        script.slot("child").resolve(child);
                        Ok(Some(running(1)))
                    },
                    &cx,
                )
                .await
        }),
    );
    let parent = script.start(&root, "parent").await;
    until_status(&harness, parent, TaskStatus::Completing).await;
    assert_eq!(
        state(&harness, parent).await,
        TaskState::Completing {
            outcome: completed_parent()
        }
    );
    let waiter = tokio::spawn(harness.wait_for_task(parent, context()));
    assert!(!settled(&waiter).await);
    assert_eq!(
        harness
            .snapshot(&TASK_NOTES, parent, context())
            .await
            .unwrap()
            .map(JsonValue::Object),
        Some(json(r#"{"text":"notes"}"#))
    );
    assert!(matches!(
        inspected(&harness, parent).await,
        Some(TaskInspectionState::Completing)
    ));
    let idle = tokio::spawn(root.wait_for_idle(context()));
    assert!(!settled(&idle).await);
    script.open("child");
    assert_eq!(waiter.await.unwrap().unwrap().outcome, completed_parent());
    assert_eq!(
        harness
            .snapshot(&TASK_NOTES, parent, context())
            .await
            .unwrap(),
        None
    );
    root.wait_for_idle(context()).await.unwrap();
    assert!(script.slot("child").is_settled());
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn keeps_holding_for_ordinary_work_created_during_the_hold() {
    let script = Script::new();
    let Opened { harness, root, .. } = open_memory_nodes(&script).await;
    script.script(
        "parent",
        Behavior::default().run(|script, runtime, cx| async move {
            let owner = runtime.task_id().erase();
            runtime
                .commit(
                    move |tx, _| async move {
                        let conversation =
                            tx.create_conversation(owned_conversation(owner)).await?;
                        script.conversation_slot("parent").resolve(conversation.id);
                        create(
                            &tx,
                            script.node(),
                            "first",
                            in_conversation(conversation.id),
                        )
                        .await?;
                        Ok(Some(running(1)))
                    },
                    &cx,
                )
                .await
        }),
    );
    let parent = script.start(&root, "parent").await;
    until_status(&harness, parent, TaskStatus::Completing).await;
    let conversation = script.conversation_id("parent").await;
    let child = harness
        .conversation(conversation, context())
        .await
        .unwrap()
        .unwrap();
    script.start(&child, "second").await;
    script.open("first");
    let logged = &script;
    until(|| async move { logged.logged("run:second") }).await;
    assert_eq!(status(&harness, parent).await, TaskStatus::Completing);
    script.open("second");
    assert_eq!(
        outcome_of(&harness, parent).await,
        TaskOutcomeStatus::Completed
    );
    harness.close(context()).await.unwrap();
}

/// How the parent of [`aborts_the_work_below`] decides its held outcome.
#[derive(Clone, Copy)]
enum Held {
    Failure,
    SchedulerFault,
}

/// TS ``aborts the work below ${label}, then finishes with the held outcome``.
async fn aborts_the_work_below(held: Held) {
    let script = Script::new();
    let Opened { harness, root, .. } = open_memory_nodes(&script).await;
    script.script(
        "parent",
        Behavior::default()
            .run(|script, runtime, cx| async move {
                let owner = runtime.task_id().erase();
                runtime
                    .commit(
                        move |tx, _| async move {
                            let child = script.spawn(&tx, owner, "child").await?;
                            script.slot("child").resolve(child);
                            Ok(Some(running(1)))
                        },
                        &cx,
                    )
                    .await
            })
            .resume(move |_, runtime, cx, _| async move {
                match held {
                    Held::SchedulerFault => Err(SessionError::error("parent threw")),
                    Held::Failure => {
                        runtime
                            .commit(|_, _| async { Ok(Some(end(End::Failed, "parent"))) }, &cx)
                            .await
                    }
                }
            }),
    );
    let parent = script.start(&root, "parent").await;
    let child = script.id("child").await;
    assert_eq!(
        outcome_of(&harness, child).await,
        TaskOutcomeStatus::Aborted
    );
    assert_eq!(
        outcome_of(&harness, parent).await,
        match held {
            Held::SchedulerFault => TaskOutcomeStatus::Faulted,
            Held::Failure => TaskOutcomeStatus::Failed,
        }
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn aborts_the_work_below_a_held_failure_then_finishes_with_the_held_outcome() {
    aborts_the_work_below(Held::Failure).await;
}

#[tokio::test]
async fn aborts_the_work_below_a_held_scheduler_fault_then_finishes_with_the_held_outcome() {
    aborts_the_work_below(Held::SchedulerFault).await;
}

#[tokio::test]
async fn only_marks_a_completing_task_when_aborted_the_work_below_is_aborted_the_held_outcome_stays(
) {
    let script = Script::new();
    let Opened { harness, root, .. } = open_memory_nodes(&script).await;
    spawn_and_finish(&script, "parent", "child");
    let parent = script.start(&root, "parent").await;
    until_status(&harness, parent, TaskStatus::Completing).await;
    assert_eq!(
        harness.abort_task(parent, context()).await.unwrap(),
        TaskAbortResult::Marked
    );
    let child = script.id("parent").await;
    assert_eq!(
        outcome_of(&harness, child).await,
        TaskOutcomeStatus::Aborted
    );
    let settled_parent = harness.wait_for_task(parent, context()).await.unwrap();
    assert_eq!(settled_parent.outcome, completed_parent());
    assert!(settled_parent.abort_requested);
    assert!(!script.logged("abort:parent"));
    assert_eq!(
        harness.abort_task(parent, context()).await.unwrap(),
        TaskAbortResult::Terminal
    );
    harness.close(context()).await.unwrap();
}
