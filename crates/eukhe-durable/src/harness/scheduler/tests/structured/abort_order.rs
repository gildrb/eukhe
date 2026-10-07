//! `describe("abort order")`.

use std::sync::Arc;

use super::{
    aborted_next, assert_faulted, create, in_conversation, inspected, open_memory_nodes,
    outcome_of, owned, owned_conversation, record, running, settle, status, until, until_status,
    wait_on, Behavior, Opened, Script, OWN_CONVERSATION,
};
use crate::harness::tests::support::context;
use crate::harness::tests::task_support::aborted;
use crate::harness::types::TaskInspectionState;
use crate::harness::TaskAbortResult;
use crate::types::{JoinPolicy, TaskOutcome, TaskOutcomeStatus, TaskStatus};

/// TS status strings of a task state.
fn status_name(status: TaskStatus) -> &'static str {
    match status {
        TaskStatus::Pending => "pending",
        TaskStatus::Running => "running",
        TaskStatus::Waiting => "waiting",
        TaskStatus::Completing => "completing",
        TaskStatus::Terminal => "terminal",
    }
}

/// Script `name` to spawn `child` and wait on it; its abort handler records
/// the child's status first. The child's ID goes to the slot `name`.
fn chain(script: &Script, name: &'static str, child: &'static str) {
    script.script(
        name,
        Behavior::default()
            .run(move |script, runtime, cx| async move {
                let owner = runtime.task_id().erase();
                runtime
                    .commit(
                        move |tx, _| async move {
                            let id = script.spawn(&tx, owner, child).await?;
                            script.slot(name).resolve(id);
                            Ok(Some(wait_on(vec![id], JoinPolicy::AllSettled, 1)))
                        },
                        &cx,
                    )
                    .await
            })
            .abort(move |script, runtime, cx| async move {
                let id = script.id(name).await;
                let seen = record(&script.harness(), id).await.state.status();
                script.push_log(format!("{name} saw {}", status_name(seen)));
                runtime
                    .commit(|_, _| async { Ok(Some(aborted_next())) }, &cx)
                    .await
            }),
    );
}

#[tokio::test]
async fn runs_abort_handlers_bottom_up_across_three_levels_each_after_the_level_below_is_terminal()
{
    let script = Script::new();
    chain(&script, "a", "b");
    chain(&script, "b", "c");
    let Opened { harness, root, .. } = open_memory_nodes(&script).await;
    let a = script.start(&root, "a").await;
    let logged = &script;
    until(|| async move { logged.logged("run:c") }).await;
    let c = script.id("b").await;
    until_status(&harness, c, TaskStatus::Running).await;
    assert_eq!(
        harness.abort_task(a, context()).await.unwrap(),
        TaskAbortResult::Marked
    );
    assert_eq!(outcome_of(&harness, a).await, TaskOutcomeStatus::Aborted);
    let order: Vec<String> = script
        .log()
        .into_iter()
        .filter(|line| line.starts_with("abort:") || line.contains(" saw "))
        .collect();
    assert_eq!(
        order,
        [
            "abort:c",
            "abort:b",
            "b saw terminal",
            "abort:a",
            "a saw terminal"
        ]
    );
    assert!(script.slot("a").is_settled());
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn does_not_wait_for_a_task_it_waits_on_but_does_not_own() {
    let script = Script::new();
    let Opened { harness, root, .. } = open_memory_nodes(&script).await;
    let other = script.start(&root, "other").await;
    script.script(
        "parent",
        Behavior::default().run(move |_, runtime, cx| async move {
            runtime
                .commit(
                    move |_, _| async move {
                        Ok(Some(wait_on(vec![other], JoinPolicy::AllSettled, 1)))
                    },
                    &cx,
                )
                .await
        }),
    );
    let parent = script.start(&root, "parent").await;
    until_status(&harness, parent, TaskStatus::Waiting).await;
    harness.abort_task(parent, context()).await.unwrap();
    assert_eq!(
        outcome_of(&harness, parent).await,
        TaskOutcomeStatus::Aborted
    );
    assert_eq!(status(&harness, other).await, TaskStatus::Running);
    script.open("other");
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn reports_an_abort_marked_task_as_waiting_for_its_live_owned_work() {
    let script = Script::new();
    let Opened { harness, root, .. } = open_memory_nodes(&script).await;
    script.script("child", Behavior::default().gated_abort("abort.child"));
    script.script(
        "parent",
        Behavior::default().run(|script, runtime, cx| async move {
            let owner = runtime.task_id().erase();
            runtime
                .commit(
                    move |tx, _| async move {
                        let child = script.spawn(&tx, owner, "child").await?;
                        script.slot("child").resolve(child);
                        Ok(Some(wait_on(vec![child], JoinPolicy::AllSettled, 1)))
                    },
                    &cx,
                )
                .await
        }),
    );
    let parent = script.start(&root, "parent").await;
    until_status(&harness, parent, TaskStatus::Waiting).await;
    harness.abort_task(parent, context()).await.unwrap();
    let logged = &script;
    until(|| async move { logged.logged("abort:child") }).await;
    let child = script.id("child").await;
    match inspected(&harness, parent).await {
        Some(TaskInspectionState::Waiting { on }) => assert_eq!(on, [child]),
        other => panic!("expected a waiting inspection, got {other:?}"),
    }
    script.open("abort.child");
    assert_eq!(
        outcome_of(&harness, parent).await,
        TaskOutcomeStatus::Aborted
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn faults_an_abort_handler_that_tries_to_wait() {
    let script = Script::new();
    let Opened { harness, root, .. } = open_memory_nodes(&script).await;
    script.script(
        "parent",
        Behavior::default().abort(|_, runtime, cx| async move {
            runtime
                .commit(
                    |_, _| async { Ok(Some(wait_on(Vec::new(), JoinPolicy::AllSettled, 1))) },
                    &cx,
                )
                .await
        }),
    );
    let parent = script.start(&root, "parent").await;
    let logged = &script;
    until(|| async move { logged.logged("run:parent") }).await;
    harness.abort_task(parent, context()).await.unwrap();
    assert_faulted(&settle(&harness, parent).await, "cannot wait");
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn orphans_a_blocked_task_only_after_its_owned_work_drained() {
    let script = Script::new();
    let Opened { harness, root, .. } = open_memory_nodes(&script).await;
    let spawner = Arc::clone(&script);
    let (owner, child) = root
        .commit(
            move |tx| async move {
                let owner = create(&tx, spawner.unregistered(), "owner", OWN_CONVERSATION).await?;
                let child = create(&tx, spawner.node(), "child", owned(owner)).await?;
                Ok((owner, child))
            },
            context(),
        )
        .await
        .unwrap();
    let logged = &script;
    until(|| async move { logged.logged("run:child") }).await;
    assert_eq!(
        harness.abort_task(owner, context()).await.unwrap(),
        TaskAbortResult::Marked
    );
    assert_eq!(
        outcome_of(&harness, child).await,
        TaskOutcomeStatus::Aborted
    );
    assert_eq!(
        settle(&harness, owner).await,
        TaskOutcome::Orphaned {
            reason: "missing_task".to_owned()
        }
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn cascades_through_task_and_conversation_edges_bottom_up() {
    let script = Script::new();
    let Opened { harness, root, .. } = open_memory_nodes(&script).await;
    script.script(
        "a",
        Behavior::default().run(|script, runtime, cx| async move {
            let owner = runtime.task_id().erase();
            runtime
                .commit(
                    move |tx, _| async move {
                        let b = script.spawn(&tx, owner, "b").await?;
                        Ok(Some(wait_on(vec![b], JoinPolicy::AllSettled, 1)))
                    },
                    &cx,
                )
                .await
        }),
    );
    script.script(
        "b",
        Behavior::default()
            .run(|script, runtime, cx| async move {
                let owner = runtime.task_id().erase();
                runtime
                    .commit(
                        move |tx, _| async move {
                            let conversation =
                                tx.create_conversation(owned_conversation(owner)).await?;
                            let x =
                                create(&tx, script.node(), "x", in_conversation(conversation.id))
                                    .await?;
                            script.slot("x").resolve(x);
                            Ok(Some(running(1)))
                        },
                        &cx,
                    )
                    .await
            })
            .resume(|_, runtime, _, _| async move { Err(aborted(&runtime.signal()).await) }),
    );
    let a = script.start(&root, "a").await;
    let logged = &script;
    until(|| async move { logged.logged("run:x") }).await;
    harness.abort_task(a, context()).await.unwrap();
    assert_eq!(outcome_of(&harness, a).await, TaskOutcomeStatus::Aborted);
    let x = script.id("x").await;
    assert_eq!(outcome_of(&harness, x).await, TaskOutcomeStatus::Aborted);
    assert_eq!(
        script.log_starting("abort:"),
        ["abort:x", "abort:b", "abort:a"]
    );
    harness.close(context()).await.unwrap();
}
