//! `describe("waiting")`.

use super::{
    assert_faulted, create, end, marked, open_memory_nodes, outcome_of, owned, parent_of, running,
    settle, state, status, until, until_status, wait_on, Behavior, End, Ending, Opened, Script,
};
use crate::harness::tests::support::context;
use crate::harness::tests::task_support::settled;
use crate::harness::TaskAbortResult;
use crate::types::{JoinPolicy, TaskId, TaskOutcome, TaskOutcomeStatus, TaskState, TaskStatus};

#[tokio::test]
async fn resumes_once_every_awaited_task_is_terminal_and_reads_their_outcomes_in_order_all_settled()
{
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
                            for name in ["ok", "fails", "throws", "aborted"] {
                                let id = script.spawn(&tx, owner, name).await?;
                                script.push_id("parent", id);
                            }
                            let orphan =
                                create(&tx, script.unregistered(), "orphan", owned(owner)).await?;
                            script.push_id("parent", orphan);
                            Ok(Some(wait_on(
                                script.ids("parent"),
                                JoinPolicy::AllSettled,
                                1,
                            )))
                        },
                        &cx,
                    )
                    .await
            })
            .resume(|script, runtime, cx, _| async move {
                let outcomes = runtime.outcomes(&script.ids("parent"), &cx).await?;
                script.set_outcomes("parent", outcomes.iter().map(TaskOutcome::status).collect());
                runtime
                    .commit(
                        |_, _| async { Ok(Some(end(End::Completed, "parent"))) },
                        &cx,
                    )
                    .await
            }),
    );
    let parent = script.start(&root, "parent").await;
    let found = &script;
    until(|| async move { found.ids("parent").len() == 5 }).await;
    until_status(&harness, parent, TaskStatus::Waiting).await;
    script.open("ok");
    script.open_with("fails", Ending::Failed);
    script.open_with("throws", Ending::Throw);
    let ids = script.ids("parent");
    harness.abort_task(ids[3], context()).await.unwrap();
    assert_eq!(
        harness.abort_task(ids[4], context()).await.unwrap(),
        TaskAbortResult::Marked
    );
    assert_eq!(
        outcome_of(&harness, parent).await,
        TaskOutcomeStatus::Completed
    );
    assert_eq!(
        script.outcomes("parent"),
        [
            TaskOutcomeStatus::Completed,
            TaskOutcomeStatus::Failed,
            TaskOutcomeStatus::Faulted,
            TaskOutcomeStatus::Aborted,
            TaskOutcomeStatus::Orphaned,
        ]
    );
    // allSettled never marks siblings.
    assert_eq!(script.log_starting("abort:"), ["abort:aborted"]);
    harness.close(context()).await.unwrap();
}

/// TS `fails fast when a child ends ${ending}: …` for `ending`.
async fn fails_fast(ending: Ending, ended: TaskOutcomeStatus) {
    let script = Script::new();
    let Opened { harness, root, .. } = open_memory_nodes(&script).await;
    parent_of(
        &script,
        "checkout",
        &["p1", "p2", "p3", "p4"],
        JoinPolicy::FailFast,
    );
    let parent = script.start(&root, "checkout").await;
    until_status(&harness, parent, TaskStatus::Waiting).await;
    script.open_with("p2", ending);
    assert_eq!(
        outcome_of(&harness, parent).await,
        TaskOutcomeStatus::Completed
    );
    assert_eq!(
        script.outcomes("checkout"),
        [
            TaskOutcomeStatus::Aborted,
            ended,
            TaskOutcomeStatus::Aborted,
            TaskOutcomeStatus::Aborted,
        ]
    );
    assert!(!marked(&harness, parent).await);
    let mut aborts = script.log_starting("abort:");
    aborts.sort();
    assert_eq!(aborts, ["abort:p1", "abort:p3", "abort:p4"]);
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn fails_fast_when_a_child_ends_failed_its_live_siblings_are_aborted_the_parent_is_not() {
    fails_fast(Ending::Failed, TaskOutcomeStatus::Failed).await;
}

#[tokio::test]
async fn fails_fast_when_a_child_ends_faulted_its_live_siblings_are_aborted_the_parent_is_not() {
    fails_fast(Ending::Throw, TaskOutcomeStatus::Faulted).await;
}

#[tokio::test]
async fn fails_fast_on_a_held_failure_before_the_failing_child_drains() {
    let script = Script::new();
    let Opened { harness, root, .. } = open_memory_nodes(&script).await;
    script.script(
        "p1",
        Behavior::default()
            .run(|script, runtime, cx| async move {
                let owner = runtime.task_id().erase();
                runtime
                    .commit(
                        move |tx, _| async move {
                            script.spawn(&tx, owner, "grandchild").await?;
                            Ok(Some(running(1)))
                        },
                        &cx,
                    )
                    .await
            })
            .resume(|_, runtime, cx, _| async move {
                runtime
                    .commit(|_, _| async { Ok(Some(end(End::Failed, "p1"))) }, &cx)
                    .await
            }),
    );
    script.script(
        "grandchild",
        Behavior::default().gated_abort("abort.grandchild"),
    );
    script.script(
        "parent",
        Behavior::default().run(|script, runtime, cx| async move {
            let owner = runtime.task_id().erase();
            runtime
                .commit(
                    move |tx, _| async move {
                        for name in ["p1", "p2"] {
                            let id = script.spawn(&tx, owner, name).await?;
                            script.push_id("parent", id);
                        }
                        let outside = script.spawn(&tx, owner, "outside").await?;
                        script.slot("outside").resolve(outside);
                        Ok(Some(wait_on(script.ids("parent"), JoinPolicy::FailFast, 1)))
                    },
                    &cx,
                )
                .await
        }),
    );
    let parent = script.start(&root, "parent").await;
    let found = &script;
    until(|| async move { found.ids("parent").len() == 2 }).await;
    let ids = script.ids("parent");
    // p1 holds `failed` while its grandchild's abort handler runs; p2 is already aborted.
    assert_eq!(
        outcome_of(&harness, ids[1]).await,
        TaskOutcomeStatus::Aborted
    );
    match state(&harness, ids[0]).await {
        TaskState::Completing { outcome } => {
            assert_eq!(outcome.status(), TaskOutcomeStatus::Failed);
        }
        other => panic!("expected a completing state, got {other:?}"),
    }
    assert_eq!(status(&harness, parent).await, TaskStatus::Waiting);
    script.open("abort.grandchild");
    until(|| async move { found.logged("resume:parent") }).await;
    // Only the other tasks in `on` are marked: not the failed one, not the parent, not a child outside `on`.
    let outside = script.id("outside").await;
    assert_eq!(
        outcome_of(&harness, ids[0]).await,
        TaskOutcomeStatus::Failed
    );
    assert_eq!(
        [
            marked(&harness, ids[0]).await,
            marked(&harness, ids[1]).await,
            marked(&harness, outside).await,
        ],
        [false, true, false]
    );
    assert!(!marked(&harness, parent).await);
    assert_eq!(status(&harness, outside).await, TaskStatus::Running);
    // Finished, the parent holds for the child outside `on`.
    until_status(&harness, parent, TaskStatus::Completing).await;
    script.open("outside");
    assert_eq!(
        outcome_of(&harness, parent).await,
        TaskOutcomeStatus::Completed
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn waits_with_all_settled_on_tasks_it_does_not_own_including_already_terminal_ones() {
    let script = Script::new();
    let Opened { harness, root, .. } = open_memory_nodes(&script).await;
    let done = script.start(&root, "done").await;
    script.open("done");
    harness.wait_for_task(done, context()).await.unwrap();
    let live = script.start(&root, "live").await;
    script.script(
        "parent",
        Behavior::default()
            .run(move |_, runtime, cx| async move {
                runtime
                    .commit(
                        move |_, _| async move {
                            Ok(Some(wait_on(vec![done, live], JoinPolicy::AllSettled, 1)))
                        },
                        &cx,
                    )
                    .await
            })
            .resume(move |script, runtime, cx, _| async move {
                let outcomes = runtime.outcomes(&[done, live], &cx).await?;
                script.set_outcomes("parent", outcomes.iter().map(TaskOutcome::status).collect());
                runtime
                    .commit(
                        |_, _| async { Ok(Some(end(End::Completed, "parent"))) },
                        &cx,
                    )
                    .await
            }),
    );
    let parent = script.start(&root, "parent").await;
    until_status(&harness, parent, TaskStatus::Waiting).await;
    // A task it does not own is not its work: the parent may finish while it lives, but here it waits for it.
    script.open_with("live", Ending::Failed);
    assert_eq!(
        outcome_of(&harness, parent).await,
        TaskOutcomeStatus::Completed
    );
    assert_eq!(
        script.outcomes("parent"),
        [TaskOutcomeStatus::Completed, TaskOutcomeStatus::Failed]
    );
    harness.close(context()).await.unwrap();
}

/// Which tasks a case of the rejected waits waits on.
#[derive(Clone, Copy)]
enum On {
    Itself,
    Missing,
    Foreign(TaskId),
}

#[tokio::test]
async fn rejects_waits_on_itself_its_owner_a_missing_task_and_fail_fast_on_a_task_it_does_not_own()
{
    let script = Script::new();
    let Opened { harness, root, .. } = open_memory_nodes(&script).await;
    let other = script.start(&root, "other").await;
    let cases = [
        (
            "self",
            On::Itself,
            JoinPolicy::AllSettled,
            "cannot wait on itself or its owner",
        ),
        (
            "missing",
            On::Missing,
            JoinPolicy::AllSettled,
            "does not exist",
        ),
        (
            "foreign",
            On::Foreign(other),
            JoinPolicy::FailFast,
            "only on tasks it owns",
        ),
    ];
    for (name, on, policy, message) in cases {
        script.script(
            name,
            Behavior::default().run(move |_, runtime, cx| async move {
                let on = match on {
                    On::Itself => vec![runtime.task_id().erase()],
                    On::Missing => vec![TaskId::from_number(999_999)],
                    On::Foreign(id) => vec![id],
                };
                runtime
                    .commit(
                        move |_, _| async move { Ok(Some(wait_on(on, policy, 1))) },
                        &cx,
                    )
                    .await
            }),
        );
        let id = script.start(&root, name).await;
        assert_faulted(&settle(&harness, id).await, message);
    }
    // A child waiting on its owner could never resume.
    script.script(
        "child",
        Behavior::default().run(|script, runtime, cx| async move {
            let parent = script.id("parent").await;
            runtime
                .commit(
                    move |_, _| async move {
                        Ok(Some(wait_on(vec![parent], JoinPolicy::AllSettled, 1)))
                    },
                    &cx,
                )
                .await
        }),
    );
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
    script.slot("parent").resolve(parent);
    assert_eq!(
        outcome_of(&harness, parent).await,
        TaskOutcomeStatus::Completed
    );
    let child = script.id("child").await;
    assert_faulted(
        &settle(&harness, child).await,
        "cannot wait on itself or its owner",
    );
    script.open("other");
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn resumes_at_the_next_pass_when_it_waits_on_nothing() {
    let script = Script::new();
    let Opened { harness, root, .. } = open_memory_nodes(&script).await;
    script.script(
        "parent",
        Behavior::default().run(|_, runtime, cx| async move {
            runtime
                .commit(
                    |_, _| async { Ok(Some(wait_on(Vec::new(), JoinPolicy::FailFast, 1))) },
                    &cx,
                )
                .await
        }),
    );
    let parent = script.start(&root, "parent").await;
    assert_eq!(
        outcome_of(&harness, parent).await,
        TaskOutcomeStatus::Completed
    );
    assert_eq!(script.log(), ["run:parent", "resume:parent"]);
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn keeps_running_phases_after_spawning_and_waits_on_subsets_in_sequence() {
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
                            for name in ["a", "b", "c"] {
                                let id = script.spawn(&tx, owner, name).await?;
                                script.push_id("parent", id);
                            }
                            Ok(Some(running(0)))
                        },
                        &cx,
                    )
                    .await
            })
            .resume(|script, runtime, cx, round| async move {
                script.push_log(format!("round:{round}"));
                let ids = script.ids("parent");
                let next = match round {
                    0 => wait_on(vec![ids[0]], JoinPolicy::AllSettled, 1),
                    1 => wait_on(vec![ids[1], ids[2]], JoinPolicy::FailFast, 2),
                    _ => end(End::Completed, "parent"),
                };
                runtime
                    .commit(move |_, _| async move { Ok(Some(next)) }, &cx)
                    .await
            }),
    );
    let parent = script.start(&root, "parent").await;
    let logged = &script;
    until(|| async move { logged.logged("round:0") }).await;
    until_status(&harness, parent, TaskStatus::Waiting).await;
    script.open("b");
    let ids = script.ids("parent");
    let b = tokio::spawn(harness.wait_for_task(ids[1], context()));
    assert!(settled(&b).await);
    assert_eq!(status(&harness, parent).await, TaskStatus::Waiting);
    script.open("a");
    until(|| async move { logged.logged("round:1") }).await;
    script.open("c");
    assert_eq!(
        outcome_of(&harness, parent).await,
        TaskOutcomeStatus::Completed
    );
    assert_eq!(
        script.log_starting("round:"),
        ["round:0", "round:1", "round:2"]
    );
    harness.close(context()).await.unwrap();
}
