//! `describe("waiting")`.

use eukhe_chord::context::Context;
use eukhe_chord::json::JsonValue;

use super::{
    create, end, marked, open_memory_nodes, outcome_of, owned, owned_conversation, parent_of,
    running, settle, state, status, until, until_status, wait_on, Behavior, End, Ending,
    NodeRuntime, Opened, Script, BACKGROUND,
};
use crate::harness::tests::support::context;
use crate::harness::tests::task_support::{deferred, settled, Deferred};
use crate::harness::TaskAbortResult;
use crate::session::SessionResult;
use crate::types::{
    JoinPolicy, TaskId, TaskOptions, TaskOutcome, TaskOutcomeError, TaskOutcomeStatus, TaskState,
    TaskStatus,
};

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

/// `{ status: "faulted", error: { message } }`.
fn fault(message: String) -> TaskOutcome {
    TaskOutcome::Faulted {
        error: TaskOutcomeError {
            message,
            detail: None,
        },
    }
}

/// `{ status: "completed", result: name }` of a default `test.node` end.
fn completed(name: &str) -> TaskOutcome {
    TaskOutcome::Completed {
        result: JsonValue::from(name),
    }
}

#[tokio::test]
async fn rejects_waits_on_itself_its_owner_a_missing_task_and_fail_fast_on_a_task_it_does_not_own()
{
    let script = Script::new();
    let Opened { harness, root, .. } = open_memory_nodes(&script).await;
    let other = script.start(&root, "other").await;
    let cases = [
        ("self", On::Itself, JoinPolicy::AllSettled),
        ("missing", On::Missing, JoinPolicy::AllSettled),
        ("foreign", On::Foreign(other), JoinPolicy::FailFast),
    ];
    for (name, on, policy) in cases {
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
        let message = match on {
            On::Itself => format!("Task {id} cannot wait on {id}: {id} -> {id} is a wait cycle"),
            On::Missing => "Task 999999 does not exist".to_owned(),
            On::Foreign(other) => {
                format!("Task {id} can wait failFast only on tasks it owns; {other} is not one")
            }
        };
        assert_eq!(settle(&harness, id).await, fault(message));
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
    assert_eq!(
        settle(&harness, child).await,
        fault(format!(
            "Task {child} cannot wait on {parent}: {child} -> {parent} -> {child} is a wait cycle"
        ))
    );
    script.open("other");
    harness.close(context()).await.unwrap();
}

/// What a behavior's wait commit returned: `Ok`, or the rejection's message.
type Committed = Deferred<Result<(), String>>;

/// Commit a wait on `on` with `allSettled`, record what the commit returned
/// in `committed`, and return it.
async fn commit_wait(
    runtime: &NodeRuntime,
    on: Vec<TaskId>,
    committed: &Committed,
    cx: &Context,
) -> SessionResult<()> {
    let result = runtime
        .commit(
            move |_, _| async move { Ok(Some(wait_on(on, JoinPolicy::AllSettled, 1))) },
            cx,
        )
        .await;
    committed.resolve(result.as_ref().map(|&()| ()).map_err(ToString::to_string));
    result
}

/// A behavior whose run, once the gate `name` opens, waits for the task in
/// slot `target`, then commits a wait on it through [`commit_wait`].
fn waits_on(name: &'static str, target: &'static str, committed: &Committed) -> Behavior {
    let committed = committed.clone();
    Behavior::default().run(move |script, runtime, cx| {
        let committed = committed.clone();
        async move {
            script.gate(name).wait().await;
            let on = script.slot(target).wait().await;
            commit_wait(&runtime, vec![on], &committed, &cx).await
        }
    })
}

#[tokio::test]
async fn rejects_a_wait_on_a_task_that_waits_on_the_waiter() {
    let script = Script::new();
    let Opened { harness, root, .. } = open_memory_nodes(&script).await;
    let (a_waits, b_waits): (Committed, Committed) = (deferred(), deferred());
    script.script("a", waits_on("a", "b", &a_waits));
    script.script("b", waits_on("b", "a", &b_waits));
    script.open("a");
    let a = script.start(&root, "a").await;
    script.slot("a").resolve(a);
    let b = script.start(&root, "b").await;
    script.slot("b").resolve(b);
    assert_eq!(a_waits.wait().await, Ok(()));
    script.open("b");
    let message = format!("Task {b} cannot wait on {a}: {b} -> {a} -> {b} is a wait cycle");
    assert_eq!(b_waits.wait().await, Err(message.clone()));
    assert_eq!(settle(&harness, b).await, fault(message));
    // `a` resumes once `b` settled.
    assert_eq!(settle(&harness, a).await, completed("a"));
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn rejects_a_wait_that_closes_a_cycle_through_an_owner_holding_its_outcome() {
    let script = Script::new();
    let Opened { harness, root, .. } = open_memory_nodes(&script).await;
    let (child_waits, owner_ends, x_waits): (Committed, Committed, Committed) =
        (deferred(), deferred(), deferred());
    // `owner` spawns a child that waits on `x`, then ends and holds
    // `completing` while the child lives.
    let ended = owner_ends.clone();
    script.script(
        "owner",
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
            .resume(move |_, runtime, cx, _| {
                let ended = ended.clone();
                async move {
                    let result = runtime
                        .commit(|_, _| async { Ok(Some(end(End::Completed, "owner"))) }, &cx)
                        .await;
                    ended.resolve(result.as_ref().map(|&()| ()).map_err(ToString::to_string));
                    result
                }
            }),
    );
    script.script("child", waits_on("child", "x", &child_waits));
    script.script("x", waits_on("x", "holder", &x_waits));
    script.open("child");
    let x = script.start(&root, "x").await;
    script.slot("x").resolve(x);
    let owner = script.start(&root, "owner").await;
    script.slot("holder").resolve(owner);
    assert_eq!(child_waits.wait().await, Ok(()));
    assert_eq!(owner_ends.wait().await, Ok(()));
    let child = script.slot("child").wait().await;
    assert_eq!(
        state(&harness, owner).await,
        TaskState::Completing {
            outcome: completed("owner")
        }
    );
    // `x` waiting on the owner would wait on itself: x -> owner -> child -> x.
    script.open("x");
    let message = format!(
        "Task {x} cannot wait on {owner}: {x} -> {owner} -> {child} -> {x} is a wait cycle"
    );
    assert_eq!(x_waits.wait().await, Err(message.clone()));
    assert_eq!(settle(&harness, x).await, fault(message));
    // The child resumes once `x` settled, which frees its owner.
    assert_eq!(settle(&harness, child).await, completed("child"));
    assert_eq!(settle(&harness, owner).await, completed("owner"));
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn lets_a_background_task_wait_on_the_owner_of_its_conversation() {
    let script = Script::new();
    let Opened { harness, root, .. } = open_memory_nodes(&script).await;
    let watcher_waits: Committed = deferred();
    // `owner` starts a background `watcher` in a conversation it owns, and
    // ends once its gate opens; the watcher does not hold it.
    script.script(
        "owner",
        Behavior::default()
            .run(|script, runtime, cx| async move {
                let owner = runtime.task_id().erase();
                runtime
                    .commit(
                        move |tx, _| async move {
                            let conversation =
                                tx.create_conversation(owned_conversation(owner)).await?.id;
                            let options = TaskOptions {
                                conversation_id: Some(conversation),
                                ..BACKGROUND
                            };
                            let watcher = create(&tx, script.node(), "watcher", options).await?;
                            script.slot("watcher").resolve(watcher);
                            Ok(Some(running(1)))
                        },
                        &cx,
                    )
                    .await
            })
            .resume(|script, runtime, cx, _| async move {
                script.gate("owner").wait().await;
                runtime
                    .commit(|_, _| async { Ok(Some(end(End::Completed, "owner"))) }, &cx)
                    .await
            }),
    );
    script.script("watcher", waits_on("watcher", "owner", &watcher_waits));
    script.open("watcher");
    let owner = script.start(&root, "owner").await;
    script.slot("owner").resolve(owner);
    assert_eq!(watcher_waits.wait().await, Ok(()));
    let watcher = script.slot("watcher").wait().await;
    script.open("owner");
    assert_eq!(settle(&harness, owner).await, completed("owner"));
    assert_eq!(settle(&harness, watcher).await, completed("watcher"));
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
