//! TS `describe("ownership")`.

use super::*;

#[tokio::test]
async fn keeps_a_conversation_busy_while_its_owned_foreground_subtree_has_live_work_holding_the_completed_owner(
) {
    let world = World::new();
    let Opened { harness, root, .. } = open_harness(&world, memory()).await;
    let tree = owned_child(&world, &root, "owner", TreeOptions::default()).await;
    world.open("owner", Ending::Completed);
    until_status(&harness, tree.owner, TaskStatus::Completing).await;
    let idle = tokio::spawn(root.wait_for_idle(context()));
    assert!(!settled(&idle).await);
    assert!(!settled(&tokio::spawn(harness.wait_for_idle(context()))).await);
    world.open("owner.inner", Ending::Completed);
    idle.await.unwrap().unwrap();
    harness.wait_for_idle(context()).await.unwrap();
    assert_eq!(
        status(&harness, tree.owner)
            .await
            .outcome()
            .map(TaskOutcome::status),
        Some(TaskOutcomeStatus::Completed)
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn stops_idle_traversal_at_a_background_owner() {
    let world = World::new();
    let Opened { harness, root, .. } = open_harness(&world, memory()).await;
    let tree = owned_child(
        &world,
        &root,
        "background",
        TreeOptions {
            background: true,
            ..TreeOptions::default()
        },
    )
    .await;
    root.wait_for_idle(context()).await.unwrap();
    harness.wait_for_idle(context()).await.unwrap();
    // The background child is its own scope.
    let child = harness
        .conversation(tree.child, context())
        .await
        .unwrap()
        .unwrap();
    assert!(!settled(&tokio::spawn(child.wait_for_idle(context()))).await);
    child
        .abort(ConversationAbortOptions::default(), context())
        .await
        .unwrap();
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn cascades_an_abort_mark_to_the_owned_foreground_subtree_and_withdraws_its_queued_inputs() {
    let world = World::new();
    let Opened { harness, root, .. } = open_harness(&world, memory()).await;
    let tree = owned_child(&world, &root, "owner", TreeOptions::default()).await;
    let nested = harness
        .conversation(tree.child, context())
        .await
        .unwrap()
        .unwrap();
    let deeper = owned_child(&world, &nested, "deeper", TreeOptions::default()).await;
    let shielded = owned_child(
        &world,
        &nested,
        "shielded",
        TreeOptions {
            background: true,
            ..TreeOptions::default()
        },
    )
    .await;
    // Busy conversations queue submissions; the inner task stands in for the child's run.
    busy(&nested, tree.inner).await;
    let queued = nested
        .submit(InputSubmissionDraft::new("later"), context())
        .await
        .unwrap()
        .id();
    assert_eq!(
        harness.abort_task(tree.owner, context()).await.unwrap(),
        TaskAbortResult::Marked
    );
    for id in [tree.owner, tree.inner, deeper.owner, deeper.inner] {
        assert_eq!(outcome_of(&harness, id).await, TaskOutcomeStatus::Aborted);
    }
    // A nested background owner is a boundary.
    assert_ne!(
        status(&harness, shielded.owner).await.status(),
        TaskStatus::Terminal
    );
    assert_ne!(
        status(&harness, shielded.inner).await.status(),
        TaskStatus::Terminal
    );
    let record = submission_record(&harness, queued).await;
    assert_eq!(record.state.status(), SubmissionStatus::Unanswered);
    assert_eq!(record.state.reason(), Some("aborted"));
    harness.abort_task(shielded.owner, context()).await.unwrap();
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn cascades_a_failed_owner_but_not_a_completed_one() {
    let world = World::new();
    let Opened { harness, root, .. } = open_harness(&world, memory()).await;
    let failed = owned_child(&world, &root, "failed", TreeOptions::default()).await;
    let completed_tree = owned_child(&world, &root, "done", TreeOptions::default()).await;
    world.open("failed", Ending::Failed);
    world.open("done", Ending::Completed);
    assert_eq!(
        outcome_of(&harness, failed.inner).await,
        TaskOutcomeStatus::Aborted
    );
    assert_eq!(
        outcome_of(&harness, failed.owner).await,
        TaskOutcomeStatus::Failed
    );
    until_status(&harness, completed_tree.owner, TaskStatus::Completing).await;
    assert_ne!(
        status(&harness, completed_tree.inner).await.status(),
        TaskStatus::Terminal
    );
    world.open("done.inner", Ending::Completed);
    assert_eq!(
        outcome_of(&harness, completed_tree.owner).await,
        TaskOutcomeStatus::Completed
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn aborts_a_background_task_directly_with_its_ordinary_subtree() {
    let world = World::new();
    let Opened { harness, root, .. } = open_harness(&world, memory()).await;
    let tree = owned_child(
        &world,
        &root,
        "background",
        TreeOptions {
            background: true,
            ..TreeOptions::default()
        },
    )
    .await;
    harness.abort_task(tree.owner, context()).await.unwrap();
    assert_eq!(
        outcome_of(&harness, tree.inner).await,
        TaskOutcomeStatus::Aborted
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn aborts_a_conversation_queued_inputs_withdrawn_writes_kept_foreground_work_aborted_background_kept(
) {
    let world = World::new();
    let Opened { harness, root, .. } = open_harness(&world, memory()).await;
    let foreground = owned_child(&world, &root, "foreground", TreeOptions::default()).await;
    let background = owned_child(
        &world,
        &root,
        "background",
        TreeOptions {
            background: true,
            ..TreeOptions::default()
        },
    )
    .await;
    busy(&root, foreground.owner).await;
    let input = root
        .submit(InputSubmissionDraft::new("later"), context())
        .await
        .unwrap()
        .id();
    let write = root
        .submit(
            WriteSubmissionDraft {
                request_id: None,
                entry: EntryDraft::new("note"),
            },
            context(),
        )
        .await
        .unwrap()
        .id();
    root.abort(ConversationAbortOptions::default(), context())
        .await
        .unwrap();
    for id in [foreground.owner, foreground.inner] {
        assert_eq!(status(&harness, id).await.status(), TaskStatus::Terminal);
    }
    assert_ne!(
        status(&harness, background.owner).await.status(),
        TaskStatus::Terminal
    );
    assert_ne!(
        status(&harness, background.inner).await.status(),
        TaskStatus::Terminal
    );
    assert_eq!(
        submission_record(&harness, input).await.state.reason(),
        Some("aborted")
    );
    assert_eq!(
        submission_record(&harness, write).await.state.status(),
        SubmissionStatus::Queued
    );
    harness
        .abort_task(background.owner, context())
        .await
        .unwrap();
    harness.close(context()).await.unwrap();
}

/// TS `create(name)`: a Hold task in `child`, owned by the conversation.
async fn create_in(world: &World, child: &Conversation, name: &str) -> TaskId {
    let (hold, input) = (world.hold.clone(), HoldInput::named(name));
    child
        .commit(
            move |tx| async move { create_task_in(&tx, &hold, &input, options(None, None)).await },
            context(),
        )
        .await
        .expect("create the task")
}

#[tokio::test]
async fn aborts_work_created_below_a_held_failed_owner_but_not_below_a_terminal_one() {
    let world = World::new();
    let Opened { harness, root, .. } = open_harness(&world, memory()).await;
    let tree = owned_child(
        &world,
        &root,
        "owner",
        TreeOptions {
            slow_inner: true,
            ..TreeOptions::default()
        },
    )
    .await;
    world.open("owner", Ending::Failed);
    until_abort_requested(&harness, tree.inner).await;
    assert_eq!(
        status(&harness, tree.owner).await.status(),
        TaskStatus::Completing
    );
    let child = harness
        .conversation(tree.child, context())
        .await
        .unwrap()
        .unwrap();
    let during = create_in(&world, &child, "during").await;
    assert_eq!(
        outcome_of(&harness, during).await,
        TaskOutcomeStatus::Aborted
    );
    world.open("abort.owner.inner", Ending::Completed);
    assert_eq!(
        outcome_of(&harness, tree.owner).await,
        TaskOutcomeStatus::Failed
    );
    // A terminal owner never cascades: interrogating its conversation runs normally.
    let after = create_in(&world, &child, "after").await;
    world.open("after", Ending::Completed);
    assert_eq!(
        outcome_of(&harness, after).await,
        TaskOutcomeStatus::Completed
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn withdraws_queued_inputs_below_the_aborted_task_but_keeps_its_own_conversations_queue_and_queued_writes(
) {
    let world = World::new();
    let Opened { harness, root, .. } = open_harness(&world, memory()).await;
    let tree = owned_child(&world, &root, "owner", TreeOptions::default()).await;
    let child = harness
        .conversation(tree.child, context())
        .await
        .unwrap()
        .unwrap();
    busy(&root, tree.owner).await;
    busy(&child, tree.inner).await;
    let own = root
        .submit(InputSubmissionDraft::new("own"), context())
        .await
        .unwrap()
        .id();
    let below = child
        .submit(InputSubmissionDraft::new("below"), context())
        .await
        .unwrap()
        .id();
    let write = child
        .submit(
            WriteSubmissionDraft {
                request_id: None,
                entry: EntryDraft::new("note"),
            },
            context(),
        )
        .await
        .unwrap()
        .id();
    harness.abort_task(tree.owner, context()).await.unwrap();
    harness.wait_for_task(tree.inner, context()).await.unwrap();
    assert_eq!(
        submission_record(&harness, own).await.state.status(),
        SubmissionStatus::Queued
    );
    assert_eq!(
        submission_record(&harness, below).await.state.status(),
        SubmissionStatus::Unanswered
    );
    assert_eq!(
        submission_record(&harness, write).await.state.status(),
        SubmissionStatus::Queued
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn keeps_a_nested_background_owners_subtree_when_its_cancelled_background_owner_is_aborted() {
    let world = World::new();
    let Opened { harness, root, .. } = open_harness(&world, memory()).await;
    let background = TreeOptions {
        background: true,
        ..TreeOptions::default()
    };
    let outer = owned_child(&world, &root, "outer", background).await;
    let outer_child = harness
        .conversation(outer.child, context())
        .await
        .unwrap()
        .unwrap();
    let inner = owned_child(&world, &outer_child, "inner", background).await;
    harness.abort_task(outer.owner, context()).await.unwrap();
    assert_eq!(
        outcome_of(&harness, outer.inner).await,
        TaskOutcomeStatus::Aborted
    );
    assert_ne!(
        status(&harness, inner.owner).await.status(),
        TaskStatus::Terminal
    );
    assert_ne!(
        status(&harness, inner.inner).await.status(),
        TaskStatus::Terminal
    );
    harness.abort_task(inner.owner, context()).await.unwrap();
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn decides_idle_after_reopen_from_owner_edges_it_has_to_load_first() {
    let world = World::new();
    let (_directory, path) = sqlite_path("pi-durable-ownership-");
    let opened = open_harness(&world, sqlite(&path).await).await;
    let foreground = owned_child(&world, &opened.root, "fg", TreeOptions::default()).await;
    let foreground_child = opened
        .harness
        .conversation(foreground.child, context())
        .await
        .unwrap()
        .unwrap();
    let deeper = owned_child(&world, &foreground_child, "fg2", TreeOptions::default()).await;
    let background = owned_child(
        &world,
        &opened.root,
        "bg",
        TreeOptions {
            background: true,
            ..TreeOptions::default()
        },
    )
    .await;
    world.open("fg", Ending::Completed);
    world.open("fg2", Ending::Completed);
    // Both owners hold their outcomes while the work below them runs.
    until_status(&opened.harness, foreground.owner, TaskStatus::Completing).await;
    until_status(&opened.harness, deeper.owner, TaskStatus::Completing).await;
    opened.harness.close(context()).await.unwrap();

    let opened = open_harness(&world, sqlite(&path).await).await;
    // Two levels below completed foreground owners, the inner tasks keep the root busy.
    assert!(!settled(&tokio::spawn(opened.root.wait_for_idle(context()))).await);
    assert!(!settled(&tokio::spawn(opened.harness.wait_for_idle(context()))).await);
    world.open("fg.inner", Ending::Completed);
    world.open("fg2.inner", Ending::Completed);
    // The background subtree does not count.
    opened.root.wait_for_idle(context()).await.unwrap();
    opened.harness.wait_for_idle(context()).await.unwrap();
    assert_eq!(
        status(&opened.harness, foreground.owner).await.status(),
        TaskStatus::Terminal
    );
    assert_ne!(
        status(&opened.harness, background.inner).await.status(),
        TaskStatus::Terminal
    );
    opened
        .harness
        .abort_task(background.owner, context())
        .await
        .unwrap();
    opened.harness.close(context()).await.unwrap();
}

/// TS `derives marks a crash left unapplied below ${label} at open`.
async fn derives_marks_a_crash_left_unapplied_below(abort_requested: bool, state: TaskState) {
    let world = World::new();
    let (_directory, path) = sqlite_path("pi-durable-ownership-");
    // Without a Harness, nothing derives marks: a cancelled owner with a live task below it.
    let session = create_session(
        sqlite(&path).await,
        crate::session::SessionOptions::default(),
    );
    let hold = world.hold.clone();
    let (owner, inner) = session
        .commit(
            move |tx| async move {
                let root = tx
                    .create_conversation(ConversationOwnership::Ownerless)
                    .await?;
                let owner = create_task_in(
                    &tx,
                    &hold,
                    &HoldInput::named("gone"),
                    options(Some(root.id), None),
                )
                .await?;
                let child = tx
                    .create_conversation(ConversationOwnership::Task { task_id: owner })
                    .await?;
                let inner = create_task_in(
                    &tx,
                    &hold,
                    &HoldInput::named("orphan"),
                    options(Some(child.id), None),
                )
                .await?;
                Ok((owner, inner))
            },
            context(),
        )
        .await
        .unwrap();
    session
        .commit(
            move |tx| async move {
                let record = tx.task(owner).await?.expect("the owner exists");
                tx.set_task(TaskRecord {
                    abort_requested,
                    state,
                    ..record
                })
            },
            context(),
        )
        .await
        .unwrap();
    session.close(context()).await.unwrap();

    let Opened { harness, .. } = open_harness(&world, sqlite(&path).await).await;
    assert_eq!(
        outcome_of(&harness, inner).await,
        TaskOutcomeStatus::Aborted
    );
    // The owner finishes only after the work below it.
    let outcome = outcome_of(&harness, owner).await;
    assert_eq!(
        outcome,
        if abort_requested {
            TaskOutcomeStatus::Aborted
        } else {
            TaskOutcomeStatus::Failed
        }
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn derives_marks_a_crash_left_unapplied_below_a_held_failed_owner_at_open() {
    derives_marks_a_crash_left_unapplied_below(
        false,
        TaskState::Completing {
            outcome: TaskOutcome::Failed {
                error: TaskOutcomeError {
                    message: "crash".to_owned(),
                    detail: None,
                },
                result: None,
            },
        },
    )
    .await;
}

#[tokio::test]
async fn derives_marks_a_crash_left_unapplied_below_an_abort_marked_owner_at_open() {
    derives_marks_a_crash_left_unapplied_below(
        true,
        TaskState::Pending {
            checkpoint: json(r#"{"phase":"hold"}"#),
        },
    )
    .await;
}

#[tokio::test]
async fn withdraws_an_input_queued_below_a_held_failed_owner_after_its_cascade() {
    let world = World::new();
    let Opened { harness, root, .. } = open_harness(&world, memory()).await;
    let tree = owned_child(
        &world,
        &root,
        "owner",
        TreeOptions {
            slow_inner: true,
            ..TreeOptions::default()
        },
    )
    .await;
    let child = harness
        .conversation(tree.child, context())
        .await
        .unwrap()
        .unwrap();
    // The inner task stands in for the child's run, which stays busy after the cascade.
    busy(&child, tree.inner).await;
    world.open("owner", Ending::Failed);
    until_abort_requested(&harness, tree.inner).await;
    let late = child
        .submit(InputSubmissionDraft::new("late"), context())
        .await
        .unwrap();
    let settled_late = late.wait(context()).await.unwrap();
    assert_eq!(settled_late.state.status(), SubmissionStatus::Unanswered);
    assert_eq!(settled_late.state.reason(), Some("aborted"));
    world.open("abort.owner.inner", Ending::Completed);
    harness.wait_for_task(tree.owner, context()).await.unwrap();
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn marks_work_admitted_after_reopen_below_a_cancelled_owner_whose_edge_was_not_loaded() {
    let world = World::new();
    let (_directory, path) = sqlite_path("pi-durable-ownership-");
    let opened = open_harness(&world, sqlite(&path).await).await;
    let tree = owned_child(
        &world,
        &opened.root,
        "owner",
        TreeOptions {
            slow_owner: true,
            ..TreeOptions::default()
        },
    )
    .await;
    world.open("owner.inner", Ending::Completed);
    opened
        .harness
        .wait_for_task(tree.inner, context())
        .await
        .unwrap();
    // The owner stays live and cancelled in its slow abort handler.
    opened
        .harness
        .abort_task(tree.owner, context())
        .await
        .unwrap();
    opened.harness.close(context()).await.unwrap();

    // The child is empty at open, so nothing loads its edge until new work arrives.
    let opened = open_harness(&world, sqlite(&path).await).await;
    let child = opened
        .harness
        .conversation(tree.child, context())
        .await
        .unwrap()
        .unwrap();
    let late = create_in(&world, &child, "late").await;
    assert_eq!(
        outcome_of(&opened.harness, late).await,
        TaskOutcomeStatus::Aborted
    );
    world.open("abort.owner", Ending::Completed);
    assert_eq!(
        outcome_of(&opened.harness, tree.owner).await,
        TaskOutcomeStatus::Aborted
    );
    opened.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn cascades_from_an_owner_the_scheduler_orphans() {
    let world = World::new();
    let Opened { harness, root, .. } = open_harness(&world, memory()).await;
    let (unregistered, hold) = (unregistered_task(), world.hold.clone());
    let (owner, inner) = root
        .commit(
            move |tx| async move {
                let owner = create_task_in(
                    &tx,
                    &unregistered,
                    &HoldInput::named("unregistered"),
                    options(None, None),
                )
                .await?;
                let child = tx
                    .create_conversation(ConversationOwnership::Task { task_id: owner })
                    .await?;
                let inner = create_task_in(
                    &tx,
                    &hold,
                    &HoldInput::named("below"),
                    options(Some(child.id), None),
                )
                .await?;
                Ok((owner, inner))
            },
            context(),
        )
        .await
        .unwrap();
    assert_eq!(
        harness.abort_task(owner, context()).await.unwrap(),
        TaskAbortResult::Marked
    );
    assert_eq!(
        harness
            .wait_for_task(owner, context())
            .await
            .unwrap()
            .outcome,
        TaskOutcome::Orphaned {
            reason: "missing_task".to_owned(),
        }
    );
    assert_eq!(
        outcome_of(&harness, inner).await,
        TaskOutcomeStatus::Aborted
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn cancels_only_the_callers_wait_never_the_shared_work() {
    let world = World::new();
    let Opened { harness, root, .. } = open_harness(&world, memory()).await;
    let tree = owned_child(&world, &root, "owner", TreeOptions::default()).await;
    let (waiting_context, waiting) = with_cancel(context());
    let idle = tokio::spawn(root.wait_for_idle(&waiting_context));
    waiting.cancel(Some(Arc::new(std::io::Error::other("stop waiting"))));
    let error = idle.await.unwrap().unwrap_err();
    assert!(error.to_string().contains("stop waiting"), "{error}");
    assert_ne!(
        status(&harness, tree.inner).await.status(),
        TaskStatus::Terminal
    );

    // Cancelling an abort after its commit leaves the marks in place.
    let slow = owned_child(&world, &root, "slow", TreeOptions::default()).await;
    let slow_owner = slow.owner;
    root.commit(
        move |tx| async move {
            let record = tx.task(slow_owner).await?.expect("the owner exists");
            tx.set_task(TaskRecord {
                input: to_json(&HoldInput::slow("slow", true))?,
                ..record
            })
        },
        context(),
    )
    .await
    .unwrap();
    let (aborting_context, aborting) = with_cancel(context());
    let abort = tokio::spawn(root.abort(ConversationAbortOptions::default(), &aborting_context));
    until_abort_requested(&harness, slow.owner).await;
    aborting.cancel(Some(Arc::new(std::io::Error::other("stop aborting"))));
    let error = abort.await.unwrap().unwrap_err();
    assert!(error.to_string().contains("stop aborting"), "{error}");
    world.open("abort.slow", Ending::Completed);
    for id in [tree.owner, tree.inner, slow.owner, slow.inner] {
        assert_eq!(outcome_of(&harness, id).await, TaskOutcomeStatus::Aborted);
    }
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn aborts_a_waiting_child_whose_awaited_task_completes_in_the_commit_that_marks_its_owner() {
    let world = World::new();
    let Opened { harness, root, .. } = open_harness(&world, memory()).await;
    let (hold, waiter) = (world.hold.clone(), world.waiter.clone());
    let (owner, dependency, blocked) = root
        .commit(
            move |tx| async move {
                let owner =
                    create_task_in(&tx, &hold, &HoldInput::named("owner"), options(None, None))
                        .await?;
                let child = tx
                    .create_conversation(ConversationOwnership::Task { task_id: owner })
                    .await?;
                let dependency = create_task_in(
                    &tx,
                    &hold,
                    &HoldInput::named("dependency"),
                    options(None, None),
                )
                .await?;
                let blocked = tx
                    .create_task(
                        waiter.erase().as_definition_ref(),
                        to_json(&WaiterInput {
                            on: vec![dependency],
                        })?,
                        options(Some(child.id), None),
                    )
                    .await?;
                Ok((owner, dependency, blocked))
            },
            context(),
        )
        .await
        .unwrap();
    let gates = &world.gates;
    wait_for(
        || async move { gates.runs("dependency") == Some(1) && gates.runs("owner") == Some(1) },
        WAIT_UNTIL_MS,
    )
    .await;
    until_status(&harness, blocked, TaskStatus::Waiting).await;
    // One commit completes the dependency and marks the owner.
    root.commit(
        move |tx| async move {
            let completed_dependency = tx.task(dependency).await?.expect("the dependency exists");
            let marked = tx.task(owner).await?.expect("the owner exists");
            tx.set_task(TaskRecord {
                state: TaskState::Terminal {
                    outcome: TaskOutcome::Completed {
                        result: JsonValue::Null,
                    },
                },
                ..completed_dependency
            })?;
            tx.set_task(TaskRecord {
                abort_requested: true,
                ..marked
            })
        },
        context(),
    )
    .await
    .unwrap();
    assert_eq!(
        outcome_of(&harness, blocked).await,
        TaskOutcomeStatus::Aborted
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn applies_marks_found_through_an_edge_loaded_after_reopen_once_a_failed_cascade_commit_is_reopened(
) {
    let world = World::new();
    let (_directory, path) = sqlite_path("pi-durable-ownership-");
    let opened = open_harness(&world, sqlite(&path).await).await;
    let tree = owned_child(
        &world,
        &opened.root,
        "owner",
        TreeOptions {
            slow_owner: true,
            ..TreeOptions::default()
        },
    )
    .await;
    world.open("owner.inner", Ending::Completed);
    opened
        .harness
        .wait_for_task(tree.inner, context())
        .await
        .unwrap();
    opened
        .harness
        .abort_task(tree.owner, context())
        .await
        .unwrap();
    opened.harness.close(context()).await.unwrap();

    let reject_mark: Arc<Mutex<Option<TaskId>>> = Arc::default();
    let storage = Arc::new(RejectMark {
        inner: sqlite(&path).await,
        mark: Arc::clone(&reject_mark),
    });
    let opened = open_harness(&world, storage).await;
    let child = opened
        .harness
        .conversation(tree.child, context())
        .await
        .unwrap()
        .unwrap();
    let (hold, mark) = (world.hold.clone(), Arc::clone(&reject_mark));
    let late = child
        .commit(
            move |tx| async move {
                let id = create_task_in(&tx, &hold, &HoldInput::named("late"), options(None, None))
                    .await?;
                *mark.lock().unwrap_or_else(PoisonError::into_inner) = Some(id);
                Ok(id)
            },
            context(),
        )
        .await
        .unwrap();
    // The failed cascade commit fails the Harness. `closed` settles once its
    // invocations have ended, and the owner's abort handler ignores its
    // signal: let it return.
    world.open("abort.owner", Ending::Completed);
    assert!(matches!(
        opened.harness.closed().await,
        SessionEnd::Failed { .. }
    ));
    opened.harness.close(context()).await.unwrap();
    // Reopening derives the mark again.
    let opened = open_harness(&world, sqlite(&path).await).await;
    assert_eq!(
        outcome_of(&opened.harness, late).await,
        TaskOutcomeStatus::Aborted
    );
    opened.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn fails_the_harness_on_a_failed_cascade_commit_and_reopening_applies_the_cascade() {
    let world = World::new();
    let reject_mark: Arc<Mutex<Option<TaskId>>> = Arc::default();
    let memory = ControlledStorage::new();
    let storage = Arc::new(RejectMark {
        inner: Arc::clone(&memory) as Arc<dyn Storage>,
        mark: Arc::clone(&reject_mark),
    });
    let Opened {
        harness,
        root,
        reports,
    } = open_harness(&world, Arc::clone(&storage) as Arc<dyn Storage>).await;
    let tree = owned_child(&world, &root, "owner", TreeOptions::default()).await;
    *reject_mark.lock().unwrap_or_else(PoisonError::into_inner) = Some(tree.inner);
    world.open("owner", Ending::Failed);
    let end = harness.closed().await;
    assert!(
        matches!(&end, SessionEnd::Failed { error } if error.to_string() == "disk gone"),
        "{end:?}"
    );
    let reported = reports.all();
    assert_eq!(reported.len(), 1);
    assert_eq!(reported[0].to_string(), "disk gone");
    harness.close(context()).await.unwrap();
    memory.reopen();
    let reopened = open_harness(&world, storage).await;
    assert_eq!(
        outcome_of(&reopened.harness, tree.inner).await,
        TaskOutcomeStatus::Aborted
    );
    reopened.harness.close(context()).await.unwrap();
}
