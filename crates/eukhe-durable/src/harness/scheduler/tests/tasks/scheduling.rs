//! `describe("task scheduling")`.

use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use eukhe_chord::context::{AbortController, Context};

use super::{
    assert_rejects, complete, faulted, gated, joined, lock, one_step, open_root, open_root_with,
    reason, start, start_background, with_signal, OpenedRoot, StepRuntime,
};
use crate::errors::{StorageError, StorageRejected};
use crate::harness::tests::support::{add_task, add_tool, context, tool_described};
use crate::harness::tests::task_support::{
    deferred, eventually, flush, settled, Deferred, OpenTasksOptions,
};
use crate::harness::types::ConversationCreateOptions;
use crate::harness::TaskAbortResult;
use crate::session::tests::support::ControlledStorage;
use crate::session::SessionError;
use crate::types::{ConversationOwnership, EntryDraft, TaskId, TaskStatus};

fn busy() -> StorageError {
    StorageError::Rejected(StorageRejected::new("busy"))
}

#[tokio::test]
async fn retries_reservation_on_the_next_wakeup_after_a_rejected_reservation_commit() {
    let runs = Arc::new(AtomicUsize::new(0));
    let once = one_step::<(), _, _>("test.once", {
        let runs = Arc::clone(&runs);
        move |_task, runtime: StepRuntime, cx: Context| {
            runs.fetch_add(1, Ordering::SeqCst);
            async move { complete(&runtime, (), &cx).await }
        }
    });
    let storage = ControlledStorage::new();
    let OpenedRoot {
        harness,
        root,
        registry,
        reports,
    } = open_root_with(
        storage.clone(),
        &[once.erase()],
        OpenTasksOptions::default(),
    )
    .await;
    let id = start(&root, &once).await;
    storage.fail_next_commit(busy());
    harness.resume().unwrap();
    eventually(|| std::future::ready(reports.len() == 1)).await;
    let record = harness.get_task(id, context()).await.unwrap().unwrap();
    assert_eq!(record.state.status(), TaskStatus::Pending);
    // Any wakeup, here a registry change, reserves again.
    add_tool(&registry, tool_described("wake", "wake"), None).unwrap();
    harness.wait_for_task(id, context()).await.unwrap();
    assert_eq!(runs.load(Ordering::SeqCst), 1);
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn keeps_a_wakeup_that_arrives_while_a_rejected_reservation_commit_is_in_storage() {
    let first = one_step::<(), _, _>(
        "test.wake-first",
        |_task, runtime: StepRuntime, cx: Context| async move { complete(&runtime, (), &cx).await },
    );
    let late = one_step::<(), _, _>(
        "test.wake-late",
        |_task, runtime: StepRuntime, cx: Context| async move { complete(&runtime, (), &cx).await },
    );
    let storage = ControlledStorage::new();
    let OpenedRoot {
        harness,
        root,
        registry,
        ..
    } = open_root_with(
        storage.clone(),
        &[first.erase()],
        OpenTasksOptions::default(),
    )
    .await;
    let first_id = start(&root, &first).await;
    let late_id = start(&root, &late).await;
    let held = storage.hold_commits();
    storage.fail_next_commit(busy());
    harness.resume().unwrap();
    held.entered().await;
    // Registering the missing definition wakes the scheduler while the doomed reservation is in storage.
    add_task(&registry, late.erase(), None).unwrap();
    held.release();
    harness.wait_for_task(first_id, context()).await.unwrap();
    harness.wait_for_task(late_id, context()).await.unwrap();
    harness.close(context()).await.unwrap();
}

/// TS `String(report)` is `StorageRejected: busy`; Rust displays the
/// rejection's message, and the report is the Storage rejection itself.
#[tokio::test]
async fn reruns_a_task_whose_fault_write_was_rejected() {
    let runs = Arc::new(AtomicUsize::new(0));
    let storage = ControlledStorage::new();
    let throws = one_step::<(), _, _>("test.rejected-fault", {
        let (runs, storage) = (Arc::clone(&runs), Arc::clone(&storage));
        move |_task, _runtime, _cx| {
            // The next commit is the step's fault write.
            if runs.fetch_add(1, Ordering::SeqCst) + 1 == 1 {
                storage.fail_next_commit(busy());
            }
            async { Err(SessionError::error("boom")) }
        }
    });
    let OpenedRoot {
        harness,
        root,
        reports,
        ..
    } = open_root_with(
        storage.clone(),
        &[throws.erase()],
        OpenTasksOptions::default(),
    )
    .await;
    let id = start(&root, &throws).await;
    harness.resume().unwrap();
    assert_eq!(super::outcome(&harness, id).await, faulted("boom"));
    assert_eq!(runs.load(Ordering::SeqCst), 2);
    let reports = reports.all();
    assert_eq!(reports.len(), 1);
    assert!(
        matches!(&reports[0], SessionError::Storage(StorageError::Rejected(rejection)) if rejection.to_string() == "busy"),
        "{:?}",
        reports[0]
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn waits_for_harness_and_conversation_idleness_counting_blocked_work_and_ignoring_background_tasks(
) {
    let gates: Arc<std::sync::Mutex<HashMap<TaskId, Deferred>>> = Arc::default();
    let gated_task = one_step::<(), _, _>("test.gated", {
        let gates = Arc::clone(&gates);
        move |task, runtime: StepRuntime, cx: Context| {
            let gate = deferred::<()>();
            let opened = gate.wait();
            lock(&gates).insert(task.id.erase(), gate);
            async move {
                opened.await;
                complete(&runtime, (), &cx).await
            }
        }
    });
    let open = |id: TaskId| lock(&gates).get(&id).expect("the task runs").resolve(());
    let OpenedRoot { harness, root, .. } = open_root(&[gated_task.erase()]).await;
    harness.wait_for_idle(context()).await.unwrap();
    let other = harness
        .create_conversation(
            ConversationCreateOptions::new(ConversationOwnership::Ownerless),
            context(),
        )
        .await
        .unwrap();
    let foreground = start(&root, &gated_task).await.erase();
    let background = start_background(&root, &gated_task).await.erase();
    let elsewhere = start(&other, &gated_task).await.erase();
    // Work that has not started yet is live; cancelling a wait only rejects that wait.
    let cancelled = AbortController::new();
    let cancelled_wait = tokio::spawn(harness.wait_for_idle(&with_signal(&cancelled.signal())));
    cancelled.abort(Some(reason("stop waiting")));
    assert_rejects(joined(cancelled_wait).await, "stop waiting");
    let aborted = AbortController::new();
    aborted.abort(Some(reason("already cancelled")));
    assert_rejects(
        root.wait_for_idle(&with_signal(&aborted.signal())).await,
        "already cancelled",
    );
    harness.resume().unwrap();
    eventually(|| std::future::ready(lock(&gates).len() == 3)).await;
    let root_idle = tokio::spawn(root.wait_for_idle(context()));
    let harness_idle = tokio::spawn(harness.wait_for_idle(context()));
    open(foreground);
    joined(root_idle).await.unwrap();
    assert!(!settled(&harness_idle).await);
    open(elsewhere);
    joined(harness_idle).await.unwrap();
    let record = harness
        .get_task(background, context())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(record.state.status(), TaskStatus::Running);
    open(background);
    harness.wait_for_task(background, context()).await.unwrap();
    harness.close(context()).await.unwrap();
    assert_rejects(harness.wait_for_idle(context()).await, "closed");
    assert_rejects(root.wait_for_idle(context()).await, "closed");
}

#[tokio::test]
async fn rejects_unknown_tasks_and_reports_terminal_tasks() {
    let done = one_step::<(), _, _>(
        "test.quick",
        |_task, runtime: StepRuntime, cx: Context| async move { complete(&runtime, (), &cx).await },
    );
    let OpenedRoot { harness, root, .. } = open_root(&[done.erase()]).await;
    let unknown = TaskId::from_number(999_999);
    assert_eq!(harness.get_task(unknown, context()).await.unwrap(), None);
    assert_rejects(
        harness.wait_for_task(unknown, context()).await,
        "does not exist",
    );
    assert_rejects(
        harness.abort_task(unknown, context()).await,
        "does not exist",
    );
    let id = start(&root, &done).await;
    harness.resume().unwrap();
    harness.wait_for_task(id, context()).await.unwrap();
    // A receipt is a terminal record.
    let receipt = harness.wait_for_task(id, context()).await.unwrap();
    assert_eq!(receipt.into_record().state.status(), TaskStatus::Terminal);
    assert_eq!(
        harness.abort_task(id.erase(), context()).await.unwrap(),
        TaskAbortResult::Terminal
    );
    harness.close(context()).await.unwrap();
    assert_rejects(harness.resume(), "closed");
}

#[tokio::test]
async fn rejects_task_waits_cancelled_or_closed_while_queued_on_the_line_and_pending_waits_on_close(
) {
    let gate = deferred::<()>();
    let blocking = gated("test.wait-close", &gate);
    let storage = ControlledStorage::new();
    let OpenedRoot { harness, root, .. } = open_root_with(
        storage.clone(),
        &[blocking.erase()],
        OpenTasksOptions::default(),
    )
    .await;
    let id = start(&root, &blocking).await;
    let root_id = root.id();
    let blocker = |harness: &crate::harness::Harness| {
        tokio::spawn(harness.commit(
            move |tx| async move {
                tx.append_entry(root_id, EntryDraft::new("blocker")).await?;
                Ok(())
            },
            context(),
        ))
    };

    // Hold the line with a commit, then queue waits behind it.
    let held = storage.hold_commits();
    let first_blocker = blocker(&harness);
    held.entered().await;
    let controller = AbortController::new();
    let cancelled_while_queued =
        tokio::spawn(harness.wait_for_task(id, &with_signal(&controller.signal())));
    controller.abort(Some(reason("wait cancelled")));
    held.release();
    joined(first_blocker).await.unwrap();
    assert_rejects(joined(cancelled_while_queued).await, "wait cancelled");

    let pending = tokio::spawn(harness.wait_for_task(id, context()));
    let idle = tokio::spawn(harness.wait_for_idle(context()));
    let conversation_idle = tokio::spawn(root.wait_for_idle(context()));
    flush().await;
    let held_again = storage.hold_commits();
    let blocker_again = blocker(&harness);
    held_again.entered().await;
    let closed_while_queued = tokio::spawn(harness.wait_for_task(id, context()));
    let closing = tokio::spawn(harness.close(context()));
    held_again.release();
    joined(blocker_again).await.unwrap();
    assert_rejects(joined(closed_while_queued).await, "closed");
    assert_rejects(joined(pending).await, "closed");
    assert_rejects(joined(idle).await, "closed");
    assert_rejects(joined(conversation_idle).await, "closed");
    gate.resolve(());
    joined(closing).await.unwrap();
}
