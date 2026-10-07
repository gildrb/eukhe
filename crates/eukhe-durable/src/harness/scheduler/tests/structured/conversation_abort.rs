//! `describe("conversation abort and boundaries")`.

use std::sync::Arc;

use super::rejecting::{is_rejection, Rejecting};
use super::{
    create, marked, open_memory_nodes, open_nodes, outcome_of, owned_conversation,
    spawn_and_finish, status, until, until_status, Behavior, Opened, Script, BACKGROUND,
    OWN_CONVERSATION,
};
use crate::harness::tests::support::context;
use crate::harness::types::ConversationAbortOptions;
use crate::types::{EntryDraft, TaskOptions, TaskOutcomeStatus, TaskStatus};

#[tokio::test]
async fn marks_a_held_completed_task_with_conversation_abort_the_work_below_is_aborted_the_outcome_stays(
) {
    let script = Script::new();
    let Opened { harness, root, .. } = open_memory_nodes(&script).await;
    spawn_and_finish(&script, "held", "child");
    let held = script.start(&root, "held").await;
    until_status(&harness, held, TaskStatus::Completing).await;
    root.abort(ConversationAbortOptions::default(), context())
        .await
        .unwrap();
    let child = script.id("held").await;
    assert_eq!(
        outcome_of(&harness, child).await,
        TaskOutcomeStatus::Aborted
    );
    let record = harness.wait_for_task(held, context()).await.unwrap();
    assert_eq!(record.outcome.status(), TaskOutcomeStatus::Completed);
    assert!(record.abort_requested);
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn marks_and_awaits_only_the_background_work_reached_when_background_true_is_admitted() {
    let script = Script::new();
    let Opened { harness, root, .. } = open_memory_nodes(&script).await;
    script.script("first", Behavior::default().gated_abort("abort.first"));
    let first = script.start_with(&root, "first", BACKGROUND).await;
    let logged = &script;
    until(|| async move { logged.logged("run:first") }).await;
    let aborting =
        tokio::spawn(root.abort(ConversationAbortOptions { background: true }, context()));
    let reader = &harness;
    until(|| async move { marked(reader, first).await }).await;
    let later = script.start_with(&root, "later", BACKGROUND).await;
    script.open("abort.first");
    aborting.await.unwrap().unwrap();
    assert_ne!(status(&harness, later).await, TaskStatus::Terminal);
    assert!(!marked(&harness, later).await);
    harness.abort_task(later, context()).await.unwrap();
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn stops_a_cascade_at_an_unmarked_background_task_but_not_at_a_marked_one() {
    let script = Script::new();
    let Opened { harness, root, .. } = open_memory_nodes(&script).await;
    script.script("owner", Behavior::default().gated_abort("abort.owner"));
    let node = script.node().clone();
    let (owner, outer, background, inner) = root
        .commit(
            move |tx| async move {
                let owner = create(&tx, &node, "owner", OWN_CONVERSATION).await?;
                let outer = tx.create_conversation(owned_conversation(owner)).await?;
                let background = create(
                    &tx,
                    &node,
                    "background",
                    TaskOptions {
                        conversation_id: Some(outer.id),
                        background: Some(true),
                        ..OWN_CONVERSATION
                    },
                )
                .await?;
                let inner = tx
                    .create_conversation(owned_conversation(background))
                    .await?;
                Ok((owner, outer.id, background, inner.id))
            },
            context(),
        )
        .await
        .unwrap();
    let logged = &script;
    until(|| async move { logged.logged("run:owner") && logged.logged("run:background") }).await;
    // The owner's abort handler starts at once: background work is not its ordinary owned work.
    harness.abort_task(owner, context()).await.unwrap();
    until(|| async move { logged.logged("abort:owner") }).await;
    let inner = harness
        .conversation(inner, context())
        .await
        .unwrap()
        .unwrap();
    let outer = harness
        .conversation(outer, context())
        .await
        .unwrap()
        .unwrap();
    let shielded = script.start(&inner, "shielded").await;
    let exposed = script.start(&outer, "exposed").await;
    assert_eq!(
        outcome_of(&harness, exposed).await,
        TaskOutcomeStatus::Aborted
    );
    assert!(!marked(&harness, shielded).await);
    // Marked directly, the background task cascades into its own subtree.
    harness.abort_task(background, context()).await.unwrap();
    assert_eq!(
        outcome_of(&harness, shielded).await,
        TaskOutcomeStatus::Aborted
    );
    assert_eq!(
        outcome_of(&harness, background).await,
        TaskOutcomeStatus::Aborted
    );
    script.open("abort.owner");
    assert_eq!(
        outcome_of(&harness, owner).await,
        TaskOutcomeStatus::Aborted
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn retries_a_finalization_the_storage_rejected_with_the_next_commit() {
    let script = Script::new();
    let storage = Rejecting::new();
    let Opened {
        harness,
        root,
        reports,
        ..
    } = open_nodes(&script, Arc::clone(&storage) as _).await;
    spawn_and_finish(&script, "parent", "child");
    let parent = script.start(&root, "parent").await;
    until_status(&harness, parent, TaskStatus::Completing).await;
    storage.arm(parent);
    script.open("child");
    let child = script.id("parent").await;
    harness.wait_for_task(child, context()).await.unwrap();
    let reported = &reports;
    until(|| async move { reported.all().iter().any(is_rejection) }).await;
    assert_eq!(status(&harness, parent).await, TaskStatus::Completing);
    let conversation = root.id();
    root.commit(
        move |tx| async move {
            tx.append_entry(conversation, EntryDraft::new("note"))
                .await?;
            Ok(())
        },
        context(),
    )
    .await
    .unwrap();
    assert_eq!(
        outcome_of(&harness, parent).await,
        TaskOutcomeStatus::Completed
    );
    harness.close(context()).await.unwrap();
}
