//! `describe("task ownership")`.

use std::sync::Arc;

use eukhe_chord::json::from_json;

use super::{
    assert_faulted, assert_rejects, create, end, in_conversation, json, open_memory_nodes,
    outcome_of, owned, owned_conversation, record, running, settle, until, until_status, wait_on,
    Behavior, End, NodeInput, Opened, Script,
};
use crate::harness::tests::support::context;
use crate::harness::tests::task_support::settled;
use crate::harness::types::ConversationCreateOptions;
use crate::types::{
    ConversationOwnership, JoinPolicy, TaskId, TaskOptions, TaskOutcomeStatus, TaskQuery,
    TaskStatus,
};

#[tokio::test]
async fn creates_a_child_in_its_owners_conversation_with_its_owner_recorded() {
    let script = Script::new();
    let Opened { harness, root, .. } = open_memory_nodes(&script).await;
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
    let child = script.id("child").await;
    let child_record = record(&harness, child).await;
    assert_eq!(
        (
            child_record.owner,
            child_record.conversation_id,
            child_record.background
        ),
        (Some(parent), root.id(), false)
    );
    assert_eq!(record(&harness, parent).await.owner, None);
    script.open("child");
    assert_eq!(
        outcome_of(&harness, parent).await,
        TaskOutcomeStatus::Completed
    );
    harness.close(context()).await.unwrap();
}

/// TS `create({} as TaskOptions)` rejects because `ownership` is missing.
/// Rust's `TaskOptions` cannot omit it; the closest observable is that
/// options without `ownership` do not decode.
#[tokio::test]
async fn rejects_no_ownership_a_missing_owner_a_child_in_another_conversation_and_a_background_child(
) {
    let script = Script::new();
    let Opened { harness, root, .. } = open_memory_nodes(&script).await;
    let parent = script.start(&root, "parent").await;
    let other = harness
        .create_conversation(
            ConversationCreateOptions::new(ConversationOwnership::Ownerless),
            context(),
        )
        .await
        .unwrap();
    assert!(from_json::<TaskOptions>(&json("{}")).is_err());
    assert_rejects(
        script
            .try_start(&root, "x", owned(TaskId::from_number(999_999)))
            .await,
        "does not exist",
    );
    assert_rejects(
        script
            .try_start(
                &root,
                "x",
                TaskOptions {
                    conversation_id: Some(other.id()),
                    ..owned(parent)
                },
            )
            .await,
        "owner's conversation",
    );
    assert_rejects(
        script
            .try_start(
                &root,
                "x",
                TaskOptions {
                    background: Some(true),
                    ..owned(parent)
                },
            )
            .await,
        "cannot be background",
    );
    // The owner's conversation is the default, even from a commit bound to another conversation.
    let spawner = Arc::clone(&script);
    let child = other
        .commit(
            move |tx| async move { spawner.spawn(&tx, parent, "child").await },
            context(),
        )
        .await
        .unwrap();
    assert_eq!(record(&harness, child).await.conversation_id, root.id());
    script.open("parent");
    script.open("child");
    harness.wait_for_task(parent, context()).await.unwrap();
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn rejects_new_owned_work_below_an_owner_that_is_completing_terminal_or_abort_marked() {
    let script = Script::new();
    let Opened { harness, root, .. } = open_memory_nodes(&script).await;
    script.script(
        "parent",
        Behavior::default().run(|script, runtime, cx| async move {
            let owner = runtime.task_id().erase();
            runtime
                .commit(
                    move |tx, _| async move {
                        script.spawn(&tx, owner, "child").await?;
                        Ok(Some(running(1)))
                    },
                    &cx,
                )
                .await
        }),
    );
    let parent = script.start(&root, "parent").await;
    until_status(&harness, parent, TaskStatus::Completing).await;
    let create_child = || {
        let script = Arc::clone(&script);
        root.commit(
            move |tx| async move { script.spawn(&tx, parent, "late").await },
            context(),
        )
    };
    let create_conversation = || {
        root.commit(
            move |tx| async move { tx.create_conversation(owned_conversation(parent)).await },
            context(),
        )
    };
    assert_rejects(create_child().await, "is completing");
    assert_rejects(create_conversation().await, "is completing");
    script.open("child");
    harness.wait_for_task(parent, context()).await.unwrap();
    assert_rejects(create_child().await, "is terminal");
    assert_rejects(create_conversation().await, "is terminal");

    script.script("slow", Behavior::default().gated_abort("abort.slow"));
    let slow = script.start(&root, "slow").await;
    let logged = &script;
    until(|| async move { logged.logged("run:slow") }).await;
    harness.abort_task(slow, context()).await.unwrap();
    let spawner = Arc::clone(&script);
    assert_rejects(
        root.commit(
            move |tx| async move { spawner.spawn(&tx, slow, "late").await },
            context(),
        )
        .await,
        "is abort-marked",
    );
    script.open("abort.slow");
    assert_eq!(outcome_of(&harness, slow).await, TaskOutcomeStatus::Aborted);
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn cannot_create_a_child_in_its_finishing_commit_but_work_it_starts_in_an_owned_conversation_holds_it(
) {
    let script = Script::new();
    let Opened { harness, root, .. } = open_memory_nodes(&script).await;
    script.script(
        "eager",
        Behavior::default().run(|script, runtime, cx| async move {
            let owner = runtime.task_id().erase();
            runtime
                .commit(
                    move |tx, _| async move {
                        script.spawn(&tx, owner, "never").await?;
                        Ok(Some(end(End::Completed, "eager")))
                    },
                    &cx,
                )
                .await
        }),
    );
    let eager = script.start(&root, "eager").await;
    assert_faulted(&settle(&harness, eager).await, "is completing");
    // The rejected commit wrote nothing.
    let nodes = harness
        .commit(
            |tx| async move {
                tx.scan_tasks(
                    TaskQuery {
                        kind: Some("test.node".to_owned()),
                        ..TaskQuery::default()
                    },
                    20,
                    None,
                )
                .await
            },
            context(),
        )
        .await
        .unwrap();
    let names: Vec<String> = nodes
        .items
        .iter()
        .map(|task| from_json::<NodeInput>(&task.input).unwrap().name)
        .collect();
    assert_eq!(names, ["eager"]);

    script.script(
        "host",
        Behavior::default()
            .run(|script, runtime, cx| async move {
                let owner = runtime.task_id().erase();
                runtime
                    .commit(
                        move |tx, _| async move {
                            let child = tx.create_conversation(owned_conversation(owner)).await?;
                            script.conversation_slot("host").resolve(child.id);
                            Ok(Some(running(1)))
                        },
                        &cx,
                    )
                    .await
            })
            .resume(|script, runtime, cx, _| async move {
                let child = script.conversation_slot("host").wait().await;
                runtime
                    .commit(
                        move |tx, _| async move {
                            create(&tx, script.node(), "inner", in_conversation(child)).await?;
                            Ok(Some(end(End::Completed, "host")))
                        },
                        &cx,
                    )
                    .await
            }),
    );
    let host = script.start(&root, "host").await;
    until_status(&harness, host, TaskStatus::Completing).await;
    let waiter = tokio::spawn(harness.wait_for_task(host, context()));
    assert!(!settled(&waiter).await);
    script.open("inner");
    assert_eq!(
        outcome_of(&harness, host).await,
        TaskOutcomeStatus::Completed
    );
    harness.close(context()).await.unwrap();
}
