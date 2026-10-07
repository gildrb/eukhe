//! `describe("recovery through ownership edges")` over native SQLite storage.

use super::{
    create, in_conversation, inspected, open_nodes, outcome_of, owned_conversation, parent_of,
    running, sqlite, sqlite_path, status, until, Behavior, Script, BACKGROUND,
};
use crate::harness::tests::support::context;
use crate::harness::tests::task_support::{open_tasks, settled, OpenTasksOptions};
use crate::harness::types::{ConversationAbortOptions, TaskInspectionState};
use crate::session::create_session;
use crate::types::{ConversationOwnership, JoinPolicy, TaskOutcomeStatus, TaskStatus};

#[tokio::test]
async fn shows_an_abort_marked_owner_waiting_for_work_in_its_owned_conversation_before_resume_after_reopen(
) {
    let script = Script::new();
    let (_directory, path) = sqlite_path();
    let session = create_session(sqlite(&path).await);
    let node = script.node().clone();
    let (owner, inner) = session
        .commit(
            move |tx| async move {
                let conversation = tx
                    .create_conversation(ConversationOwnership::Ownerless)
                    .await?;
                let owner = create(&tx, &node, "owner", in_conversation(conversation.id)).await?;
                let child = tx.create_conversation(owned_conversation(owner)).await?;
                let inner = create(&tx, &node, "inner", in_conversation(child.id)).await?;
                Ok((owner, inner))
            },
            context(),
        )
        .await
        .unwrap();
    session
        .commit(
            move |tx| async move {
                let mut record = tx.task(owner).await?.expect("the owner exists");
                record.abort_requested = true;
                tx.set_task(record)
            },
            context(),
        )
        .await
        .unwrap();
    session.close(context()).await.unwrap();

    let opened = open_tasks(
        sqlite(&path).await,
        &[script.node().clone()],
        OpenTasksOptions::default(),
    )
    .await;
    let harness = opened.harness;
    match inspected(&harness, owner).await {
        Some(TaskInspectionState::Waiting { on }) => assert_eq!(on, [inner]),
        other => panic!("expected a waiting inspection, got {other:?}"),
    }
    harness.resume().unwrap();
    assert_eq!(
        outcome_of(&harness, owner).await,
        TaskOutcomeStatus::Aborted
    );
    assert_eq!(
        script.log_starting("abort:"),
        ["abort:inner", "abort:owner"]
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn keeps_the_root_busy_after_reopen_for_work_below_a_child_tasks_owned_conversation() {
    let script = Script::new();
    let (_directory, path) = sqlite_path();
    script.script(
        "child",
        Behavior::default().run(|script, runtime, cx| async move {
            let owner = runtime.task_id().erase();
            runtime
                .commit(
                    move |tx, _| async move {
                        let conversation =
                            tx.create_conversation(owned_conversation(owner)).await?;
                        let inner = create(
                            &tx,
                            script.node(),
                            "inner",
                            in_conversation(conversation.id),
                        )
                        .await?;
                        script.slot("inner").resolve(inner);
                        Ok(Some(running(1)))
                    },
                    &cx,
                )
                .await
        }),
    );
    parent_of(&script, "parent", &["child"], JoinPolicy::AllSettled);
    let opened = open_nodes(&script, sqlite(&path).await).await;
    let parent = script.start(&opened.root, "parent").await;
    let logged = &script;
    until(|| async move { logged.logged("run:inner") }).await;
    opened.harness.close(context()).await.unwrap();

    let opened = open_nodes(&script, sqlite(&path).await).await;
    let idle = tokio::spawn(opened.root.wait_for_idle(context()));
    assert!(!settled(&idle).await);
    script.open("inner");
    opened.root.wait_for_idle(context()).await.unwrap();
    assert_eq!(
        outcome_of(&opened.harness, parent).await,
        TaskOutcomeStatus::Completed
    );
    assert!(script.slot("inner").is_settled());
    opened.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn keeps_a_finished_background_ancestor_a_boundary_after_reopen_which_background_true_crosses(
) {
    let script = Script::new();
    let (_directory, path) = sqlite_path();
    script.script(
        "child",
        Behavior::default().run(|script, runtime, cx| async move {
            let owner = runtime.task_id().erase();
            runtime
                .commit(
                    move |tx, _| async move {
                        let conversation =
                            tx.create_conversation(owned_conversation(owner)).await?;
                        script.conversation_slot("child").resolve(conversation.id);
                        Ok(Some(running(1)))
                    },
                    &cx,
                )
                .await
        }),
    );
    parent_of(&script, "background", &["child"], JoinPolicy::AllSettled);
    let opened = open_nodes(&script, sqlite(&path).await).await;
    let background = script
        .start_with(&opened.root, "background", BACKGROUND)
        .await;
    opened
        .harness
        .wait_for_task(background, context())
        .await
        .unwrap();
    opened.harness.close(context()).await.unwrap();

    let opened = open_nodes(&script, sqlite(&path).await).await;
    let conversation = script.conversation_id("child").await;
    let child = opened
        .harness
        .conversation(conversation, context())
        .await
        .unwrap()
        .unwrap();
    let below = script.start(&child, "below").await;
    let logged = &script;
    until(|| async move { logged.logged("run:below") }).await;
    opened.root.wait_for_idle(context()).await.unwrap();
    opened
        .root
        .abort(ConversationAbortOptions::default(), context())
        .await
        .unwrap();
    assert_eq!(status(&opened.harness, below).await, TaskStatus::Running);
    opened
        .root
        .abort(ConversationAbortOptions { background: true }, context())
        .await
        .unwrap();
    assert_eq!(
        outcome_of(&opened.harness, below).await,
        TaskOutcomeStatus::Aborted
    );
    opened.harness.close(context()).await.unwrap();
}
