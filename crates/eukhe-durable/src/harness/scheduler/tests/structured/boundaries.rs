//! `describe("boundaries")`: background and terminal owners.

use super::{
    create, in_conversation, open_memory_nodes, outcome_of, owned_conversation, running, status,
    until, wait_on, Behavior, Opened, Script, BACKGROUND,
};
use crate::harness::tests::support::context;
use crate::harness::tests::task_support::aborted;
use crate::harness::types::ConversationAbortOptions;
use crate::types::{JoinPolicy, TaskOutcomeStatus, TaskStatus};

#[tokio::test]
async fn keeps_background_work_through_conversation_abort_background_true_aborts_it_and_waits() {
    let script = Script::new();
    let Opened { harness, root, .. } = open_memory_nodes(&script).await;
    let foreground = script.start(&root, "foreground").await;
    script.script(
        "background",
        Behavior::default().run(|script, runtime, cx| async move {
            let owner = runtime.task_id().erase();
            runtime
                .commit(
                    move |tx, _| async move {
                        let child = script.spawn(&tx, owner, "child").await?;
                        script.slot("child").resolve(child);
                        let conversation =
                            tx.create_conversation(owned_conversation(owner)).await?;
                        let below = create(
                            &tx,
                            script.node(),
                            "below",
                            in_conversation(conversation.id),
                        )
                        .await?;
                        script.slot("below").resolve(below);
                        Ok(Some(wait_on(vec![child], JoinPolicy::AllSettled, 1)))
                    },
                    &cx,
                )
                .await
        }),
    );
    let background = script.start_with(&root, "background", BACKGROUND).await;
    let logged = &script;
    until(|| async move { logged.logged("run:below") && logged.logged("run:child") }).await;
    root.abort(ConversationAbortOptions::default(), context())
        .await
        .unwrap();
    assert_eq!(
        outcome_of(&harness, foreground).await,
        TaskOutcomeStatus::Aborted
    );
    let ids = [
        background,
        script.id("child").await,
        script.id("below").await,
    ];
    for id in ids {
        assert_ne!(status(&harness, id).await, TaskStatus::Terminal);
    }
    root.abort(ConversationAbortOptions { background: true }, context())
        .await
        .unwrap();
    for id in ids {
        assert_eq!(status(&harness, id).await, TaskStatus::Terminal);
    }
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn never_cascades_from_a_terminal_owner_an_aborted_subagents_conversation_runs_new_work_normally(
) {
    let script = Script::new();
    let Opened { harness, root, .. } = open_memory_nodes(&script).await;
    script.script(
        "agent",
        Behavior::default()
            .run(|script, runtime, cx| async move {
                let owner = runtime.task_id().erase();
                runtime
                    .commit(
                        move |tx, _| async move {
                            let conversation =
                                tx.create_conversation(owned_conversation(owner)).await?;
                            script.conversation_slot("agent").resolve(conversation.id);
                            Ok(Some(running(1)))
                        },
                        &cx,
                    )
                    .await
            })
            .resume(|_, runtime, _, _| async move { Err(aborted(&runtime.signal()).await) }),
    );
    let agent = script.start(&root, "agent").await;
    let logged = &script;
    until(|| async move { logged.logged("resume:agent") }).await;
    harness.abort_task(agent, context()).await.unwrap();
    assert_eq!(
        outcome_of(&harness, agent).await,
        TaskOutcomeStatus::Aborted
    );
    let conversation = script.conversation_id("agent").await;
    let child = harness
        .conversation(conversation, context())
        .await
        .unwrap()
        .unwrap();
    let question = script.start(&child, "question").await;
    script.open("question");
    assert_eq!(
        outcome_of(&harness, question).await,
        TaskOutcomeStatus::Completed
    );
    harness.close(context()).await.unwrap();
}
