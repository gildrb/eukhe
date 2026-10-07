//! `describe("recovery")` over native SQLite storage.

use super::{
    completed_state, failed_state, json, open_nodes, outcome_of, parent_of, seed, sqlite,
    sqlite_path, state, until, until_status, waiting_state, Opened, Patch, Script, Seeded,
};
use crate::harness::tests::support::context;
use crate::types::{JoinPolicy, TaskOutcome, TaskOutcomeStatus, TaskState, TaskStatus};

#[tokio::test]
async fn resumes_a_parent_whose_awaited_children_finished_before_the_crash() {
    let script = Script::new();
    let (_directory, path) = sqlite_path();
    let Seeded { parent, children } = seed(&script, &path, &["c1"], |seeded| {
        vec![
            Patch::state(seeded.children[0], completed_state()),
            Patch::state(
                seeded.parent,
                waiting_state(seeded.children.clone(), JoinPolicy::AllSettled),
            ),
        ]
    })
    .await;
    let Opened { harness, .. } = open_nodes(&script, sqlite(&path).await).await;
    assert_eq!(
        outcome_of(&harness, parent).await,
        TaskOutcomeStatus::Completed
    );
    assert_eq!(script.log(), ["resume:parent"]);
    assert_eq!(children.len(), 1);
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn marks_fail_fast_siblings_a_crash_left_unmarked() {
    let script = Script::new();
    let (_directory, path) = sqlite_path();
    let Seeded { parent, children } = seed(&script, &path, &["c1", "c2"], |seeded| {
        vec![
            Patch::state(seeded.children[0], failed_state()),
            Patch::state(
                seeded.parent,
                waiting_state(seeded.children.clone(), JoinPolicy::FailFast),
            ),
        ]
    })
    .await;
    let Opened { harness, .. } = open_nodes(&script, sqlite(&path).await).await;
    assert_eq!(
        outcome_of(&harness, children[1]).await,
        TaskOutcomeStatus::Aborted
    );
    assert_eq!(
        outcome_of(&harness, parent).await,
        TaskOutcomeStatus::Completed
    );
    assert!(!script.logged("run:c2"));
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn finalizes_a_held_outcome_whose_work_drained_before_the_crash_and_keeps_one_whose_work_lives(
) {
    let script = Script::new();
    let (_directory, path) = sqlite_path();
    let held = || TaskState::Completing {
        outcome: TaskOutcome::Completed {
            result: json(r#""parent""#),
        },
    };
    let Seeded { parent, children } = seed(&script, &path, &["c1"], |seeded| {
        vec![Patch::state(seeded.parent, held())]
    })
    .await;
    let opened = open_nodes(&script, sqlite(&path).await).await;
    let logged = &script;
    until(|| async move { logged.logged("run:c1") }).await;
    assert_eq!(state(&opened.harness, parent).await, held());
    opened.harness.close(context()).await.unwrap();

    let opened = open_nodes(&script, sqlite(&path).await).await;
    script.open("c1");
    assert_eq!(
        outcome_of(&opened.harness, children[0]).await,
        TaskOutcomeStatus::Completed
    );
    assert_eq!(
        outcome_of(&opened.harness, parent).await,
        TaskOutcomeStatus::Completed
    );
    opened.harness.close(context()).await.unwrap();

    let (_drained_directory, drained) = sqlite_path();
    let second = seed(&script, &drained, &["c1"], |seeded| {
        vec![
            Patch::state(seeded.children[0], completed_state()),
            Patch::state(seeded.parent, held()),
        ]
    })
    .await;
    let opened = open_nodes(&script, sqlite(&drained).await).await;
    assert_eq!(
        outcome_of(&opened.harness, second.parent).await,
        TaskOutcomeStatus::Completed
    );
    opened.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn resumes_a_bottom_up_abort_a_crash_interrupted_before_the_cascade() {
    let script = Script::new();
    let (_directory, path) = sqlite_path();
    let Seeded { parent, children } = seed(&script, &path, &["c1"], |seeded| {
        vec![Patch {
            id: seeded.parent,
            abort_requested: Some(true),
            state: Some(waiting_state(
                seeded.children.clone(),
                JoinPolicy::AllSettled,
            )),
        }]
    })
    .await;
    let Opened { harness, .. } = open_nodes(&script, sqlite(&path).await).await;
    assert_eq!(
        outcome_of(&harness, parent).await,
        TaskOutcomeStatus::Aborted
    );
    assert_eq!(
        outcome_of(&harness, children[0]).await,
        TaskOutcomeStatus::Aborted
    );
    assert_eq!(script.log_starting("abort:"), ["abort:c1", "abort:parent"]);
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn reopens_a_checkout_waiting_on_live_payments_and_finishes_it() {
    let script = Script::new();
    let (_directory, path) = sqlite_path();
    parent_of(&script, "checkout", &["p1", "p2"], JoinPolicy::FailFast);
    let opened = open_nodes(&script, sqlite(&path).await).await;
    let parent = script.start(&opened.root, "checkout").await;
    until_status(&opened.harness, parent, TaskStatus::Waiting).await;
    let logged = &script;
    until(|| async move { logged.logged("run:p1") && logged.logged("run:p2") }).await;
    opened.harness.close(context()).await.unwrap();

    let opened = open_nodes(&script, sqlite(&path).await).await;
    let TaskState::Waiting { on, .. } = state(&opened.harness, parent).await else {
        panic!("the checkout is waiting");
    };
    script.set_ids("checkout", on);
    script.open("p1");
    script.open("p2");
    assert_eq!(
        outcome_of(&opened.harness, parent).await,
        TaskOutcomeStatus::Completed
    );
    assert_eq!(
        script.outcomes("checkout"),
        [TaskOutcomeStatus::Completed, TaskOutcomeStatus::Completed]
    );
    opened.harness.close(context()).await.unwrap();
}
