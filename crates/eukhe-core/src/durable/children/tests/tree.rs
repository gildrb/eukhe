//! The agent tree over the children: a split spawns both children in their
//! own copies with their places, a refused split names its first failing
//! check, a help leaf works read-only in the parent's directory, a failed
//! split child runs again once, and an abort of the turn cancels the
//! subtree.

use eukhe_types::daemon::agent_tree::{TreePlace, TreeRole};

use super::*;
use crate::child_workspace::WorkspaceMode;

/// The places and workspaces the host was asked to spawn, in order.
fn spawned(host: &FakeHost) -> Vec<(Option<TreePlace>, WorkspaceMode)> {
    lock(&host.state)
        .spawns
        .iter()
        .map(|spawn| (spawn.tree.clone(), spawn.workspace))
        .collect()
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_split_spawns_both_children_in_their_own_copies() {
    let setup = setup();
    let host = FakeHost::new();
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    split_children(&opened, &setup, &["src/a"], &["src/b", "docs"]).await;
    let place = |role, scope: &[&str], path: &str| TreePlace {
        role,
        scope: scope.iter().map(|path| (*path).to_owned()).collect(),
        path: path.to_owned(),
        allowance: 7,
        deadline: None,
    };
    assert_eq!(
        spawned(&host),
        vec![
            (
                Some(place(TreeRole::Left, &["src/a"], "L")),
                WorkspaceMode::Isolated
            ),
            (
                Some(place(TreeRole::Right, &["src/b", "docs"], "R")),
                WorkspaceMode::Isolated
            ),
        ]
    );
    opened.root.wait_for_idle(cx()).await.unwrap();
    opened.harness.close(cx()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_refused_split_names_its_first_failing_check_and_spawns_nothing() {
    let setup = setup();
    let host = FakeHost::new();
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    let split = |left: &str, right: &str| {
        json!({
            "left": { "scope": [left], "task": "l" },
            "right": { "scope": [right], "task": "r" },
        })
    };
    let overlapping = request_turn(&opened, &setup, "rlm.split", split("src", "src/a")).await;
    let empty = request_turn(
        &opened,
        &setup,
        "rlm.split",
        json!({ "left": { "scope": [], "task": "l" }, "right": { "scope": ["b"], "task": "r" } }),
    )
    .await;
    let spawns_after_refusals = host.spawn_keys().len();
    split_children(&opened, &setup, &["a"], &["b"]).await;
    let again = request_turn(&opened, &setup, "rlm.split", split("c", "d")).await;
    assert_eq!(
        (overlapping, empty, spawns_after_refusals, again),
        (
            "error: own, left and right must split the node's scope exactly, each half non-empty"
                .to_owned(),
            "error: rlm.split left scope must be a non-empty list of paths".to_owned(),
            0,
            "error: the node has already split".to_owned(),
        )
    );
    opened.root.wait_for_idle(cx()).await.unwrap();
    opened.harness.close(cx()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_help_leaf_works_read_only_in_the_parents_directory() {
    let setup = setup();
    let host = FakeHost::new();
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    spawn_child(&opened, &setup).await;
    assert_eq!(
        spawned(&host),
        vec![(
            Some(TreePlace {
                role: TreeRole::Help,
                scope: Vec::new(),
                path: String::new(),
                allowance: 1,
                deadline: None,
            }),
            WorkspaceMode::Shared
        )]
    );
    opened.root.wait_for_idle(cx()).await.unwrap();
    opened.harness.close(cx()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_failed_split_child_runs_again_once_then_reports_its_failure() {
    let setup = setup();
    let host = FakeHost::new();
    lock(&host.state).patch = Some(vec![None, Some(1), None]);
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    let [left, _right] = split_children(&opened, &setup, &["a"], &["b"]).await;
    eventually(|| async { host.prompt_keys().len() == 2 }).await;
    let failed = || RlmChildRunState::Failed {
        failure: eukhe_types::input_origin::ChildFailure::Aborted,
        error: "boom".to_owned(),
    };
    host.settle(&left.session_id, failed(), None);
    let redo = format!("rlm:{}:redo", left.task_id);
    eventually(|| async { host.prompt_keys().contains(&redo) }).await;
    let running = row_of(&opened.harness, left.task_id).await.unwrap().status;
    host.settle(&left.session_id, RlmChildRunState::Running, None);
    setup.faux.append_responses(vec![answer("noted")]);
    host.settle(&left.session_id, failed(), None);
    opened
        .harness
        .wait_for_task(TaskId::<Value>::from_number(left.task_id), cx())
        .await
        .unwrap();
    opened.root.wait_for_idle(cx()).await.unwrap();
    let row = row_of(&opened.harness, left.task_id).await.unwrap();
    assert_eq!(
        (
            running,
            row.status,
            row.patch,
            host.prompt_keys()
                .iter()
                .filter(|key| **key == redo)
                .count(),
        ),
        (
            ChildStatus::Running,
            ChildStatus::Error,
            Some(vec![None, Some(1), None]),
            1
        )
    );
    opened.harness.close(cx()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn an_abort_of_the_turn_cancels_every_child_of_the_subtree() {
    let setup = setup();
    let host = FakeHost::new();
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    let [left, right] = split_children(&opened, &setup, &["a"], &["b"]).await;
    eventually(|| async { host.prompt_keys().len() == 2 }).await;
    crate::durable::children::cancel_tree(&opened.harness, ROOT_CONVERSATION_ID, cx())
        .await
        .unwrap();
    for row in [&left, &right] {
        opened
            .harness
            .wait_for_task(TaskId::<Value>::from_number(row.task_id), cx())
            .await
            .unwrap();
    }
    let cancelled: Vec<String> = lock(&host.state)
        .cancels
        .iter()
        .map(|cancel| cancel.session_id.clone())
        .collect();
    let statuses = [
        row_of(&opened.harness, left.task_id).await.unwrap().status,
        row_of(&opened.harness, right.task_id).await.unwrap().status,
    ];
    assert_eq!(
        (cancelled, statuses),
        (
            vec![left.session_id.clone(), right.session_id.clone()],
            [ChildStatus::Cancelled, ChildStatus::Cancelled]
        )
    );
    opened.root.wait_for_idle(cx()).await.unwrap();
    opened.harness.close(cx()).await.unwrap();
}
