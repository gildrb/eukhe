//! A split child's workspace: the hand-back by its scope that a finished
//! child's report and registry row carry.

use super::*;
use crate::durable::children::registry::HandbackOutcome;

/// A split child that ends without a reply hands back the writes inside
/// its scope: the host gets the child's units and scope, the no-reply
/// report names the taken paths and the writes outside the scope, and the
/// registry row and `rlm.collect` keep the outcome.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_finished_split_child_hands_back_its_scope() {
    let setup = setup();
    let host = FakeHost::new();
    let handback = RlmChildHandback {
        handback: ScopedHandback {
            taken: vec!["a/x.txt".to_owned()],
            outside: vec!["b/y.txt".to_owned()],
            conflicts: Vec::new(),
            kept: Some("/workspaces/kept".to_owned()),
            patch: vec![None, Some(1), None],
        },
        child_check: CheckRun::None,
        parent_check: CheckRun::None,
    };
    lock(&host.state).handback = Some(handback.clone());
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    let [left, _right] = split_children(&opened, &setup, &["a"], &["b"]).await;
    eventually(|| async { host.prompt_keys().len() == 2 }).await;

    setup.faux.append_responses(vec![answer("noted")]);
    host.settle(
        &left.session_id,
        RlmChildRunState::Answered {
            answer_preview: Some("done".to_owned()),
        },
        None,
    );
    opened
        .harness
        .wait_for_task(TaskId::<Value>::from_number(left.task_id), cx())
        .await
        .unwrap();
    opened.root.wait_for_idle(cx()).await.unwrap();

    let outcome = HandbackOutcome::Done {
        handback: Box::new(handback.clone()),
    };
    let row = row_of(&opened.harness, left.task_id).await.unwrap();
    assert_eq!(
        (row, lock(&host.state).handbacks.clone()),
        (
            ChildRow {
                status: ChildStatus::Done,
                answer_preview: Some("done".to_owned()),
                settled: true,
                handback: Some(outcome.clone()),
                ..left.clone()
            },
            vec![RlmChildHandbackRequest {
                session_id: left.session_id.clone(),
                rlm_child_id: left.rlm_child_id.clone(),
                units: vec![String::new(), "a".to_owned(), "b".to_owned()],
                scope: vec![false, true, false],
            }],
        )
    );
    assert_eq!(
        user_texts(&opened.root, "[child-exited").await,
        [format!(
            "[child-exited: no-reply child:{}]\n\nResume your work using the result below.\n\nLast assistant text: done\n\n{}",
            left.session_name,
            handback.text()
        )]
    );
    let collected = handle(
        &opened,
        "rlm.collect",
        json!({ "targets": [left.rlm_child_id] }),
    )
    .await
    .unwrap();
    assert_eq!(
        collected["results"][0]["handback"],
        Value::from(outcome.text())
    );
    opened.harness.close(cx()).await.unwrap();
}

/// A writer's work reaches its parent as it arrives: while the writer's
/// checks still wait (a check queued for a slot), its row and
/// `rlm.collect` already show the hand-back, its checks to come; the
/// checks' results land on the row when they end.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_writers_hand_back_shows_before_its_checks_end() {
    let setup = setup();
    let host = FakeHost::new();
    let handback = RlmChildHandback {
        handback: ScopedHandback {
            taken: vec!["a/x.txt".to_owned()],
            outside: Vec::new(),
            conflicts: Vec::new(),
            kept: None,
            patch: vec![None, Some(1), None],
        },
        child_check: CheckRun::Ran {
            command: "./check.sh".to_owned(),
            outcome: crate::child_workspace::CheckOutcome::Passed,
            output: String::new(),
            duration_ms: 1_800_000,
        },
        parent_check: CheckRun::Ran {
            command: "./check.sh".to_owned(),
            outcome: crate::child_workspace::CheckOutcome::Failed { code: Some(1) },
            output: "FMT FAILED\n".to_owned(),
            duration_ms: 900,
        },
    };
    lock(&host.state).handback = Some(handback.clone());
    host.checks_open.send_replace(false);
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    let [left, _right] = split_children(&opened, &setup, &["a"], &["b"]).await;
    eventually(|| async { host.prompt_keys().len() == 2 }).await;

    setup.faux.append_responses(vec![answer("noted")]);
    host.settle(
        &left.session_id,
        RlmChildRunState::Answered {
            answer_preview: Some("done".to_owned()),
        },
        None,
    );
    eventually(|| async {
        row_of(&opened.harness, left.task_id)
            .await
            .is_some_and(|row| row.handback.is_some())
    })
    .await;
    let integrated = HandbackOutcome::Done {
        handback: Box::new(RlmChildHandback {
            child_check: CheckRun::Pending,
            parent_check: CheckRun::Pending,
            ..handback.clone()
        }),
    };
    let collected = handle(
        &opened,
        "rlm.collect",
        json!({ "targets": [left.rlm_child_id] }),
    )
    .await
    .unwrap();
    assert_eq!(
        (
            row_of(&opened.harness, left.task_id)
                .await
                .and_then(|row| row.handback),
            collected["results"][0]["handback"].clone(),
            lock(&host.state).checks.len(),
        ),
        (Some(integrated.clone()), Value::from(integrated.text()), 0)
    );

    host.checks_open.send_replace(true);
    opened
        .harness
        .wait_for_task(TaskId::<Value>::from_number(left.task_id), cx())
        .await
        .unwrap();
    opened.root.wait_for_idle(cx()).await.unwrap();
    assert_eq!(
        row_of(&opened.harness, left.task_id)
            .await
            .and_then(|row| row.handback),
        Some(HandbackOutcome::Done {
            handback: Box::new(handback),
        })
    );
    opened.harness.close(cx()).await.unwrap();
}

/// An abort that meets a writer after its integration, while its checks
/// wait, records what landed: the tree's node finished with the
/// integrated patch, the row done with its hand-back and its checks not
/// run, and the checkout closed.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn an_abort_during_the_checks_keeps_the_integration() {
    let setup = setup();
    let host = FakeHost::new();
    let handback = RlmChildHandback {
        handback: ScopedHandback {
            taken: vec!["a/x.txt".to_owned()],
            outside: Vec::new(),
            conflicts: Vec::new(),
            kept: None,
            patch: vec![None, Some(1), None],
        },
        child_check: CheckRun::None,
        parent_check: CheckRun::None,
    };
    lock(&host.state).handback = Some(handback.clone());
    host.checks_open.send_replace(false);
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    let [left, _right] = split_children(&opened, &setup, &["a"], &["b"]).await;
    eventually(|| async { host.prompt_keys().len() == 2 }).await;
    host.settle(
        &left.session_id,
        RlmChildRunState::Answered {
            answer_preview: Some("done".to_owned()),
        },
        None,
    );
    eventually(|| async {
        row_of(&opened.harness, left.task_id)
            .await
            .is_some_and(|row| row.handback.is_some())
    })
    .await;

    crate::durable::children::cancel_tree(&opened.harness, ROOT_CONVERSATION_ID, cx())
        .await
        .unwrap();
    opened
        .harness
        .wait_for_task(TaskId::<Value>::from_number(left.task_id), cx())
        .await
        .unwrap();
    let row = row_of(&opened.harness, left.task_id).await.unwrap();
    let node =
        crate::durable::children::tree::read_local(&opened.harness, ROOT_CONVERSATION_ID, cx())
            .await
            .unwrap()
            .and_then(|local| {
                local
                    .crown()
                    .tree
                    .at(&[eukhe_bend::rules::agent_tree::Dir::Left])
                    .map(|node| (node.info().status, node.info().patch.clone()))
            });
    let not_run = || CheckRun::NotRun {
        error: "an abort stopped the checks after the integration".to_owned(),
    };
    assert_eq!(
        (
            row.status,
            row.handback,
            row.patch,
            node,
            lock(&host.state).closes.clone(),
        ),
        (
            ChildStatus::Done,
            Some(HandbackOutcome::Done {
                handback: Box::new(RlmChildHandback {
                    child_check: not_run(),
                    parent_check: not_run(),
                    ..handback
                }),
            }),
            None,
            Some((
                eukhe_bend::rules::agent_tree::Status::Finished,
                vec![None, Some(1), None]
            )),
            vec![RlmChildHandbackRequest {
                session_id: left.session_id.clone(),
                rlm_child_id: left.rlm_child_id.clone(),
                units: vec![String::new(), "a".to_owned(), "b".to_owned()],
                scope: vec![false, true, false],
            }],
        )
    );
    opened.root.wait_for_idle(cx()).await.unwrap();
    opened.harness.close(cx()).await.unwrap();
}
