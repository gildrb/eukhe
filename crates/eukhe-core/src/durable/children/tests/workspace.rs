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
