//! Isolated child workspaces: the `workspace` spawn kwarg, and the
//! hand-back an ended child's report and registry row carry.

use super::*;
use crate::durable::children::registry::HandbackOutcome;

/// `rlm.spawn` takes `workspace="shared"|"isolated"` only.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn an_unknown_workspace_is_rejected() {
    let setup = setup();
    let host = FakeHost::new();
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    let error = handle(
        &opened,
        "rlm.run",
        json!({ "prompt": PROMPT, "kwargs": { "workspace": "elsewhere" } }),
    )
    .await
    .unwrap_err();
    assert_eq!(
        error.to_string(),
        "rlm.spawn workspace must be \"shared\" or \"isolated\""
    );
    assert_eq!(host.spawn_keys(), Vec::<String>::new());
    opened.harness.close(cx()).await.unwrap();
}

/// An isolated child that ends without a reply hands its workspace back:
/// the no-reply report names the taken paths and the conflicts, and the
/// registry row and `rlm.collect` keep the outcome.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn an_ended_child_reports_its_workspace_hand_back() {
    let setup = setup();
    let host = FakeHost::new();
    let handback = Handback {
        taken: vec!["a.txt".to_owned()],
        conflicts: vec!["c.txt".to_owned()],
        kept: Some("/workspaces/kept".to_owned()),
    };
    lock(&host.state).handback = Some(handback.clone());
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    let row = spawn_child(&opened, &setup).await;
    eventually(|| async { !host.prompt_keys().is_empty() }).await;
    let row = row_of(&opened.harness, row.task_id).await.unwrap();

    setup.faux.append_responses(vec![answer("noted")]);
    host.settle(
        &row.session_id,
        RlmChildRunState::Answered {
            answer_preview: Some("done".to_owned()),
        },
        None,
    );
    opened
        .harness
        .wait_for_task(TaskId::<Value>::from_number(row.task_id), cx())
        .await
        .unwrap();
    opened.root.wait_for_idle(cx()).await.unwrap();

    let outcome = HandbackOutcome::Done {
        handback: handback.clone(),
    };
    assert_eq!(
        row_of(&opened.harness, row.task_id).await.unwrap(),
        ChildRow {
            status: ChildStatus::Done,
            answer_preview: Some("done".to_owned()),
            settled: true,
            handback: Some(outcome.clone()),
            ..row.clone()
        }
    );
    assert_eq!(
        user_texts(&opened.root, "[child-exited").await,
        [format!(
            "[child-exited: no-reply child:{}]\n\nLast assistant text: done\n\n{}",
            row.session_name,
            handback.text()
        )]
    );
    let collected = handle(&opened, "rlm.collect", json!({})).await.unwrap();
    assert_eq!(
        collected["results"][0]["handback"],
        Value::from(outcome.text())
    );
    opened.harness.close(cx()).await.unwrap();
}
