//! Silent children (a dynamic workflow's agents): the `label`, `phase`,
//! and `report` spawn kwargs; a silent child settles its row with its full
//! answer and posts nothing to the parent's inbox.

use super::*;

/// A silent child keeps its label, phase, and full answer on its row, and
/// its task ends without a report.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_silent_child_settles_its_row_without_a_report() {
    let setup = setup();
    let host = FakeHost::new();
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    let reply = spawn_batch_turn(
        &opened,
        &setup,
        json!([{
            "prompt": PROMPT,
            "kwargs": { "label": "scan api", "phase": "Scan", "report": "silent" }
        }]),
    )
    .await;
    assert!(reply.contains("handles"), "{reply}");
    let row = read_children(&opened.harness, ROOT_CONVERSATION_ID, cx())
        .await
        .unwrap()
        .children
        .values()
        .last()
        .cloned()
        .expect("the spawn admitted a child");
    eventually(|| async { !host.prompt_keys().is_empty() }).await;
    let row = row_of(&opened.harness, row.task_id).await.unwrap();
    lock(&host.state)
        .answers
        .insert(row.session_id.clone(), "the full answer".to_owned());
    host.settle(
        &row.session_id,
        RlmChildRunState::Answered {
            answer_preview: Some("the full…".to_owned()),
        },
        None,
    );
    opened
        .harness
        .wait_for_task(TaskId::<Value>::from_number(row.task_id), cx())
        .await
        .unwrap();
    opened.root.wait_for_idle(cx()).await.unwrap();
    assert_eq!(
        row_of(&opened.harness, row.task_id).await.unwrap(),
        ChildRow {
            label: "scan api".to_owned(),
            phase: Some("Scan".to_owned()),
            status: ChildStatus::Done,
            answer_preview: Some("the full…".to_owned()),
            answer: Some("the full answer".to_owned()),
            settled: true,
            ..row.clone()
        }
    );
    assert_eq!(
        user_texts(&opened.root, "[child-exited").await,
        Vec::<String>::new()
    );
    let answer = handle(&opened, "rlm.answer", json!({ "target": row.rlm_child_id }))
        .await
        .unwrap();
    assert_eq!(
        answer,
        json!({
            "status": "done",
            "settled": true,
            "sessionId": row.session_id,
            "answer": "the full answer",
            "error": null,
            "failure": null,
        })
    );
    opened.harness.close(cx()).await.unwrap();
}

/// A silent child whose run failed settles as an error, also without a
/// report.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_failed_silent_child_posts_no_report() {
    let setup = setup();
    let host = FakeHost::new();
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    spawn_batch_turn(
        &opened,
        &setup,
        json!([{ "prompt": PROMPT, "kwargs": { "report": "silent" } }]),
    )
    .await;
    let row = read_children(&opened.harness, ROOT_CONVERSATION_ID, cx())
        .await
        .unwrap()
        .children
        .values()
        .last()
        .cloned()
        .expect("the spawn admitted a child");
    eventually(|| async { !host.prompt_keys().is_empty() }).await;
    host.settle(
        &row.session_id,
        RlmChildRunState::Failed {
            failure: eukhe_types::input_origin::ChildFailure::Aborted,
            error: "boom".to_owned(),
        },
        None,
    );
    opened
        .harness
        .wait_for_task(TaskId::<Value>::from_number(row.task_id), cx())
        .await
        .unwrap();
    opened.root.wait_for_idle(cx()).await.unwrap();
    let settled = row_of(&opened.harness, row.task_id).await.unwrap();
    assert_eq!(
        (settled.status, settled.error, settled.settled),
        (ChildStatus::Error, Some("boom".to_owned()), true)
    );
    assert_eq!(
        user_texts(&opened.root, "[child-").await,
        Vec::<String>::new()
    );
    opened.harness.close(cx()).await.unwrap();
}
