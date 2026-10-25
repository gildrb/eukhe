//! Main's worker tools: the first `worker_assign` creates the worker with
//! the user's words verbatim; a later one re-tasks the settled worker
//! under a new task (its own prompt key, report ids and watch), carrying
//! only the messages since the last hand-over.

use super::*;
use crate::durable::children::host::ChildMessageKind;

fn call_tool(name: &str) -> FauxResponseStep {
    FauxResponseStep::Message(Box::new(faux_assistant_message(
        faux_tool_call(name, JsonObject::new(), None),
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::ToolUse),
            ..FauxAssistantMessageOptions::default()
        },
    )))
}

async fn say(opened: &Opened, text: &str) {
    let submission = opened
        .root
        .submit(
            InputSubmissionDraft {
                request_id: None,
                content: UserContent::Text(text.to_owned()),
                when_busy: None,
                origin: eukhe_types::input_origin::InputOrigin::User,
                entry: None,
            },
            cx(),
        )
        .await
        .unwrap();
    submission.wait(cx()).await.unwrap();
}

/// What the host was asked to prompt: (key, prompt, kind, row id).
fn prompts(host: &FakeHost) -> Vec<(String, String, ChildMessageKind, String)> {
    lock(&host.state)
        .prompts
        .iter()
        .map(|prompt| {
            (
                prompt.idempotency_key.clone(),
                prompt.prompt.clone(),
                prompt.kind,
                prompt.row_id.clone(),
            )
        })
        .collect()
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn assign_creates_then_re_tasks_the_worker_with_the_users_words_once() {
    let setup = setup();
    let host = FakeHost::new();
    let storage = Arc::new(MemoryStorage::new());
    let opened = open(
        Arc::clone(&storage) as Arc<dyn Storage>,
        &setup,
        Arc::clone(&host),
    )
    .await;

    setup
        .faux
        .append_responses(vec![call_tool("worker_assign"), answer("handed")]);
    say(&opened, "build  the thing\nexactly so").await;
    let first = read_children(&opened.harness, ROOT_CONVERSATION_ID, cx())
        .await
        .unwrap()
        .children
        .values()
        .last()
        .cloned()
        .expect("the worker");
    assert_eq!(
        (first.session_name.as_str(), first.worker),
        ("worker", true)
    );
    assert!(lock(&host.state).spawns[0].worker);
    eventually(|| async { !prompts(&host).is_empty() }).await;

    // The worker's task ends; its report reaches main.
    setup.faux.append_responses(vec![answer("noted")]);
    host.settle(
        &first.session_id,
        RlmChildRunState::Answered {
            answer_preview: Some("built".to_owned()),
        },
        None,
    );
    eventually(|| async {
        row_of(&opened.harness, first.task_id)
            .await
            .is_some_and(|row| row.settled)
    })
    .await;
    opened.root.wait_for_idle(cx()).await.unwrap();

    // A second task: only the new message goes, under a new task.
    host.settle(&first.session_id, RlmChildRunState::Running, None);
    setup
        .faux
        .append_responses(vec![call_tool("worker_assign"), answer("handed again")]);
    say(&opened, "now the docs").await;
    let row = row_of(&opened.harness, first.task_id).await.unwrap();
    let second = row.task.expect("the re-task's task");
    assert_ne!(second, first.task_id);
    assert_eq!(
        (row.status, row.settled, row.worker),
        (ChildStatus::Running, false, true)
    );
    eventually(|| async { prompts(&host).len() == 2 }).await;
    assert_eq!(
        prompts(&host),
        vec![
            (
                format!("rlm:{}:prompt", first.task_id),
                "build  the thing\nexactly so".to_owned(),
                ChildMessageKind::Task,
                format!("spawn:{}", first.rlm_child_id),
            ),
            (
                format!("rlm:{second}:prompt"),
                "now the docs".to_owned(),
                ChildMessageKind::Task,
                format!("task:{second}"),
            ),
        ]
    );

    // The re-task reports under its own request ids.
    setup.faux.append_responses(vec![answer("noted again")]);
    host.settle(
        &first.session_id,
        RlmChildRunState::Answered {
            answer_preview: Some("documented".to_owned()),
        },
        None,
    );
    opened
        .harness
        .wait_for_task(TaskId::<Value>::from_number(second), cx())
        .await
        .unwrap();
    opened.root.wait_for_idle(cx()).await.unwrap();
    let reported = user_texts(&opened.root, "").await;
    assert!(
        reported.iter().any(|text| text.contains("documented")),
        "{reported:?}"
    );
    assert!(
        storage
            .submission_by_request(
                ROOT_CONVERSATION_ID,
                &report_request_id(TaskId::from_number(second), 1),
                cx(),
            )
            .await
            .unwrap()
            .is_some(),
        "the re-task's report goes under its own task id"
    );
    opened.harness.close(cx()).await.unwrap();
}
