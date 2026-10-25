//! Main's worker tools: the first `worker_assign` creates the worker with
//! the user's words verbatim; a later one re-tasks the settled worker
//! under a new task (its own prompt key, report ids and watch), carrying
//! only the messages since the last hand-over. Images and file references
//! go along with the words they came with.

use eukhe_types::pi_ai::ImageContent;

use super::*;
use crate::durable::children::host::ChildMessageKind;

fn call_tool(name: &str) -> FauxResponseStep {
    call_tool_with(name, JsonObject::new())
}

fn call_tool_with(name: &str, arguments: JsonObject) -> FauxResponseStep {
    FauxResponseStep::Message(Box::new(faux_assistant_message(
        faux_tool_call(name, arguments, None),
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::ToolUse),
            ..FauxAssistantMessageOptions::default()
        },
    )))
}

async fn say(opened: &Opened, text: &str) {
    say_content(opened, UserContent::Text(text.to_owned())).await;
}

async fn say_content(opened: &Opened, content: UserContent) {
    let submission = opened
        .root
        .submit(
            InputSubmissionDraft {
                request_id: None,
                content,
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

fn image(data: &str, mime_type: &str) -> ImageContent {
    ImageContent {
        data: data.to_owned(),
        mime_type: mime_type.to_owned(),
    }
}

/// The user's text block, then its images, as a prompt with pasted images
/// arrives.
fn words_with(text: &str, images: &[ImageContent]) -> UserContent {
    let mut blocks = vec![UserContentBlock::Text(TextContent::new(text.to_owned()))];
    blocks.extend(images.iter().cloned().map(UserContentBlock::Image));
    UserContent::Blocks(blocks)
}

/// What the worker was handed: (prompt, images), in order.
fn handed(host: &FakeHost) -> Vec<(String, Vec<ImageContent>)> {
    lock(&host.state)
        .prompts
        .iter()
        .map(|prompt| (prompt.prompt.clone(), prompt.images.clone()))
        .collect()
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_hand_over_carries_the_users_images_and_file_references_once_in_order() {
    let setup = setup();
    let host = FakeHost::new();
    let opened = open(
        Arc::new(MemoryStorage::new()) as Arc<dyn Storage>,
        &setup,
        Arc::clone(&host),
    )
    .await;
    let (first, second, third) = (
        image("Zmlyc3Q=", "image/png"),
        image("c2Vjb25k", "image/jpeg"),
        image("dGhpcmQ=", "image/png"),
    );

    // The first task: one message with a file reference and an image (the
    // task's prompt reads the image back from main's transcript).
    setup
        .faux
        .append_responses(vec![call_tool("worker_assign"), answer("handed")]);
    say_content(
        &opened,
        words_with("fix @src/lib.rs like  this", std::slice::from_ref(&first)),
    )
    .await;
    eventually(|| async { handed(&host).len() == 1 }).await;

    // The running work gets two more images and a second reference as
    // context: only the new message's, in their order.
    let mut context = JsonObject::new();
    context.insert("kind".to_owned(), json!("context"));
    setup.faux.append_responses(vec![
        call_tool_with("worker_forward", context),
        answer("sent"),
    ]);
    say_content(
        &opened,
        words_with("and @docs/a.md:3-9 too", &[second.clone(), third.clone()]),
    )
    .await;
    eventually(|| async { handed(&host).len() == 2 }).await;
    assert_eq!(
        handed(&host),
        vec![
            (
                "fix @src/lib.rs like  this\n[image: image/png]".to_owned(),
                vec![first],
            ),
            (
                "and @docs/a.md:3-9 too\n[image: image/jpeg]\n[image: image/png]".to_owned(),
                vec![second, third],
            ),
        ]
    );
    opened.harness.close(cx()).await.unwrap();
}

/// `/goal` and `/autonomous` typed on main run on its worker, as typed;
/// before main has a worker there is none to run them on.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn main_directors_run_on_the_worker() {
    use crate::durable::children::worker_session_command;
    let setup = setup();
    let host = FakeHost::new();
    let opened = open(
        Arc::new(MemoryStorage::new()) as Arc<dyn Storage>,
        &setup,
        Arc::clone(&host),
    )
    .await;
    let before = worker_session_command(
        &opened.harness,
        host.as_ref(),
        ROOT_CONVERSATION_ID,
        "/goal ship it",
        cx(),
    )
    .await
    .unwrap();
    assert_eq!(before, None);

    setup
        .faux
        .append_responses(vec![call_tool("worker_assign"), answer("handed")]);
    say(&opened, "build it").await;
    let worker = read_children(&opened.harness, ROOT_CONVERSATION_ID, cx())
        .await
        .unwrap()
        .children
        .values()
        .last()
        .cloned()
        .expect("the worker");
    for text in ["/goal ship it", "/autonomous on"] {
        let ran = worker_session_command(
            &opened.harness,
            host.as_ref(),
            ROOT_CONVERSATION_ID,
            text,
            cx(),
        )
        .await
        .unwrap();
        assert_eq!(ran.as_deref(), Some("worker"));
    }
    assert_eq!(
        lock(&host.state).commands,
        ["/goal ship it", "/autonomous on"]
            .map(|text| RlmChildCommandRequest {
                session_id: worker.session_id.clone(),
                text: text.to_owned(),
            })
            .to_vec()
    );
    opened.harness.close(cx()).await.unwrap();
}
