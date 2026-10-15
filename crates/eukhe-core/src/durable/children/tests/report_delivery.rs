//! A child's task prompt and report delivery around a busy spawning call:
//! a call that spawns and then waits on the child sees it run, and a
//! queued report an abort withdraws is delivered again, once.

use super::super::notice::ChildReport;
use super::super::task::ChildCheckpoint;
use super::*;

/// The `spawn_collect_hold` tool's shared state: what its `rlm.collect`
/// returned, and the gate that ends its call.
#[derive(Default)]
pub(super) struct HeldSpawn {
    collected: Mutex<Option<Value>>,
    gate: tokio::sync::Notify,
}

/// A tool whose single call spawns a child, waits for it to settle
/// (`rlm.collect` with a timeout, as one kernel cell does), records the
/// result, then holds the parent's turn until the gate opens or the call
/// is aborted.
pub(super) fn spawn_collect_hold_tool(
    requests: HostRequestRegistry,
    held: Arc<HeldSpawn>,
) -> Arc<Extension> {
    let parameters: TSchema = Type::object(Vec::<(String, TSchema)>::new());
    let tool = define_tool(ToolRegistration::new(
        "spawn_collect_hold",
        "Spawn one RLM child, wait for it, then hold",
        parameters,
        move |_args, api, cx| {
            let spawn = requests.get("rlm.run").expect("rlm.run is registered");
            let collect = requests.get("rlm.collect").expect("rlm.collect");
            let held = Arc::clone(&held);
            async move {
                let call = |data: Value| HostCall {
                    data,
                    cell_source_code: None,
                    call: Some(api.clone()),
                };
                let handle = spawn(call(json!({ "prompt": PROMPT }))).await.unwrap();
                let target = handle["rlm_child_id"].clone();
                let collected = collect(call(json!({ "targets": [target], "timeout_ms": 30_000 })))
                    .await
                    .unwrap();
                *lock(&held.collected) = Some(collected);
                let aborted = async {
                    match cx.abort_signal() {
                        Some(signal) => {
                            signal.cancelled().await;
                        }
                        None => std::future::pending().await,
                    }
                };
                tokio::select! {
                    () = held.gate.notified() => {}
                    () = aborted => {}
                }
                Ok(ToolExecutionResult::default())
            }
        },
    ));
    define_extension(Extension {
        tools: vec![tool],
        ..Extension::named("test.spawn_collect_hold")
    })
}

/// Submit `text` as a user input to the root conversation.
async fn submit_input(opened: &Opened, text: &str) {
    opened
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
}

fn call_spawn_collect_hold() -> FauxResponseStep {
    FauxResponseStep::Message(Box::new(faux_assistant_message(
        faux_tool_call("spawn_collect_hold", JsonObject::new(), None),
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::ToolUse),
            ..FauxAssistantMessageOptions::default()
        },
    )))
}

/// Wait until the held call's `rlm.collect` returned; the child's row.
async fn spawned_and_collected(opened: &Opened, host: &FakeHost) -> ChildRow {
    // The task prompt goes out while the spawning call still runs (the
    // regression: it waited for that call, so the call's own wait on the
    // child could never see it run).
    eventually(|| async { !host.prompt_keys().is_empty() }).await;
    let row = read_children(&opened.harness, ROOT_CONVERSATION_ID, cx())
        .await
        .unwrap()
        .children
        .values()
        .last()
        .cloned()
        .expect("the spawn admitted a child");
    host.settle(
        &row.session_id,
        RlmChildRunState::Answered {
            answer_preview: Some("found it".to_owned()),
        },
        None,
    );
    eventually(|| async { lock(&opened.held.collected).is_some() }).await;
    let collected = lock(&opened.held.collected).clone().unwrap();
    assert_eq!(collected["results"][0]["status"], "done", "{collected}");
    assert_eq!(collected["results"][0]["settled"], true, "{collected}");
    row
}

/// One kernel call that spawns a child and then waits for it sees the
/// child run and settle, and the report reaches the parent once.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_call_that_spawns_then_waits_sees_the_child_settle() {
    let setup = setup();
    let host = FakeHost::new();
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    setup.faux.append_responses(vec![
        call_spawn_collect_hold(),
        answer("held"),
        answer("noted"),
    ]);
    submit_input(&opened, "go").await;
    let row = spawned_and_collected(&opened, &host).await;
    opened.held.gate.notify_one();
    let task = TaskId::<Value>::from_number(row.task_id);
    opened.harness.wait_for_task(task, cx()).await.unwrap();
    opened.root.wait_for_idle(cx()).await.unwrap();
    assert_eq!(
        user_texts(&opened.root, "[child-exited").await,
        [format!(
            "[child-exited: no-reply child:{}]\n\nLast assistant text: found it",
            row.session_name
        )]
    );
    opened.harness.close(cx()).await.unwrap();
}

/// A report queued behind a busy parent turn that an abort withdraws (the
/// worker's close for a daemon shutdown aborts the conversation) is
/// submitted again under the next request id and reaches the parent once.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_withdrawn_report_is_delivered_again_once() {
    let setup = setup();
    let host = FakeHost::new();
    let storage = Arc::new(MemoryStorage::new());
    let opened = open(
        Arc::clone(&storage) as Arc<dyn Storage>,
        &setup,
        Arc::clone(&host),
    )
    .await;
    setup.faux.append_responses(vec![call_spawn_collect_hold()]);
    submit_input(&opened, "go").await;
    let row = spawned_and_collected(&opened, &host).await;
    let task = TaskId::from_number(row.task_id);
    let submission = |ordinal| {
        let storage = Arc::clone(&storage);
        async move {
            storage
                .submission_by_request(
                    ROOT_CONVERSATION_ID,
                    &report_request_id(task, ordinal),
                    cx(),
                )
                .await
                .unwrap()
        }
    };
    eventually(|| async { submission(1).await.is_some() }).await;

    // The abort withdraws the queued report.
    setup.faux.append_responses(vec![answer("noted")]);
    opened
        .root
        .abort(ConversationAbortOptions::default(), cx())
        .await
        .unwrap();
    let withdrawn = submission(1).await.unwrap();
    assert_eq!(withdrawn.state.status(), SubmissionStatus::Unanswered);
    assert_eq!(withdrawn.state.entry(), None);

    opened
        .harness
        .wait_for_task(TaskId::<Value>::from_number(row.task_id), cx())
        .await
        .unwrap();
    opened.root.wait_for_idle(cx()).await.unwrap();
    assert_eq!(
        submission(2).await.unwrap().state.status(),
        SubmissionStatus::Done
    );
    assert_eq!(
        user_texts(&opened.root, "[child-exited").await,
        [format!(
            "[child-exited: no-reply child:{}]\n\nLast assistant text: found it",
            row.session_name
        )]
    );
    assert!(lock(&setup.reports).is_empty());
    opened.harness.close(cx()).await.unwrap();
}

/// Checkpoints stored before these changes still decode: a `prompt`
/// checkpoint's dropped `waited` flag is ignored, and a `report` one
/// without `withdrawn` has had none withdrawn.
#[test]
fn checkpoints_stored_before_report_redelivery_decode() {
    let prompt: ChildCheckpoint =
        serde_json::from_value(json!({ "phase": "prompt", "waited": true })).unwrap();
    assert_eq!(prompt, ChildCheckpoint::Prompt);
    let report = ChildCheckpoint::Report {
        report: ChildReport::Cancelled {
            session_name: "kid".to_owned(),
            reason: None,
        },
        withdrawn: 0,
    };
    let mut stored = serde_json::to_value(&report).unwrap();
    stored.as_object_mut().unwrap().remove("withdrawn");
    assert_eq!(
        serde_json::from_value::<ChildCheckpoint>(stored).unwrap(),
        report
    );
}
