//! TS `describe("owned conversations from tools and supervisors")`.

use super::*;

/// A value a tool or task handler hands back to the test.
type Slot<T> = Arc<Mutex<Option<T>>>;

fn put<T>(slot: &Slot<T>, value: T) {
    *slot.lock().unwrap_or_else(PoisonError::into_inner) = Some(value);
}

fn get<T: Clone>(slot: &Slot<T>) -> Option<T> {
    slot.lock().unwrap_or_else(PoisonError::into_inner).clone()
}

/// The TS string of a submission status.
fn status_text(status: SubmissionStatus) -> &'static str {
    match status {
        SubmissionStatus::Queued => "queued",
        SubmissionStatus::Placed => "placed",
        SubmissionStatus::Done => "done",
        SubmissionStatus::Unanswered => "unanswered",
    }
}

/// TS `{ content: [{ type: "text", text }] }`.
fn text_result(text: impl Into<String>) -> ToolExecutionResult {
    ToolExecutionResult {
        content: Some(vec![UserContentBlock::Text(TextContent::new(text.into()))]),
        ..ToolExecutionResult::default()
    }
}

/// The faux model every child conversation is configured with.
fn faux_model() -> AgentChange {
    AgentChange {
        model: FieldChange::Set(ModelRef {
            provider: "faux".to_owned(),
            model_id: "faux-1".to_owned(),
        }),
        ..AgentChange::default()
    }
}

fn tool_use() -> FauxAssistantMessageOptions {
    FauxAssistantMessageOptions {
        stop_reason: Some(StopReason::ToolUse),
        ..FauxAssistantMessageOptions::default()
    }
}

fn call(name: &str, arguments: serde_json::Value, id: &str) -> AssistantContentBlock {
    let serde_json::Value::Object(arguments) = arguments else {
        panic!("tool arguments are an object");
    };
    faux_tool_call(name, arguments, Some(id.to_owned()))
}

/// TS `fauxAssistantMessage([fauxToolCall(name, arguments, { id })], { stopReason: "toolUse" })`.
fn call_message(name: &str, arguments: serde_json::Value, id: &str) -> AssistantMessage {
    faux_assistant_message(vec![call(name, arguments, id)], tool_use())
}

fn text_message(text: &str) -> AssistantMessage {
    faux_assistant_message(
        vec![faux_text(text)],
        FauxAssistantMessageOptions::default(),
    )
}

/// The error of a rejected operation whose value is not `Debug`.
fn rejection<T>(result: SessionResult<T>) -> SessionError {
    match result {
        Ok(_) => panic!("expected a rejection"),
        Err(error) => error,
    }
}

/// `pi.user` entries of a conversation.
async fn user_entries(conversation: &Conversation, limit: usize) -> usize {
    conversation
        .entries(ConversationEntryQuery::default(), limit, None, context())
        .await
        .unwrap()
        .items
        .iter()
        .filter(|entry| entry.kind == "pi.user")
        .count()
}

/// Create a conversation owned by the calling tool task, configured with
/// the faux model when `configured`.
async fn create_owned_child(
    tx: Tx,
    task_id: TaskId,
    configured: bool,
) -> SessionResult<ConversationId> {
    let created = tx
        .create_conversation(ConversationOwnership::Task { task_id })
        .await?;
    if configured {
        configure(&tx, created.id, &faux_model()).await?;
    }
    Ok(created.id)
}

fn children_initial() -> JsonValue {
    json("{}")
}

/// TS `Children`: the supervisor's child conversation, per parent.
const CHILDREN_DOC: ConversationDoc<JsonValue> = match ConversationDoc::define(
    DocDefinition {
        kind: "test.children",
        version: 1,
        initial: children_initial,
        migrate: None,
        checkpoint_when: None,
    },
    LatestFork::Initial,
) {
    Ok(token) => token,
    Err(_) => panic!("valid definition"),
};

/// Input of the supervisor task (TS `{ parent: ConversationId }`).
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
struct SupervisorInput {
    parent: ConversationId,
}

/// TS `{ phase: "run" }`.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(tag = "phase", rename_all = "lowercase")]
enum SupervisorStep {
    Run,
}

/// Result of the supervisor task (TS `{ answer: EntryId }`).
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
struct SupervisorResult {
    answer: EntryId,
}

fn supervisor_task() -> Task<SupervisorInput, SupervisorStep, SupervisorResult, ()> {
    define_task(
        TaskDefinition::<SupervisorInput, SupervisorStep, SupervisorResult, ()>::new(
            "test.supervisor",
            1,
            |_: &SupervisorInput| Ok(SupervisorStep::Run),
            |_task, runtime, cx| async move {
                runtime
                    .commit(
                        |_tx, _current| async {
                            Ok(Some(NextTaskState::Terminal {
                                outcome: TaskOutcome::Aborted {
                                    reason: None,
                                    result: None,
                                },
                            }))
                        },
                        &cx,
                    )
                    .await
            },
        )
        .phase("run", |task, runtime, cx| async move {
            let children = runtime
                .snapshot(&CHILDREN_DOC, task.input.parent, &cx)
                .await?
                .expect("the children document exists");
            let id: ConversationId =
                from_json(children.get("child").expect("the child is recorded"))?;
            let child = runtime
                .conversation(id, &cx)
                .await?
                .expect("the child conversation exists");
            let submission = child
                .submit(
                    InputSubmissionDraft {
                        request_id: Some("stable".to_owned()),
                        ..InputSubmissionDraft::new("work")
                    },
                    &cx,
                )
                .await?;
            let settled = submission.wait(&cx).await?;
            let SubmissionState::Input(InputSubmission::Done { answer, .. }) = &settled.state
            else {
                return Err(SessionError::error(status_text(settled.state.status())));
            };
            let answer = *answer;
            runtime
                .commit(
                    move |_tx, _current| async move {
                        Ok(Some(NextTaskState::Terminal {
                            outcome: TaskOutcome::Completed {
                                result: SupervisorResult { answer },
                            },
                        }))
                    },
                    &cx,
                )
                .await
        }),
    )
}

#[tokio::test]
#[expect(clippy::too_many_lines, reason = "one TS case, ported whole")]
async fn gives_a_tool_an_invocation_bound_handle_whose_submissions_stay_durable_after_the_call_ends(
) {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let handle: Slot<Arc<dyn ConversationHandle>> = Slot::default();
    // TS starts `missing` as a non-undefined placeholder; here `None` is that placeholder.
    let missing_is_none: Slot<bool> = Slot::default();
    let submission: Slot<Arc<dyn Submission>> = Slot::default();
    let (handle_slot, missing_slot, submission_slot) = (
        Arc::clone(&handle),
        Arc::clone(&missing_is_none),
        Arc::clone(&submission),
    );
    add_tool(
        &setup.registry,
        define_tool(ToolRegistration::new(
            "delegate",
            "Delegates",
            empty_object_schema(),
            move |_args, api, call_context| {
                let (handle_slot, missing_slot, submission_slot) = (
                    Arc::clone(&handle_slot),
                    Arc::clone(&missing_slot),
                    Arc::clone(&submission_slot),
                );
                async move {
                    let task_id = api.task_id();
                    let child = api
                        .commit(
                            move |tx| create_owned_child(tx, task_id, true),
                            &call_context,
                        )
                        .await?;
                    let missing = api
                        .conversation(ConversationId::from_number(99_999), &call_context)
                        .await?;
                    put(&missing_slot, missing.is_none());
                    let handle = api
                        .conversation(child, &call_context)
                        .await?
                        .expect("the child conversation exists");
                    put(&handle_slot, Arc::clone(&handle));
                    let submitted = handle
                        .submit(
                            InputSubmissionDraft {
                                request_id: Some("child".to_owned()),
                                ..InputSubmissionDraft::new("child task")
                            },
                            &call_context,
                        )
                        .await?;
                    put(&submission_slot, Arc::clone(&submitted));
                    let settled = submitted.wait(&call_context).await?;
                    Ok(text_result(status_text(settled.state.status())))
                }
            },
        )),
        None,
    )
    .unwrap();
    setup.faux.set_responses(vec![
        call_message("delegate", serde_json::json!({}), "c1").into(),
        text_message("child answer").into(),
        text_message("done").into(),
    ]);
    let OpenChat { harness, root } = open_chat(memory(), &setup, None).await.unwrap();
    root.submit(InputSubmissionDraft::new("go"), context())
        .await
        .unwrap()
        .wait(context())
        .await
        .unwrap();
    assert_eq!(get(&missing_is_none), Some(true));
    // The call ended: the handle and its submission reject, while the submission record remains.
    let handle = get(&handle).expect("the tool kept its handle");
    let submission = get(&submission).expect("the tool kept its submission");
    let error = rejection(
        handle
            .submit(InputSubmissionDraft::new("again"), context())
            .await,
    );
    assert!(
        error.to_string().contains("invocation has ended"),
        "{error}"
    );
    let error = handle.wait_for_idle(context()).await.unwrap_err();
    assert!(
        error.to_string().contains("invocation has ended"),
        "{error}"
    );
    let error = handle
        .abort(ConversationAbortOptions::default(), context())
        .await
        .unwrap_err();
    assert!(
        error.to_string().contains("invocation has ended"),
        "{error}"
    );
    let error = submission.wait(context()).await.unwrap_err();
    assert!(
        error.to_string().contains("invocation has ended"),
        "{error}"
    );
    // Nothing was admitted or marked after the call ended.
    let child_conversation = harness
        .conversation(handle.id(), context())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(user_entries(&child_conversation, 100).await, 1);
    let child_tasks: Vec<AnyTaskRecord> = harness
        .inspect(context())
        .await
        .unwrap()
        .tasks
        .into_iter()
        .filter(|task| task.record.conversation_id == handle.id())
        .map(|task| task.record)
        .collect();
    assert_eq!(child_tasks, Vec::<AnyTaskRecord>::new());
    assert_eq!(
        submission_record(&harness, submission.id())
            .await
            .state
            .status(),
        SubmissionStatus::Done
    );
    harness.close(context()).await.unwrap();
}

type Submitting = tokio::task::JoinHandle<SessionResult<Arc<dyn Submission>>>;

#[tokio::test]
#[expect(clippy::too_many_lines, reason = "one TS case, ported whole")]
async fn rejects_a_handle_operation_queued_on_the_line_when_the_invocation_ends_before_it_runs() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let ready: Deferred<(ConversationId, TaskId)> = deferred();
    let go: Deferred = deferred();
    let queued: Deferred = deferred();
    let submitting_slot: Arc<Mutex<Option<Submitting>>> = Arc::default();
    let (tool_ready, tool_go, tool_queued, tool_submitting) = (
        ready.clone(),
        go.clone(),
        queued.clone(),
        Arc::clone(&submitting_slot),
    );
    add_tool(
        &setup.registry,
        define_tool(ToolRegistration::new(
            "delegate",
            "Delegates late",
            empty_object_schema(),
            move |_args, api, call_context| {
                let (ready, go, queued, submitting) = (
                    tool_ready.clone(),
                    tool_go.clone(),
                    tool_queued.clone(),
                    Arc::clone(&tool_submitting),
                );
                async move {
                    let task_id = api.task_id();
                    let child = api
                        .commit(
                            move |tx| create_owned_child(tx, task_id, false),
                            &call_context,
                        )
                        .await?;
                    let handle = api
                        .conversation(child, &call_context)
                        .await?
                        .expect("the child conversation exists");
                    ready.resolve((child, task_id));
                    go.wait().await;
                    // Called while the invocation is alive, with a context that is not the call's: the handle binds it to the
                    // invocation. It reaches the line only after the abort mark.
                    let late =
                        tokio::spawn(handle.submit(InputSubmissionDraft::new("late"), context()));
                    *submitting.lock().unwrap_or_else(PoisonError::into_inner) = Some(late);
                    queued.resolve(());
                    let signal = call_context
                        .abort_signal()
                        .expect("the call carries a signal");
                    Err(aborted(&signal).await)
                }
            },
        )),
        None,
    )
    .unwrap();
    setup.faux.set_responses(vec![
        call_message("delegate", serde_json::json!({}), "c1").into()
    ]);
    let OpenChat { harness, root } = open_chat(memory(), &setup, None).await.unwrap();
    root.submit(InputSubmissionDraft::new("go"), context())
        .await
        .unwrap();
    let (child, task_id) = ready.wait().await;
    // Hold the Session line, queue the abort mark behind it, then let the tool queue its submit.
    let release: Deferred = deferred();
    let held = release.clone();
    let holding = tokio::spawn(root.commit(
        move |_tx| async move {
            held.wait().await;
            Ok(())
        },
        context(),
    ));
    let aborting = tokio::spawn(harness.abort_task(task_id, context()));
    // TS runs `abortTask` up to its line wait synchronously; let the spawned abort reach the line first.
    flush().await;
    go.resolve(());
    queued.wait().await;
    let submitting = submitting_slot
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .take()
        .expect("the tool queued its submit");
    release.resolve(());
    holding.await.unwrap().unwrap();
    aborting.await.unwrap().unwrap();
    assert!(submitting.await.unwrap().is_err());
    let child_conversation = harness
        .conversation(child, context())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(
        child_conversation
            .entries(ConversationEntryQuery::default(), 10, None, context())
            .await
            .unwrap()
            .items,
        Vec::<EntryRecord>::new()
    );
    let child_submissions: Vec<SubmissionRecord> = harness
        .inspect(context())
        .await
        .unwrap()
        .submissions
        .into_iter()
        .filter(|record| record.conversation_id == child)
        .collect();
    assert_eq!(child_submissions, Vec::<SubmissionRecord>::new());
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn aborts_a_subagent_run_with_its_parents_conversation_rejecting_the_waiting_tool() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let child: Slot<ConversationId> = Slot::default();
    let tool_wait: Deferred<String> = deferred();
    let (child_slot, waited) = (Arc::clone(&child), tool_wait.clone());
    add_tool(
        &setup.registry,
        define_tool(ToolRegistration::new(
            "delegate",
            "Delegates",
            empty_object_schema(),
            move |_args, api, call_context| {
                let (child_slot, tool_wait) = (Arc::clone(&child_slot), waited.clone());
                async move {
                    let task_id = api.task_id();
                    let child = api
                        .commit(
                            move |tx| create_owned_child(tx, task_id, true),
                            &call_context,
                        )
                        .await?;
                    put(&child_slot, child);
                    let submission = api
                        .conversation(child, &call_context)
                        .await?
                        .expect("the child conversation exists")
                        .submit(InputSubmissionDraft::new("child task"), &call_context)
                        .await?;
                    match submission.wait(&call_context).await {
                        Ok(settled) => Ok(text_result(status_text(settled.state.status()))),
                        Err(error) => {
                            tool_wait.resolve(error.to_string());
                            Err(error)
                        }
                    }
                }
            },
        )),
        None,
    )
    .unwrap();
    let Gated { step, reached } = gated(text_message("never"));
    setup.faux.set_responses(vec![
        call_message("delegate", serde_json::json!({}), "c1").into(),
        step,
    ]);
    let OpenChat { harness, root } = open_chat(memory(), &setup, None).await.unwrap();
    let input = root
        .submit(InputSubmissionDraft::new("go"), context())
        .await
        .unwrap();
    reached.wait().await;
    root.abort(ConversationAbortOptions::default(), context())
        .await
        .unwrap();
    let settled_input = input.wait(context()).await.unwrap();
    assert_eq!(settled_input.state.status(), SubmissionStatus::Unanswered);
    assert_eq!(settled_input.state.reason(), Some("aborted"));
    assert!(!tool_wait.wait().await.is_empty());
    let child = get(&child).expect("the tool created its child");
    let child_conversation = harness
        .conversation(child, context())
        .await
        .unwrap()
        .unwrap();
    child_conversation.wait_for_idle(context()).await.unwrap();
    let child_live = harness.snapshot(&LIVE_DOC, child, context()).await.unwrap();
    assert_eq!(child_live.map(JsonValue::Object), Some(json("{}")));
    let child_inputs: Vec<SubmissionRecord> = harness
        .inspect(context())
        .await
        .unwrap()
        .submissions
        .into_iter()
        .filter(|record| record.conversation_id == child)
        .collect();
    assert_eq!(child_inputs, Vec::<SubmissionRecord>::new());
    harness.wait_for_idle(context()).await.unwrap();
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn lets_a_running_tool_abort_its_owned_child_and_continue() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let Gated { step, reached } = gated(text_message("never"));
    add_tool(
        &setup.registry,
        define_tool(ToolRegistration::new(
            "delegate",
            "Delegates and cancels",
            empty_object_schema(),
            move |_args, api, call_context| {
                let reached = reached.clone();
                async move {
                    let task_id = api.task_id();
                    let child = api
                        .commit(
                            move |tx| create_owned_child(tx, task_id, true),
                            &call_context,
                        )
                        .await?;
                    let handle = api
                        .conversation(child, &call_context)
                        .await?
                        .expect("the child conversation exists");
                    let submission = handle
                        .submit(InputSubmissionDraft::new("child task"), &call_context)
                        .await?;
                    reached.wait().await;
                    handle
                        .abort(ConversationAbortOptions::default(), &call_context)
                        .await?;
                    let settled_child = submission.wait(&call_context).await?;
                    Ok(text_result(format!(
                        "child {}",
                        status_text(settled_child.state.status())
                    )))
                }
            },
        )),
        None,
    )
    .unwrap();
    setup.faux.set_responses(vec![
        call_message("delegate", serde_json::json!({}), "c1").into(),
        step,
        text_message("done").into(),
    ]);
    let OpenChat { harness, root } = open_chat(memory(), &setup, None).await.unwrap();
    let settled = root
        .submit(InputSubmissionDraft::new("go"), context())
        .await
        .unwrap()
        .wait(context())
        .await
        .unwrap();
    assert_eq!(settled.state.status(), SubmissionStatus::Done);
    harness.close(context()).await.unwrap();
}

#[tokio::test]
#[expect(clippy::too_many_lines, reason = "one TS case, ported whole")]
async fn aborts_the_children_of_a_tool_call_that_throws_or_is_interrupted_while_the_run_continues()
{
    let world = World::new();
    let (_directory, path) = sqlite_path("pi-durable-tool-children-");
    let children: Arc<Mutex<Vec<TaskId>>> = Arc::default();
    let tool_running: Deferred = deferred();
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    add_task(&setup.registry, world.hold.erase(), None).unwrap();
    let (hold, spawned, running) = (
        world.hold.clone(),
        Arc::clone(&children),
        tool_running.clone(),
    );
    add_tool(
        &setup.registry,
        define_tool(ToolRegistration::new(
            "spawn",
            "Starts owned work, then throws or hangs",
            Type::object([("mode", Type::string())]),
            move |args: PiJsonValue, api, call_context| {
                let (hold, children, tool_running) =
                    (hold.clone(), Arc::clone(&spawned), running.clone());
                async move {
                    let task_id = api.task_id();
                    let input = HoldInput::named(&format!("child.{}", api.call_id()));
                    let child = api
                        .commit(
                            move |tx| async move {
                                let created = tx
                                    .create_conversation(ConversationOwnership::Task { task_id })
                                    .await?;
                                create_task_in(&tx, &hold, &input, options(Some(created.id), None))
                                    .await
                            },
                            &call_context,
                        )
                        .await?;
                    children
                        .lock()
                        .unwrap_or_else(PoisonError::into_inner)
                        .push(child);
                    if args.get("mode").and_then(PiJsonValue::as_str) == Some("throw") {
                        return Err(SessionError::error("spawn failed"));
                    }
                    tool_running.resolve(());
                    let signal = call_context
                        .abort_signal()
                        .expect("the call carries a signal");
                    Err(aborted(&signal).await)
                }
            },
        )),
        None,
    )
    .unwrap();
    let spawn_call =
        |mode: &str, id: &str| call_message("spawn", serde_json::json!({ "mode": mode }), id);
    setup.faux.set_responses(vec![
        spawn_call("throw", "c1").into(),
        text_message("after throw").into(),
        spawn_call("hang", "c2").into(),
    ]);
    let opened = open_chat(sqlite(&path).await, &setup, None).await.unwrap();
    let first = opened
        .root
        .submit(InputSubmissionDraft::new("one"), context())
        .await
        .unwrap()
        .wait(context())
        .await
        .unwrap();
    assert_eq!(first.state.status(), SubmissionStatus::Done);
    let first_child = children.lock().unwrap_or_else(PoisonError::into_inner)[0];
    assert_eq!(
        outcome_of(&opened.harness, first_child).await,
        TaskOutcomeStatus::Aborted
    );

    // The second call hangs until the process stops; on reopen it is interrupted.
    let second = opened
        .root
        .submit(InputSubmissionDraft::new("two"), context())
        .await
        .unwrap()
        .id();
    tool_running.wait().await;
    opened.harness.close(context()).await.unwrap();
    setup
        .faux
        .set_responses(vec![text_message("after interrupt").into()]);
    let opened = open_chat(sqlite(&path).await, &setup, None).await.unwrap();
    opened.harness.resume().unwrap();
    let second_child = children.lock().unwrap_or_else(PoisonError::into_inner)[1];
    assert_eq!(
        outcome_of(&opened.harness, second_child).await,
        TaskOutcomeStatus::Aborted
    );
    let settled_second = opened
        .harness
        .submission(second, context())
        .await
        .unwrap()
        .unwrap()
        .wait(context())
        .await
        .unwrap();
    assert_eq!(settled_second.state.status(), SubmissionStatus::Done);
    let tools = opened
        .harness
        .commit(
            |tx| async move {
                tx.scan_tasks(
                    TaskQuery {
                        kind: Some("pi.tool".to_owned()),
                        ..TaskQuery::default()
                    },
                    10,
                    None,
                )
                .await
            },
            context(),
        )
        .await
        .unwrap()
        .items;
    let outcomes: Vec<Option<TaskOutcomeStatus>> = tools
        .iter()
        .map(|task| match &task.state {
            TaskState::Terminal { outcome } => Some(outcome.status()),
            TaskState::Pending { .. }
            | TaskState::Running { .. }
            | TaskState::Waiting { .. }
            | TaskState::Completing { .. } => None,
        })
        .collect();
    assert_eq!(
        outcomes,
        vec![
            Some(TaskOutcomeStatus::Failed),
            Some(TaskOutcomeStatus::Failed)
        ]
    );
    opened.harness.close(context()).await.unwrap();
}

#[tokio::test]
#[expect(clippy::too_many_lines, reason = "one TS case, ported whole")]
async fn reruns_a_replay_safe_subagent_tool_after_a_restart_with_the_same_child_and_submission() {
    let (_directory, path) = sqlite_path("pi-durable-safe-subagent-");
    let children: Arc<Mutex<Vec<ConversationId>>> = Arc::default();
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let recorded = Arc::clone(&children);
    add_tool(
        &setup.registry,
        define_tool(ToolRegistration {
            replay: Some(ToolReplay::Safe),
            ..ToolRegistration::new(
                "subagent",
                "Delegates",
                empty_object_schema(),
                move |_args, api, call_context| {
                    let children = Arc::clone(&recorded);
                    async move {
                        let task_id = api.task_id();
                        let child = api
                            .commit(
                                move |tx| async move {
                                    let existing = tx
                                        .scan_conversations(
                                            ConversationQuery {
                                                owner_task_id: Some(task_id),
                                                ..ConversationQuery::default()
                                            },
                                            1,
                                            None,
                                        )
                                        .await?;
                                    if let Some(existing) = existing.items.first() {
                                        return Ok(existing.id);
                                    }
                                    create_owned_child(tx, task_id, true).await
                                },
                                &call_context,
                            )
                            .await?;
                        children
                            .lock()
                            .unwrap_or_else(PoisonError::into_inner)
                            .push(child);
                        let request = InputSubmissionDraft {
                            request_id: Some(format!("subagent:{task_id}")),
                            ..InputSubmissionDraft::new("child task")
                        };
                        let submission = api
                            .conversation(child, &call_context)
                            .await?
                            .expect("the child conversation exists")
                            .submit(request, &call_context)
                            .await?;
                        let settled = submission.wait(&call_context).await?;
                        Ok(text_result(status_text(settled.state.status())))
                    }
                },
            )
        }),
        None,
    )
    .unwrap();
    let Gated { step, reached } = gated(text_message("never"));
    setup.faux.set_responses(vec![
        call_message("subagent", serde_json::json!({}), "c1").into(),
        step,
    ]);
    let opened = open_chat(sqlite(&path).await, &setup, None).await.unwrap();
    let input = opened
        .root
        .submit(InputSubmissionDraft::new("go"), context())
        .await
        .unwrap()
        .id();
    reached.wait().await;
    opened.harness.close(context()).await.unwrap();

    setup.faux.set_responses(vec![
        text_message("child answer").into(),
        text_message("done").into(),
    ]);
    let opened = open_chat(sqlite(&path).await, &setup, None).await.unwrap();
    let settled = opened
        .harness
        .submission(input, context())
        .await
        .unwrap()
        .unwrap()
        .wait(context())
        .await
        .unwrap();
    assert_eq!(settled.state.status(), SubmissionStatus::Done);
    let children = children
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone();
    assert_eq!(children.len(), 2);
    assert_eq!(children[1], children[0]);
    let child = opened
        .harness
        .conversation(children[0], context())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(user_entries(&child, 100).await, 1);
    let results: Vec<bool> = opened
        .root
        .context(context())
        .await
        .unwrap()
        .messages
        .iter()
        .filter_map(|message| {
            if let Message::ToolResult(result) = message {
                Some(result.is_error)
            } else {
                None
            }
        })
        .collect();
    assert_eq!(results, vec![false]);
    opened.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn lets_a_background_supervisor_resubmit_after_a_restart_without_submitting_twice() {
    let (_directory, path) = sqlite_path("pi-durable-supervisor-");
    let supervisor_definition = supervisor_task();
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    add_task(&setup.registry, supervisor_definition.erase(), None).unwrap();
    let Gated { step, reached } = gated(text_message("never"));
    setup
        .faux
        .set_responses(vec![step, text_message("answer").into()]);
    let opened = open_chat(sqlite(&path).await, &setup, None).await.unwrap();
    let root_id = opened.root.id();
    let definition = supervisor_definition.erase();
    let (supervisor, child) = opened
        .root
        .commit(
            move |tx| async move {
                let supervisor = tx
                    .create_task(
                        definition.as_definition_ref(),
                        to_json(&SupervisorInput { parent: root_id })?,
                        options(None, Some(true)),
                    )
                    .await?;
                let created = tx
                    .create_conversation(ConversationOwnership::Task {
                        task_id: supervisor,
                    })
                    .await?;
                configure(&tx, created.id, &faux_model()).await?;
                tx.doc(&CHILDREN_DOC, root_id)
                    .await?
                    .set("child", to_json(&created.id)?)?;
                Ok((supervisor, created.id))
            },
            context(),
        )
        .await
        .unwrap();
    opened.harness.resume().unwrap();
    // The submission is admitted and its generation requested; then the process stops.
    reached.wait().await;
    opened.harness.close(context()).await.unwrap();

    let opened = open_chat(sqlite(&path).await, &setup, None).await.unwrap();
    opened.harness.resume().unwrap();
    let done = opened
        .harness
        .wait_for_task(supervisor, context())
        .await
        .unwrap();
    assert_eq!(done.outcome.status(), TaskOutcomeStatus::Completed);
    let child_conversation = opened
        .harness
        .conversation(child, context())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(user_entries(&child_conversation, 100).await, 1);
    // The root never waited for the background supervisor.
    opened.root.wait_for_idle(context()).await.unwrap();
    opened.harness.close(context()).await.unwrap();
}
