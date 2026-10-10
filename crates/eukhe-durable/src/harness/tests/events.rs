//! Port of `test/harness-events.test.ts`.

use std::sync::{Arc, Mutex, PoisonError};
use std::time::Duration;

use eukhe_chord::context::with_cancel;
use eukhe_chord::json::{from_json, to_json, JsonValue};
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_text, faux_thinking, faux_tool_call, FauxAssistantMessageOptions,
    FauxResponseStep, FauxTokenSize, RegisterFauxProviderOptions,
};
use eukhe_pi_ai::typebox::{TSchema, Type};
use eukhe_types::pi_ai::{AssistantContentBlock, AssistantMessage, Message, StopReason};
use futures::FutureExt;

use super::chat_support::{chat_setup, open_chat, text_of, wait_for, ChatSetup, OpenChat};
use super::support::{add_tool, context, empty_object_schema};
use super::task_support::{aborted, deferred, flush, Deferred};
use crate::harness::agent::AGENT_DOC;
use crate::harness::define::define_tool;
use crate::harness::live::LIVE_DOC;
use crate::harness::types::{
    ConversationCreateOptions, InputSubmissionDraft, OutputRetain, PartialRetryPolicy,
    ToolExecutionResult, ToolOutputChunk, ToolOutputLimits, ToolRegistration, WhenBusy,
};
use crate::harness::usage::USAGE_DOC;
use crate::harness::{
    watch_events, AgentEvent, AgentEventStream, Conversation, Harness, MessageChange, PathSegment,
    SnapshotEvent, ToolEventCall, ToolOutputUpdate,
};
use crate::session::{SessionError, WatchEnd};
use crate::storage::MemoryStorage;
use crate::types::{
    CommitChange, ConversationOwnership, DocumentCommitChange, EntryDraft, Storage,
    SubmissionStatus,
};

type Batches = Arc<Mutex<Vec<Vec<AgentEvent>>>>;

fn storage() -> Arc<dyn Storage> {
    Arc::new(MemoryStorage::new())
}

fn json(text: &str) -> JsonValue {
    JsonValue::parse(text).expect("valid JSON literal")
}

fn start(stream: &AgentEventStream) -> Batches {
    let batches: Batches = Arc::default();
    let sink = Arc::clone(&batches);
    stream
        .start(Arc::new(move |events, _| {
            sink.lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(events.to_vec());
            async { Ok(()) }.boxed()
        }))
        .unwrap();
    batches
}

/// Attach and start an event stream that records every delivered batch.
async fn listen(harness: &Harness, conversation: &Conversation) -> (AgentEventStream, Batches) {
    let stream = watch_events(harness, conversation.id(), context())
        .await
        .unwrap();
    let batches = start(&stream);
    (stream, batches)
}

fn batches_of(batches: &Batches) -> Vec<Vec<AgentEvent>> {
    batches
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
}

fn events(batches: &Batches) -> Vec<AgentEvent> {
    batches_of(batches).into_iter().flatten().collect()
}

fn types(events: &[AgentEvent]) -> Vec<&'static str> {
    events.iter().map(AgentEvent::kind).collect()
}

fn slow() -> ChatSetup {
    chat_setup(RegisterFauxProviderOptions {
        tokens_per_second: Some(400.0),
        token_size: Some(FauxTokenSize {
            min: Some(1),
            max: Some(1),
        }),
        ..RegisterFauxProviderOptions::default()
    })
}

fn input(text: &str) -> InputSubmissionDraft {
    InputSubmissionDraft::new(text)
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

fn text_message(text: &str) -> AssistantMessage {
    faux_assistant_message(
        vec![faux_text(text)],
        FauxAssistantMessageOptions::default(),
    )
}

/// Faux step held until `release` or the request's abort.
fn held(release: &Deferred, message: AssistantMessage) -> FauxResponseStep {
    let release = release.clone();
    FauxResponseStep::Factory(Arc::new(move |_, options, _, _| {
        let signal = options.and_then(|options| options.stream.request.signal.clone());
        let (release, message) = (release.clone(), message.clone());
        async move {
            if let Some(signal) = signal {
                tokio::select! {
                    () = release.wait() => Ok(message),
                    reason = signal.cancelled() => Err(reason),
                }
            } else {
                release.wait().await;
                Ok(message)
            }
        }
        .boxed()
    }))
}

/// A tool definition over an async `execute`.
fn define<F, Fut>(
    name: &str,
    description: &str,
    parameters: TSchema,
    execute: F,
) -> ToolRegistration
where
    F: Fn(Arc<dyn crate::harness::types::ToolExecutionApi>, eukhe_chord::context::Context) -> Fut
        + Send
        + Sync
        + 'static,
    Fut: std::future::Future<Output = Result<ToolExecutionResult, SessionError>> + Send + 'static,
{
    ToolRegistration::new(name, description, parameters, move |_, api, cx| {
        execute(api, cx)
    })
}

fn print(api: &dyn crate::harness::types::ToolExecutionApi, text: &str) {
    api.output(ToolOutputChunk::Text(text), None).unwrap();
}

/// Rebuild the streamed text of block 0 from `message_start` and the text deltas that follow it.
fn streamed_text(events: &[AgentEvent]) -> String {
    let mut text = String::new();
    for event in events {
        match event {
            AgentEvent::MessageStart {
                message: Message::Assistant(message),
            } => {
                text = match message.content.first() {
                    Some(AssistantContentBlock::Text(block)) => block.text.clone(),
                    _ => String::new(),
                };
            }
            AgentEvent::MessageUpdate { changes, .. } => {
                for change in changes {
                    match change {
                        MessageChange::TextStart {
                            content_index: 0,
                            block: AssistantContentBlock::Text(block),
                        } => text.clone_from(&block.text),
                        MessageChange::TextDelta {
                            content_index: 0,
                            delta,
                        } => text.push_str(delta),
                        _ => {}
                    }
                }
            }
            _ => {}
        }
    }
    text
}

/// Apply message changes to a copy of `message`, as an events-only consumer would.
fn apply_changes(message: &AssistantMessage, changes: &[MessageChange]) -> AssistantMessage {
    let mut next = message.clone();
    for change in changes {
        match change {
            MessageChange::Message { message } => next = message.clone(),
            MessageChange::Block {
                content_index,
                block,
            } => next.content[*content_index] = block.clone(),
            MessageChange::TextStart {
                content_index,
                block,
            }
            | MessageChange::ThinkingStart {
                content_index,
                block,
            }
            | MessageChange::ToolcallStart {
                content_index,
                block,
            } => next.content.insert(*content_index, block.clone()),
            MessageChange::TextDelta {
                content_index,
                delta,
            } => {
                if let AssistantContentBlock::Text(block) = &mut next.content[*content_index] {
                    block.text.push_str(delta);
                }
            }
            MessageChange::ThinkingDelta {
                content_index,
                delta,
            } => {
                if let AssistantContentBlock::Thinking(block) = &mut next.content[*content_index] {
                    block.thinking.push_str(delta);
                }
            }
            MessageChange::ToolcallDelta {
                content_index,
                path,
                delta,
            } => {
                let AssistantContentBlock::ToolCall(call) = &mut next.content[*content_index]
                else {
                    panic!("toolcall_delta on a non-tool-call block");
                };
                let (last, parents) = path.split_last().unwrap();
                let mut target = serde_json::Value::Object(std::mem::take(&mut call.arguments));
                {
                    let mut cursor = &mut target;
                    for segment in parents {
                        cursor = match segment {
                            PathSegment::Key(key) => &mut cursor[key.as_str()],
                            PathSegment::Index(index) => &mut cursor[*index],
                        };
                    }
                    let slot = match last {
                        PathSegment::Key(key) => &mut cursor[key.as_str()],
                        PathSegment::Index(index) => &mut cursor[*index],
                    };
                    let joined = format!("{}{delta}", slot.as_str().unwrap_or_default());
                    *slot = serde_json::Value::String(joined);
                }
                let serde_json::Value::Object(arguments) = target else {
                    unreachable!("arguments stay an object")
                };
                call.arguments = arguments;
            }
        }
    }
    next
}

/// Committed `pi.live` values of every commit that has one.
fn live_values(harness: &Harness) -> Arc<Mutex<Vec<JsonValue>>> {
    let values: Arc<Mutex<Vec<JsonValue>>> = Arc::default();
    let sink = Arc::clone(&values);
    let subscription = harness
        .subscribe_commits(Arc::new(move |publication, _| {
            for change in &publication.changes {
                if let CommitChange::Document(DocumentCommitChange::Document {
                    record,
                    value: Some(value),
                    ..
                }) = change
                {
                    if record.kind == "pi.live" {
                        sink.lock()
                            .unwrap_or_else(PoisonError::into_inner)
                            .push(JsonValue::Object(Arc::clone(value)));
                    }
                }
            }
        }))
        .unwrap();
    drop(subscription);
    values
}

/// Committed partials of the generation, one per commit that has one.
fn partials_of(values: &Arc<Mutex<Vec<JsonValue>>>) -> Vec<AssistantMessage> {
    values
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .iter()
        .filter_map(|live| {
            live.get("generation")
                .and_then(|generation| generation.get("message"))
        })
        .map(|message| from_json(message).unwrap())
        .collect()
}

#[tokio::test]
async fn streams_a_run_as_lifecycle_events_and_text_deltas_that_rebuild_the_answer() {
    let setup = slow();
    let text = "streamed answer text ".repeat(20);
    setup.faux.set_responses(vec![text_message(&text).into()]);
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let (stream, batches) = listen(&harness, &root).await;
    let snapshot = stream.snapshot();
    assert!(snapshot.entries.is_empty() && snapshot.tools.is_empty() && snapshot.inbox.is_empty());
    let lives = live_values(&harness);
    let submission = root.submit(input("hi"), context()).await.unwrap();
    submission.wait(context()).await.unwrap();
    flush().await;
    let all = events(&batches);
    let mut deduped = types(&all);
    deduped.dedup();
    assert_eq!(
        deduped,
        [
            "message_start",
            "message_end",
            "submission",
            "run_start",
            "turn_start",
            "message_start",
            "message_update",
            "message_end",
            "turn_end",
            "run_end",
            "submission",
            "usage_changed",
        ]
    );
    assert_eq!(
        all.iter().find(|event| event.kind() == "run_start"),
        Some(&AgentEvent::RunStart {
            inputs: vec![submission.id()]
        })
    );
    // After each event, the rebuilt text equals the committed partial of that commit.
    let rebuilt: Vec<String> = all
        .iter()
        .enumerate()
        .filter(|(_, event)| {
            matches!(
                event,
                AgentEvent::MessageStart {
                    message: Message::Assistant(_)
                }
            ) || event.kind() == "message_update"
        })
        .map(|(index, _)| streamed_text(&all[..=index]))
        .collect();
    let partials: Vec<String> = partials_of(&lives)
        .into_iter()
        .map(|partial| text_of(Some(&Message::Assistant(partial))).unwrap_or_default())
        .collect();
    assert_eq!(rebuilt, partials);
    assert!(partials.len() > 1);
    let Some(AgentEvent::MessageEnd { entry }) =
        all.iter().rev().find(|event| event.kind() == "message_end")
    else {
        panic!("a message ends");
    };
    assert_eq!(
        text_of(entry.model.as_ref().and_then(|model| model.first())),
        Some(text)
    );
    stream.stop().await;
    harness.close(context()).await.unwrap();
}

#[tokio::test]
#[expect(clippy::too_many_lines, reason = "one-to-one port of the TS test")]
async fn reports_tool_start_output_appends_and_the_result_entry() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let gate: Deferred = deferred();
    let tool_gate = gate.clone();
    add_tool(
        &setup.registry,
        define_tool(define(
            "print",
            "Prints",
            Type::object([("n", Type::number())]),
            move |api, _| {
                let gate = tool_gate.clone();
                async move {
                    print(&*api, "one\n");
                    tokio::time::sleep(Duration::from_millis(150)).await;
                    print(&*api, "two\n");
                    gate.wait().await;
                    Ok(ToolExecutionResult::default())
                }
            },
        )),
        None,
    )
    .unwrap();
    setup.faux.set_responses(vec![
        faux_assistant_message(
            vec![call("print", serde_json::json!({ "n": 1 }), "c1")],
            tool_use(),
        )
        .into(),
        text_message("done").into(),
    ]);
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let (stream, batches) = listen(&harness, &root).await;
    let submission = root.submit(input("go"), context()).await.unwrap();
    // The output events rebuild the slot's retained window.
    let output = |batches: &Batches| {
        rebuild_outputs(&events(batches))
            .last()
            .cloned()
            .unwrap_or_default()
    };
    wait_for(
        || {
            let done = output(&batches) == "one\ntwo\n";
            async move { done }
        },
        5000,
    )
    .await;
    gate.resolve(());
    submission.wait(context()).await.unwrap();
    flush().await;
    let all = events(&batches);
    let tool: Vec<&AgentEvent> = all
        .iter()
        .filter(|event| event.kind().starts_with("tool_execution"))
        .collect();
    let AgentEvent::ToolExecutionStart { call, args } = tool[0] else {
        panic!("the tool starts first: {:?}", tool[0]);
    };
    assert!(call.task_id.is_some(), "a started call has its tool task");
    assert_eq!(
        (call, args),
        (
            &ToolEventCall {
                task_id: call.task_id,
                tool_call_id: "c1".to_owned(),
                tool_name: "print".to_owned(),
                parent_tool_call_id: None,
                parent_task_id: None,
            },
            &json(r#"{"n":1}"#)
        )
    );
    let end = *tool.last().unwrap();
    let AgentEvent::ToolExecutionEnd {
        call,
        entry: Some(entry),
        ..
    } = end
    else {
        panic!("the tool ends with its entry: {end:?}");
    };
    assert_eq!(
        (call.tool_call_id.as_str(), entry.kind.as_str()),
        ("c1", "pi.tool-result")
    );
    // As in the coding agent, the tool ends directly before its result message.
    let end_index = all.iter().position(|event| event == end).unwrap();
    assert_eq!(
        types(&all[end_index..end_index + 3]),
        ["tool_execution_end", "message_start", "message_end"]
    );
    assert!(matches!(
        &all[end_index + 1],
        AgentEvent::MessageStart { message: Message::ToolResult(result) } if result.tool_call_id == "c1"
    ));
    // Two turns: the tool round, and the answer.
    assert_eq!(
        types(&all)
            .iter()
            .filter(|kind| **kind == "turn_start")
            .count(),
        2
    );
    assert_eq!(
        types(&all)
            .iter()
            .filter(|kind| **kind == "turn_end")
            .count(),
        2
    );
    stream.stop().await;
    harness.close(context()).await.unwrap();
}

/// The retained window after each output update.
fn rebuild_outputs(events: &[AgentEvent]) -> Vec<String> {
    let mut rebuilt = Vec::new();
    let mut text = String::new();
    for event in events {
        let AgentEvent::ToolExecutionUpdate {
            output: Some(output),
            ..
        } = event
        else {
            continue;
        };
        match output {
            ToolOutputUpdate::Set { set } => text.clone_from(set),
            ToolOutputUpdate::Window { trim_start, append } => {
                text = format!(
                    "{}{}",
                    eukhe_chord::json::utf16_skip(&text, trim_start.unwrap_or(0)),
                    append.as_deref().unwrap_or_default()
                );
            }
        }
        rebuilt.push(text.clone());
    }
    rebuilt
}

#[tokio::test]
async fn reports_queued_submissions_inbox_changes_and_retries() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let release: Deferred = deferred();
    let error = faux_assistant_message(
        Vec::<AssistantContentBlock>::new(),
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::Error),
            error_message: Some("503 Service Unavailable".to_owned()),
            ..FauxAssistantMessageOptions::default()
        },
    );
    setup.faux.set_responses(vec![
        held(&release, text_message("first")),
        error.into(),
        text_message("second").into(),
    ]);
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    setup.settings.update(|settings| {
        settings.retry = Some(PartialRetryPolicy {
            enabled: Some(true),
            max_retries: Some(1),
            base_delay_ms: Some(1.0),
            ..PartialRetryPolicy::default()
        });
    });
    let (stream, batches) = listen(&harness, &root).await;
    root.submit(input("a"), context()).await.unwrap();
    let follow_up = root.submit(input("f"), context()).await.unwrap();
    flush().await;
    let inbox: Vec<JsonValue> = events(&batches)
        .iter()
        .filter(|event| event.kind() == "inbox_update")
        .map(|event| to_json(event).unwrap())
        .collect();
    assert_eq!(
        inbox,
        [json(&format!(
            r#"{{"type":"inbox_update","items":[{{"id":{},"mode":"followUp"}}]}}"#,
            follow_up.id()
        ))]
    );
    release.resolve(());
    follow_up.wait(context()).await.unwrap();
    flush().await;
    let all = events(&batches);
    let kinds = types(&all);
    assert!(kinds.contains(&"auto_retry_start"));
    assert!(kinds.contains(&"auto_retry_end"));
    assert_eq!(kinds.iter().filter(|kind| **kind == "run_start").count(), 2);
    let statuses: Vec<SubmissionStatus> = all
        .iter()
        .filter_map(|event| match event {
            AgentEvent::Submission { record } => Some(record.state.status()),
            _ => None,
        })
        .collect();
    assert_eq!(
        statuses,
        [
            SubmissionStatus::Placed,
            SubmissionStatus::Queued,
            SubmissionStatus::Done,
            SubmissionStatus::Placed,
            SubmissionStatus::Done
        ]
    );
    stream.stop().await;
    harness.close(context()).await.unwrap();
}

async fn note(conversation: &Conversation, kind: &'static str) {
    let id = conversation.id();
    conversation
        .commit(
            move |tx| async move { tx.append_entry(id, EntryDraft::new(kind)).await },
            context(),
        )
        .await
        .unwrap();
}

#[tokio::test]
async fn replaces_undelivered_batches_with_one_snapshot_after_100_pending_batches() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let stream = watch_events(&harness, root.id(), context()).await.unwrap();
    for _ in 0..101 {
        note(&root, "note").await;
    }
    let batches = start(&stream);
    flush().await;
    let delivered = batches_of(&batches);
    assert_eq!(delivered.len(), 1);
    assert_eq!(delivered[0].len(), 1);
    let AgentEvent::Snapshot(snapshot) = &delivered[0][0] else {
        panic!("a snapshot");
    };
    assert_eq!(snapshot.entries.len(), 101);
    stream.stop().await;
    harness.close(context()).await.unwrap();
}

/// eukhe addition: `delivered()` is a barrier for every batch committed before it.
#[tokio::test]
async fn delivered_resolves_once_every_batch_of_a_finished_run_reached_the_listener() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    setup
        .faux
        .set_responses(vec![text_message("answer").into()]);
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let (stream, batches) = listen(&harness, &root).await;
    let submission = root.submit(input("hi"), context()).await.unwrap();
    submission.wait(context()).await.unwrap();
    harness.wait_for_idle(context()).await.unwrap();
    stream.delivered().await;
    let kinds = types(&events(&batches));
    assert!(kinds.contains(&"run_end"), "{kinds:?}");
    assert_eq!(kinds.last(), Some(&"usage_changed"), "{kinds:?}");
    // A later commit queues one more batch; the next barrier covers it.
    note(&root, "note").await;
    stream.delivered().await;
    assert_eq!(
        batches_of(&batches).last().map(|batch| types(batch)),
        Some(vec!["entry_appended"])
    );
    stream.stop().await;
    stream.delivered().await;
    harness.close(context()).await.unwrap();
}

/// eukhe addition: an overflow snapshot is the frame `delivered()` waits for.
#[tokio::test]
async fn delivered_covers_the_overflow_snapshot_once_the_stream_starts() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let stream = watch_events(&harness, root.id(), context()).await.unwrap();
    for _ in 0..101 {
        note(&root, "note").await;
    }
    let delivered = tokio::spawn(stream.delivered());
    flush().await;
    assert!(!delivered.is_finished());
    let batches = start(&stream);
    delivered.await.unwrap();
    assert_eq!(types(&events(&batches)), vec!["snapshot"]);
    stream.stop().await;
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn rebuilds_every_committed_partial_of_thinking_text_and_tool_call_arguments_from_message_changes(
) {
    let setup = chat_setup(RegisterFauxProviderOptions {
        tokens_per_second: Some(150.0),
        token_size: Some(FauxTokenSize {
            min: Some(1),
            max: Some(1),
        }),
        ..RegisterFauxProviderOptions::default()
    });
    let message = faux_assistant_message(
        vec![
            faux_thinking("thinking about it ".repeat(10)),
            faux_text("some text ".repeat(10)),
            call(
                "missing",
                serde_json::json!({ "path": "a/long/path/".repeat(10), "note": "x".repeat(60) }),
                "c1",
            ),
        ],
        tool_use(),
    );
    setup
        .faux
        .set_responses(vec![message.into(), text_message("done").into()]);
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let lives = live_values(&harness);
    let (stream, batches) = listen(&harness, &root).await;
    root.submit(input("go"), context())
        .await
        .unwrap()
        .wait(context())
        .await
        .unwrap();
    flush().await;
    let all = events(&batches);
    let mut rebuilt: Vec<AssistantMessage> = Vec::new();
    let mut current: Option<AssistantMessage> = None;
    // The streamed tool-calling message, up to its end; the short final answer commits no partial.
    for event in &all {
        match event {
            AgentEvent::MessageEnd { entry } if entry.kind == "pi.assistant" => break,
            AgentEvent::MessageStart {
                message: Message::Assistant(message),
            } => current = Some(message.clone()),
            AgentEvent::MessageUpdate { changes, .. } => {
                current = Some(apply_changes(current.as_ref().unwrap(), changes));
            }
            _ => continue,
        }
        rebuilt.push(current.clone().unwrap());
    }
    let partials = partials_of(&lives);
    assert!(partials.len() > 2);
    let contents = |messages: &[AssistantMessage]| -> Vec<JsonValue> {
        messages
            .iter()
            .map(|message| to_json(&message.content).unwrap())
            .collect()
    };
    assert_eq!(contents(&rebuilt), contents(&partials));
    let change_types: Vec<&'static str> = all
        .iter()
        .flat_map(|event| match event {
            AgentEvent::MessageUpdate { changes, .. } => changes.clone(),
            _ => Vec::new(),
        })
        .map(|change| match change {
            MessageChange::ThinkingDelta { .. } => "thinking_delta",
            MessageChange::TextDelta { .. } => "text_delta",
            _ => "other",
        })
        .collect();
    assert!(change_types.contains(&"thinking_delta") || change_types.contains(&"text_delta"));
    stream.stop().await;
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn rebuilds_a_sliding_tail_window_from_output_trims_and_appends() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let gate: Deferred = deferred();
    let tool_gate = gate.clone();
    let mut tail = define(
        "tail",
        "Prints lines",
        empty_object_schema(),
        move |api, _| {
            let gate = tool_gate.clone();
            async move {
                for line in 0..6 {
                    print(&*api, &format!("line {line}\n"));
                    tokio::time::sleep(Duration::from_millis(120)).await;
                }
                gate.wait().await;
                Ok(ToolExecutionResult::default())
            }
        },
    );
    tail.output_limits = Some(ToolOutputLimits {
        max_lines: Some(3),
        retain: Some(OutputRetain::Tail),
        ..ToolOutputLimits::default()
    });
    add_tool(&setup.registry, define_tool(tail), None).unwrap();
    setup.faux.set_responses(vec![
        faux_assistant_message(vec![call("tail", serde_json::json!({}), "c1")], tool_use()).into(),
        text_message("done").into(),
    ]);
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let lives = live_values(&harness);
    let outputs = || -> Vec<String> {
        let mut outputs: Vec<String> = Vec::new();
        for live in lives.lock().unwrap_or_else(PoisonError::into_inner).iter() {
            let Some(output) = live
                .get("tools")
                .and_then(|tools| tools.get_index(0))
                .and_then(|slot| slot.get("output"))
                .and_then(JsonValue::as_str)
            else {
                continue;
            };
            if outputs.last().map(String::as_str) != Some(output) {
                outputs.push(output.to_owned());
            }
        }
        outputs
    };
    let (stream, batches) = listen(&harness, &root).await;
    let submission = root.submit(input("go"), context()).await.unwrap();
    wait_for(
        || {
            let done = outputs()
                .last()
                .is_some_and(|output| output.ends_with("line 5\n"));
            async move { done }
        },
        5000,
    )
    .await;
    gate.resolve(());
    submission.wait(context()).await.unwrap();
    flush().await;
    let all = events(&batches);
    assert_eq!(rebuild_outputs(&all), outputs());
    assert!(all.iter().any(|event| matches!(
        event,
        AgentEvent::ToolExecutionUpdate {
            output: Some(ToolOutputUpdate::Window {
                trim_start: Some(_),
                ..
            }),
            ..
        }
    )));
    stream.stop().await;
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn emits_one_exact_batch_when_a_run_ends_and_a_queued_follow_up_starts_the_next() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let release: Deferred = deferred();
    setup.faux.set_responses(vec![
        held(&release, text_message("first")),
        text_message("second").into(),
    ]);
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let input_submission = root.submit(input("a"), context()).await.unwrap();
    let follow_up = root.submit(input("f"), context()).await.unwrap();
    let (stream, batches) = listen(&harness, &root).await;
    release.resolve(());
    follow_up.wait(context()).await.unwrap();
    flush().await;
    let delivered = batches_of(&batches);
    let boundary = delivered
        .iter()
        .find(|batch| batch.iter().any(|event| event.kind() == "run_end"))
        .unwrap();
    assert_eq!(
        types(boundary),
        [
            "message_start",
            "message_end",
            "message_start",
            "message_end",
            "turn_end",
            "run_end",
            "submission",
            "submission",
            "inbox_update",
            "usage_changed",
            "run_start",
            "turn_start",
        ]
    );
    let ids: Vec<_> = boundary
        .iter()
        .filter_map(|event| match event {
            AgentEvent::Submission { record } => Some(record.id),
            _ => None,
        })
        .collect();
    assert_eq!(ids, [input_submission.id(), follow_up.id()]);
    stream.stop().await;
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn ends_a_call_that_never_runs_and_a_tool_aborted_with_its_generation() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    add_tool(
        &setup.registry,
        define_tool(define(
            "wait",
            "Waits until aborted",
            empty_object_schema(),
            |_, cx| async move { Err(aborted(&cx.abort_signal().expect("a call signal")).await) },
        )),
        None,
    )
    .unwrap();
    setup.faux.set_responses(vec![faux_assistant_message(
        vec![
            call("ghost", serde_json::json!({}), "c1"),
            call("wait", serde_json::json!({}), "c2"),
        ],
        tool_use(),
    )
    .into()]);
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let (stream, batches) = listen(&harness, &root).await;
    let submission = root.submit(input("go"), context()).await.unwrap();
    wait_for(
        || {
            let started = events(&batches)
                .iter()
                .any(|event| event.kind() == "tool_execution_start");
            async move { started }
        },
        5000,
    )
    .await;
    // Aborting the generation aborts its round: the tool ends with its aborted result first (spec §8.5).
    let live = harness
        .snapshot(&LIVE_DOC, root.id(), context())
        .await
        .unwrap()
        .unwrap();
    let run_task = from_json(&live.get("run").unwrap()["taskId"]).unwrap();
    harness.abort_task(run_task, context()).await.unwrap();
    submission.wait(context()).await.unwrap();
    flush().await;
    let all = events(&batches);
    // The call not offered ends after its calling message and directly before its result message.
    let round: Vec<String> = all
        .iter()
        .map(|event| match event {
            AgentEvent::MessageEnd { entry } => format!("end:{}", entry.kind),
            AgentEvent::MessageStart { message } => format!(
                "start:{}",
                match message {
                    Message::System(_) => "system",
                    Message::User(_) => "user",
                    Message::Assistant(_) => "assistant",
                    Message::ToolResult(_) => "toolResult",
                }
            ),
            other => other.kind().to_owned(),
        })
        .collect();
    let ghost_end = round
        .iter()
        .position(|kind| kind == "tool_execution_end")
        .unwrap();
    assert_eq!(
        round[ghost_end - 1..ghost_end + 3],
        [
            "end:pi.assistant",
            "tool_execution_end",
            "start:toolResult",
            "end:pi.tool-result"
        ]
    );
    let tool: Vec<(&str, String, bool)> = all
        .iter()
        .filter_map(|event| match event {
            AgentEvent::ToolExecutionStart { call, .. } => {
                Some(("tool_execution_start", call.tool_call_id.clone(), false))
            }
            AgentEvent::ToolExecutionUpdate { call, .. } => {
                Some(("tool_execution_update", call.tool_call_id.clone(), false))
            }
            AgentEvent::ToolExecutionEnd { call, entry, .. } => Some((
                "tool_execution_end",
                call.tool_call_id.clone(),
                entry.is_some(),
            )),
            _ => None,
        })
        .collect();
    assert_eq!(
        tool,
        [
            ("tool_execution_end", "c1".to_owned(), true),
            ("tool_execution_start", "c2".to_owned(), false),
            ("tool_execution_end", "c2".to_owned(), true),
        ]
    );
    stream.stop().await;
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn reports_a_steer_without_run_events_a_reset_as_an_appended_entry_and_nothing_for_other_conversations(
) {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let gate: Deferred = deferred();
    let tool_gate = gate.clone();
    add_tool(
        &setup.registry,
        define_tool(define(
            "hold",
            "Waits",
            empty_object_schema(),
            move |_, _| {
                let gate = tool_gate.clone();
                async move {
                    gate.wait().await;
                    Ok(ToolExecutionResult::default())
                }
            },
        )),
        None,
    )
    .unwrap();
    setup.faux.set_responses(vec![
        faux_assistant_message(vec![call("hold", serde_json::json!({}), "c1")], tool_use()).into(),
        text_message("done").into(),
    ]);
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let other = harness
        .create_conversation(
            ConversationCreateOptions::new(ConversationOwnership::Ownerless),
            context(),
        )
        .await
        .unwrap();
    let (stream, batches) = listen(&harness, &root).await;
    let first = root.submit(input("a"), context()).await.unwrap();
    wait_for(
        || {
            let started = events(&batches)
                .iter()
                .any(|event| event.kind() == "tool_execution_start");
            async move { started }
        },
        5000,
    )
    .await;
    let mut steer = input("s");
    steer.when_busy = Some(WhenBusy::Steer);
    root.submit(steer, context()).await.unwrap();
    let before = batches_of(&batches).len();
    note(&other, "note").await;
    flush().await;
    assert_eq!(batches_of(&batches).len(), before);
    gate.resolve(());
    first.wait(context()).await.unwrap();
    root.reset(None, context()).await.unwrap();
    flush().await;
    let all = events(&batches);
    assert_eq!(
        types(&all)
            .iter()
            .filter(|kind| **kind == "run_start")
            .count(),
        1
    );
    assert_eq!(
        types(&all)
            .iter()
            .filter(|kind| **kind == "run_end")
            .count(),
        1
    );
    assert_eq!(
        types(batches_of(&batches).last().unwrap()),
        ["entry_appended", "submission"]
    );
    stream.stop().await;
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn rejects_an_attachment_cancelled_while_it_waits_for_the_session_line() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let release: Deferred = deferred();
    let gate = release.clone();
    let blocking = tokio::spawn(root.commit(
        move |_tx| async move {
            gate.wait().await;
            Ok(())
        },
        context(),
    ));
    flush().await;
    let (child, cancel) = with_cancel(context());
    let attaching = tokio::spawn(watch_events(&harness, root.id(), &child));
    cancel.cancel(Some(Arc::new(std::io::Error::other("cancelled"))));
    release.resolve(());
    blocking.await.unwrap().unwrap();
    let error = attaching.await.unwrap().unwrap_err();
    assert!(error.to_string().contains("cancelled"), "{error}");
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn applies_deltas_after_an_overflow_snapshot_that_holds_an_in_flight_partial() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let partial = text_message("hel");
    let stream = watch_events(&harness, root.id(), context()).await.unwrap();
    let id = root.id();
    let message = to_json(&partial).unwrap();
    root.commit(
        move |tx| async move {
            let mut generation = eukhe_chord::json::JsonObject::new();
            generation.insert("attempt", JsonValue::from(1));
            generation.insert("message", message);
            tx.doc(&LIVE_DOC, id)
                .await?
                .set("generation", JsonValue::Object(Arc::new(generation)))?;
            Ok(())
        },
        context(),
    )
    .await
    .unwrap();
    for _ in 0..101 {
        note(&root, "note").await;
    }
    let batches = start(&stream);
    flush().await;
    let AgentEvent::Snapshot(snapshot) = batches_of(&batches)[0][0].clone() else {
        panic!("a snapshot first");
    };
    root.commit(
        move |tx| async move {
            let block = tx
                .doc(&LIVE_DOC, id)
                .await?
                .child("generation")?
                .child("message")?
                .child("content")?
                .child(0)?;
            let text = block
                .get("text")?
                .and_then(|item| item.to_value().ok())
                .unwrap_or_default();
            block.set("text", format!("{}lo", text.as_str().unwrap_or_default()))?;
            Ok(())
        },
        context(),
    )
    .await
    .unwrap();
    flush().await;
    let update = batches_of(&batches).last().unwrap()[0].clone();
    let AgentEvent::MessageUpdate { changes, .. } = update else {
        panic!("Unexpected {}", update.kind());
    };
    assert_eq!(
        changes,
        [MessageChange::TextDelta {
            content_index: 0,
            delta: "lo".to_owned()
        }]
    );
    let SnapshotEvent { generation, .. } = snapshot;
    let rebuilt = apply_changes(generation.unwrap().message.as_ref().unwrap(), &changes);
    assert_eq!(
        to_json(&rebuilt.content).unwrap(),
        json(r#"[{"type":"text","text":"hello"}]"#)
    );
    stream.stop().await;
    harness.close(context()).await.unwrap();
}

#[tokio::test]
#[expect(clippy::too_many_lines, reason = "one-to-one port of the TS test")]
async fn reports_usage_only_updates_cleared_tool_progress_tools_ending_without_entries_and_deferred_polls(
) {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let (stream, batches) = listen(&harness, &root).await;
    let id = root.id();
    let change = |edit: fn(&eukhe_chord::delta::Draft) -> Result<(), SessionError>| {
        root.commit(
            move |tx| async move {
                let live = tx.doc(&LIVE_DOC, id).await?;
                edit(&live)
            },
            context(),
        )
    };
    let partial = to_json(&text_message("partial")).unwrap();
    {
        let partial = partial.clone();
        root.commit(
            move |tx| async move {
                let mut generation = eukhe_chord::json::JsonObject::new();
                generation.insert("attempt", JsonValue::from(1));
                generation.insert("message", partial);
                tx.doc(&LIVE_DOC, id)
                    .await?
                    .set("generation", JsonValue::Object(Arc::new(generation)))?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    }
    // A usage-only change sends the usage and no changes.
    change(|live| {
        live.child("generation")?
            .child("message")?
            .child("usage")?
            .set("input", 42)?;
        Ok(())
    })
    .await
    .unwrap();
    change(|live| {
        live.set(
            "generation",
            json(r#"{"attempt":1,"deferred":{"pollAt":1}}"#),
        )?;
        Ok(())
    })
    .await
    .unwrap();
    change(|live| {
        live.child("generation")?
            .child("deferred")?
            .set("pollAt", 2)?;
        Ok(())
    })
    .await
    .unwrap();
    change(|live| {
        live.set(
            "tools",
            json(r#"[{"callId":"c1","name":"t","status":"running","details":{"n":1},"diagnostics":[]}]"#),
        )?;
        Ok(())
    })
    .await
    .unwrap();
    // A safe replay clears the running slot's progress.
    change(|live| {
        let slot = live.child("tools")?.child(0)?;
        slot.delete("details")?;
        slot.delete("diagnostics")?;
        Ok(())
    })
    .await
    .unwrap();
    // A fault marks the slot done without an entry.
    change(|live| {
        live.child("tools")?.child(0)?.set("status", "done")?;
        Ok(())
    })
    .await
    .unwrap();
    root.commit(
        move |tx| async move { tx.retire_doc(&USAGE_DOC, id).await },
        context(),
    )
    .await
    .unwrap();
    root.commit(
        move |tx| async move { tx.retire_doc(&AGENT_DOC, id).await },
        context(),
    )
    .await
    .unwrap();
    flush().await;
    let delivered: Vec<JsonValue> = batches_of(&batches)
        .into_iter()
        .map(|batch| {
            let kept: Vec<AgentEvent> = batch
                .into_iter()
                .filter(|event| event.kind() != "task_failed")
                .collect();
            to_json(&kept).unwrap()
        })
        .collect();
    let mut usage = partial["usage"].clone();
    usage
        .as_object_mut()
        .unwrap()
        .insert("input", JsonValue::from(42));
    let expected = [
        json(&format!(
            r#"[{{"type":"message_start","message":{partial}}}]"#
        )),
        json(&format!(
            r#"[{{"type":"message_update","usage":{usage},"changes":[]}}]"#
        )),
        json(r#"[{"type":"deferred_poll","pollAt":1}]"#),
        json(r#"[{"type":"deferred_poll","pollAt":2}]"#),
        json(r#"[{"type":"tool_execution_start","toolCallId":"c1","toolName":"t","args":{}}]"#),
        json(
            r#"[{"type":"tool_execution_update","toolCallId":"c1","toolName":"t","details":null,"diagnostics":[]}]"#,
        ),
        json(r#"[{"type":"tool_execution_end","toolCallId":"c1","toolName":"t"}]"#),
        // Retired documents read as their initial values.
        json(r#"[{"type":"usage_changed","usage":{"models":{},"tools":{}}}]"#),
        json(r#"[{"type":"agent_changed","agent":{}}]"#),
    ];
    assert_eq!(delivered, expected);
    stream.stop().await;
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn ends_the_stream_with_the_harness() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let stream = watch_events(&harness, root.id(), context()).await.unwrap();
    harness.close(context()).await.unwrap();
    assert_eq!(stream.closed().await, WatchEnd::SessionClosed);
}

#[tokio::test]
async fn starts_a_message_at_the_first_committed_partial_and_ends_it_with_the_converted_entry_on_abort(
) {
    let setup = chat_setup(RegisterFauxProviderOptions {
        tokens_per_second: Some(100.0),
        token_size: Some(FauxTokenSize {
            min: Some(1),
            max: Some(1),
        }),
        ..RegisterFauxProviderOptions::default()
    });
    setup
        .faux
        .set_responses(vec![text_message(&"x".repeat(400)).into()]);
    let OpenChat { harness, root } = open_chat(storage(), &setup, None).await.unwrap();
    let (stream, batches) = listen(&harness, &root).await;
    let submission = root.submit(input("hi"), context()).await.unwrap();
    let assistant_start = |event: &AgentEvent| {
        matches!(
            event,
            AgentEvent::MessageStart {
                message: Message::Assistant(_)
            }
        )
    };
    wait_for(
        || {
            let started = events(&batches).iter().any(assistant_start);
            async move { started }
        },
        5000,
    )
    .await;
    let live = harness
        .snapshot(&LIVE_DOC, root.id(), context())
        .await
        .unwrap()
        .unwrap();
    let run_task = from_json(&live.get("run").unwrap()["taskId"]).unwrap();
    harness.abort_task(run_task, context()).await.unwrap();
    submission.wait(context()).await.unwrap();
    flush().await;
    let all = events(&batches);
    let assistant_ends = all
        .iter()
        .filter(|event| matches!(event, AgentEvent::MessageEnd { entry } if entry.kind == "pi.assistant"))
        .count();
    assert_eq!(assistant_ends, 1);
    assert_eq!(all.iter().filter(|event| assistant_start(event)).count(), 1);
    stream.stop().await;
    harness.close(context()).await.unwrap();
}
