//! Helpers of the tool round describes: blocking and no-op tools, faux tool
//! calls, `pi.live` reads, and event streams with their labels.

use std::sync::{Arc, Mutex, PoisonError, Weak};
use std::time::Duration;

use eukhe_chord::context::Context;
use eukhe_chord::json::{from_json, JsonValue};
use eukhe_pi_ai::api::StreamSimpleFn;
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_text, faux_tool_call, FauxAssistantMessageOptions,
};
use eukhe_pi_ai::utils::event_stream::AssistantMessageEventStream;
use eukhe_types::pi_ai::{AssistantMessage, AssistantMessageEvent, Message, StopReason};
use futures::FutureExt;

use super::{create, owned, Script};
use crate::entries::TOOL_RESULT_ENTRY;
use crate::harness::live::{LiveState, LIVE_DOC};
use crate::harness::tests::chat_support::ChatSetup;
use crate::harness::tests::support::{context, empty_object_schema};
use crate::harness::tests::task_support::{aborted, deferred, Deferred};
use crate::harness::types::{
    HookDone, InputSubmissionDraft, ToolExecutionMode, ToolExecutionResult, ToolOutputChunk,
    ToolRegistration,
};
use crate::harness::{watch_events, AgentEvent, AgentEventStream, Conversation, Harness};
use crate::session::SessionError;
use crate::types::{AnyTaskRecord, EntryRecord, TaskId, TaskQuery};

/// TS `blockingTool(name)`: a sequential tool that prints `partial`, reports
/// that it started, and blocks until its call is aborted.
pub(super) struct Blocking {
    pub(super) started: Deferred,
    pub(super) registration: ToolRegistration,
}

pub(super) fn blocking_tool(name: &str) -> Blocking {
    let started = deferred::<()>();
    let reached = started.clone();
    let mut registration = ToolRegistration::new(
        name,
        format!("The {name} tool"),
        empty_object_schema(),
        move |_, api, cx| {
            let reached = reached.clone();
            async move {
                api.output(ToolOutputChunk::Text("partial"), None)?;
                reached.resolve(());
                let signal = cx
                    .abort_signal()
                    .ok_or_else(|| SessionError::error("The call has no abort signal"))?;
                Err::<ToolExecutionResult, _>(aborted(&signal).await)
            }
        },
    );
    registration.execution_mode = Some(ToolExecutionMode::Sequential);
    Blocking {
        started,
        registration,
    }
}

/// `{ ...registration, executionMode }`.
pub(super) fn with_mode(
    registration: &ToolRegistration,
    mode: ToolExecutionMode,
) -> ToolRegistration {
    ToolRegistration {
        execution_mode: Some(mode),
        ..registration.clone()
    }
}

/// The `noop` tool: `{ content: [] }`.
pub(super) fn noop() -> ToolRegistration {
    ToolRegistration::new(
        "noop",
        "Does nothing",
        empty_object_schema(),
        |_, _, _| async {
            Ok(ToolExecutionResult {
                output: Some(Vec::new()),
                ..ToolExecutionResult::default()
            })
        },
    )
}

/// TS `toolCalls(...ids)`: one tool-use answer calling `[name, id]` pairs.
pub(super) fn tool_calls(ids: &[(&str, &str)]) -> AssistantMessage {
    faux_assistant_message(
        ids.iter()
            .map(|(name, id)| faux_tool_call(*name, serde_json::Map::new(), Some((*id).to_owned())))
            .collect::<Vec<_>>(),
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::ToolUse),
            ..FauxAssistantMessageOptions::default()
        },
    )
}

/// `fauxAssistantMessage([fauxText(text)])`.
pub(super) fn text_message(text: &str) -> AssistantMessage {
    faux_assistant_message(
        vec![faux_text(text)],
        FauxAssistantMessageOptions::default(),
    )
}

/// `{ type: "input", content }`.
pub(super) fn input(content: &str) -> InputSubmissionDraft {
    InputSubmissionDraft::new(content)
}

/// The committed `pi.live` value.
pub(super) async fn live(harness: &Harness, conversation: &Conversation) -> Option<LiveState> {
    harness
        .snapshot(&LIVE_DOC, conversation.id(), context())
        .await
        .expect("read pi.live")
        .map(|value| from_json(&JsonValue::Object(value)).expect("a pi.live value"))
}

/// `live.run.taskId`.
pub(super) async fn run_task(harness: &Harness, conversation: &Conversation) -> Option<TaskId> {
    live(harness, conversation)
        .await
        .and_then(|live| live.run)
        .map(|run| run.task_id)
}

/// TS `ToolResultEntry.is(entry)`.
pub(super) fn is_tool_result(entry: &EntryRecord) -> bool {
    entry.kind == TOOL_RESULT_ENTRY.kind()
}

/// `harness.commit((tx) => tx.scanTasks(query, limit))` items.
pub(super) async fn scan(harness: &Harness, query: TaskQuery, limit: usize) -> Vec<AnyTaskRecord> {
    harness
        .commit(
            move |tx| async move { tx.scan_tasks(query, limit, None).await },
            context(),
        )
        .await
        .expect("scan tasks")
        .items
}

/// Events delivered to a started stream, in order.
pub(super) type Events = Arc<Mutex<Vec<AgentEvent>>>;

pub(super) fn events_of(events: &Events) -> Vec<AgentEvent> {
    events
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
}

/// TS `listen(harness, conversation)`.
pub(super) async fn listen(
    harness: &Harness,
    conversation: &Conversation,
) -> (AgentEventStream, Events) {
    let stream = watch_events(harness, conversation.id(), context())
        .await
        .expect("watch events");
    let events: Events = Arc::default();
    let sink = Arc::clone(&events);
    stream
        .start(Arc::new(move |batch, _| {
            sink.lock()
                .unwrap_or_else(PoisonError::into_inner)
                .extend(batch.iter().cloned());
            async { Ok(()) }.boxed()
        }))
        .expect("start the stream");
    (stream, events)
}

fn role(message: &Message) -> &'static str {
    match message {
        Message::System(_) => "system",
        Message::User(_) => "user",
        Message::Assistant(_) => "assistant",
        Message::ToolResult(_) => "toolResult",
    }
}

/// Event types, with tool ends and message ends labelled by call ID and
/// whether an entry came along (TS `labels`).
pub(super) fn labels(events: &[AgentEvent]) -> Vec<String> {
    events
        .iter()
        .filter_map(|event| match event {
            AgentEvent::ToolExecutionEnd { call, entry, .. } => {
                Some(format!("end:{}:{}", call.tool_call_id, entry.is_some()))
            }
            AgentEvent::MessageEnd { entry } => {
                let message = entry.model.as_ref().and_then(|model| model.first());
                Some(match message {
                    Some(Message::ToolResult(result)) => format!("result:{}", result.tool_call_id),
                    Some(message) => format!("message:{}", role(message)),
                    None => "message:undefined".to_owned(),
                })
            }
            _ => None,
        })
        .collect()
}

/// TS `events.filter((event) => event.type.startsWith("turn_")).map((event) => event.type)`.
pub(super) fn turns(events: &[AgentEvent]) -> Vec<&'static str> {
    events
        .iter()
        .map(AgentEvent::kind)
        .filter(|kind| kind.starts_with("turn_"))
        .collect()
}

/// `setup.models` with the faux provider's `stream_simple` replaced (TS a
/// `Proxy` over `models`).
pub(super) fn with_stream(setup: &ChatSetup, stream_simple: StreamSimpleFn) {
    let mut provider = setup.faux.provider.clone();
    provider.stream_simple = stream_simple;
    setup.models.set_provider(provider);
}

/// TS `invalidFinalStream`: a stream whose final message is not strict JSON,
/// so the classification commit throws and the task faults.
///
/// TS adds a function property to the final message. Rust messages are
/// typed, so the closest value that fails the same commit is a usage count
/// beyond `Number.MAX_SAFE_INTEGER`, which is not exact JSON.
pub(super) fn invalid_final_stream() -> StreamSimpleFn {
    Arc::new(|_, _, _| {
        let stream = AssistantMessageEventStream::new();
        stream.push(AssistantMessageEvent::Start {
            partial: faux_assistant_message(
                vec![faux_text("partial")],
                FauxAssistantMessageOptions {
                    stop_reason: Some(StopReason::Pending),
                    ..FauxAssistantMessageOptions::default()
                },
            ),
        });
        let mut last = text_message("final");
        last.usage.input = u64::MAX;
        let target = stream.clone();
        tokio::spawn(async move {
            tokio::time::sleep(Duration::from_millis(300)).await;
            target.end(Some(last));
        });
        stream
    })
}

/// An extension hook's work: `opened.commit((tx) => tx.createTask(Node, {
/// name: "hooked" }, owned(owner)), callContext)`. The hook holds the script
/// weakly, as the registry that keeps the hook is the Harness's own.
pub(super) fn start_hooked(script: &Weak<Script>, owner: TaskId, cx: &Context) -> HookDone {
    let (script, cx) = (script.upgrade(), cx.clone());
    async move {
        let script = script.ok_or_else(|| SessionError::error("The test script was dropped"))?;
        let node = script.node().clone();
        script
            .harness()
            .commit(
                move |tx| async move { create(&tx, &node, "hooked", owned(owner)).await },
                &cx,
            )
            .await?;
        Ok(())
    }
    .boxed()
}
