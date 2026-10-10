//! Helpers shared by the nested tool call tests (ports of the local helpers
//! of `test/harness-structured-output.test.ts`,
//! `test/harness-nested-tools.test.ts`, and
//! `test/harness-nested-tools-restart.test.ts`).

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};

use eukhe_chord::context::Context;
use futures::future::BoxFuture;

use eukhe_chord::json::{from_json, JsonValue};
use eukhe_pi_ai::providers::faux::FauxResponseStep;
use eukhe_types::pi_ai::{
    AssistantMessage, JsonObject as PiJsonObject, Message, TextContent, ToolResultMessage,
    UserContentBlock,
};
use futures::FutureExt;

use super::support::{calls, done, submit_and_wait, tool_with};
use crate::entries::TOOL_RESULT_ENTRY;
use crate::harness::define::define_tool;
use crate::harness::events::{watch_events, AgentEvent, AgentEventStream};
use crate::harness::live::{LiveState, LIVE_DOC};
use crate::harness::tests::chat_support::{all_entries, open_chat, ChatSetup, OpenChat};
use crate::harness::tests::support::{add_tool, context, empty_object_schema};
use crate::harness::tool::ToolTaskInput;
use crate::harness::types::{
    ExecuteToolOptions, NestedToolExecutionResult, ToolDiagnostic, ToolExecutionApi,
    ToolExecutionResult, ToolRegistration,
};
use crate::harness::{Conversation, Harness};
use crate::session::SessionResult;
use crate::storage::MemoryStorage;
use crate::types::{AnyTaskRecord, ConversationId, EntryRecord, SubmissionStatus, TaskQuery};

pub(crate) fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

/// A JSON literal.
pub(crate) fn json(text: &str) -> JsonValue {
    JsonValue::parse(text).expect("valid JSON literal")
}

/// A pi-ai JSON object literal.
pub(crate) fn object(value: serde_json::Value) -> PiJsonObject {
    let serde_json::Value::Object(object) = value else {
        panic!("an object literal");
    };
    object
}

/// TS `returning(name, result, extra)`: a tool that returns `result`, with
/// `extra` such as a schema.
pub(crate) fn returning(
    name: &str,
    result: ToolExecutionResult,
    extra: impl FnOnce(&mut ToolRegistration),
) -> Arc<ToolRegistration> {
    let mut registration =
        ToolRegistration::new(name, name, empty_object_schema(), move |_, _, _| {
            let result = result.clone();
            async move { Ok(result) }
        });
    extra(&mut registration);
    define_tool(registration)
}

/// TS `call(name)`: one call of `name` with ID `c1`.
pub(crate) fn call(name: &str) -> AssistantMessage {
    calls(&[(name, serde_json::json!({}), "c1")])
}

/// What a probe received, in call order.
pub(crate) type Received = Arc<Mutex<Vec<NestedToolExecutionResult>>>;

/// A `probe` tool that makes each `(name, args)` call as a nested call, in
/// order, and records what it got back.
pub(crate) fn probe(list: Vec<(&str, serde_json::Value)>) -> (Arc<ToolRegistration>, Received) {
    let received: Received = Arc::default();
    let list: Vec<(String, PiJsonObject)> = list
        .into_iter()
        .map(|(name, args)| (name.to_owned(), object(args)))
        .collect();
    let sink = Arc::clone(&received);
    let registration = define_tool(ToolRegistration::new(
        "probe",
        "probe",
        empty_object_schema(),
        move |_, api, cx| {
            let (list, sink) = (list.clone(), Arc::clone(&sink));
            async move {
                for (name, args) in list {
                    let result = api
                        .execute_tool(&name, args, &cx, ExecuteToolOptions::default())
                        .await?;
                    lock(&sink).push(result);
                }
                Ok(ToolExecutionResult::default())
            }
        },
    ));
    (registration, received)
}

/// Queue `probe`, then `done`, open a chat over fresh storage, and run `go`.
pub(crate) async fn run_probe(setup: &ChatSetup) -> OpenChat {
    let steps: Vec<FauxResponseStep> = vec![call("probe").into(), done().into()];
    setup.faux.set_responses(steps);
    let chat = open_chat(Arc::new(MemoryStorage::new()), setup, None)
        .await
        .unwrap();
    submit_and_wait(&chat.root, "go").await;
    chat
}

/// TS `nested(setup, name)`: run `name` as a nested call of a `probe` tool
/// and return what the probe received.
pub(crate) async fn nested(setup: &ChatSetup, name: &str) -> NestedToolExecutionResult {
    let (registration, received) = probe(vec![(name, serde_json::json!({}))]);
    add_tool(&setup.registry, registration, None).unwrap();
    let chat = run_probe(setup).await;
    chat.harness.close(context()).await.unwrap();
    let mut received = lock(&received);
    received.pop().expect("the probe received a result")
}

/// TS `direct(setup, name)`: run `name` as a model-issued call and return its
/// transcript message.
pub(crate) async fn direct(setup: &ChatSetup, name: &str) -> ToolResultMessage {
    setup
        .faux
        .set_responses(vec![call(name).into(), done().into()]);
    let chat = open_chat(Arc::new(MemoryStorage::new()), setup, None)
        .await
        .unwrap();
    submit_and_wait(&chat.root, "go").await;
    let entries = all_entries(&chat.root, context()).await.unwrap();
    chat.harness.close(context()).await.unwrap();
    let entry = entries
        .iter()
        .find(|candidate| TOOL_RESULT_ENTRY.is(Some(candidate)))
        .expect("a tool result entry");
    match entry.model.as_deref() {
        Some([Message::ToolResult(message), ..]) => message.clone(),
        other => panic!("tool result entry without a tool result message: {other:?}"),
    }
}

/// TS `codes(result)`.
pub(crate) fn codes(diagnostics: &[ToolDiagnostic]) -> Vec<Option<&str>> {
    diagnostics
        .iter()
        .map(|diagnostic| diagnostic.code.as_deref())
        .collect()
}

/// A text content item.
pub(crate) fn text_item(value: &str) -> UserContentBlock {
    UserContentBlock::Text(TextContent::new(value))
}

/// A result with output `text`.
pub(crate) fn text_result(value: &str) -> ToolExecutionResult {
    ToolExecutionResult {
        output: Some(vec![text_item(value)]),
        ..ToolExecutionResult::default()
    }
}

/// TS `echoTool(extra)`: returns `echo <text>` and counts its runs.
pub(crate) fn echo_tool(
    extra: impl FnOnce(&mut ToolRegistration),
) -> (Arc<ToolRegistration>, Arc<AtomicUsize>) {
    let runs = Arc::new(AtomicUsize::new(0));
    let counted = Arc::clone(&runs);
    let registration = tool_with(
        "echo",
        move |args, _, _| {
            counted.fetch_add(1, Ordering::SeqCst);
            let text = args["text"].as_str().unwrap_or_default().to_owned();
            async move { Ok(text_result(&format!("echo {text}"))) }
        },
        extra,
    );
    (registration, runs)
}

/// TS `call(name, args, id)`.
pub(crate) fn call_with(name: &str, args: serde_json::Value, id: &str) -> AssistantMessage {
    calls(&[(name, args, id)])
}

/// TS `text(result)` of a nested result: the value a schema-less nested call
/// gives programs when it is a string, else `""`.
pub(crate) fn nested_text(result: &NestedToolExecutionResult) -> String {
    result
        .structured_output
        .as_ref()
        .and_then(JsonValue::as_str)
        .unwrap_or_default()
        .to_owned()
}

/// TS `toolTasks(harness)`: every `pi.tool` task, in ID order.
pub(crate) async fn tool_tasks(harness: &Harness) -> Vec<AnyTaskRecord> {
    harness
        .commit(
            |tx| async move {
                tx.scan_tasks(
                    TaskQuery {
                        kind: Some("pi.tool".to_owned()),
                        ..TaskQuery::default()
                    },
                    100,
                    None,
                )
                .await
            },
            context(),
        )
        .await
        .expect("scan tool tasks")
        .items
}

/// The tool task input of `record`.
pub(crate) fn input_of(record: &AnyTaskRecord) -> ToolTaskInput {
    from_json(&record.input).expect("a tool task input")
}

pub(crate) fn is_nested(record: &AnyTaskRecord) -> bool {
    matches!(input_of(record), ToolTaskInput::Nested { .. })
}

/// TS `nestedTasks(harness)`.
pub(crate) async fn nested_tasks(harness: &Harness) -> Vec<AnyTaskRecord> {
    tool_tasks(harness)
        .await
        .into_iter()
        .filter(is_nested)
        .collect()
}

/// What [`run_once`] returns.
pub(crate) struct Ran {
    pub(crate) harness: Harness,
    pub(crate) root: Conversation,
    pub(crate) status: SubmissionStatus,
    pub(crate) entries: Vec<EntryRecord>,
}

/// TS `runOnce(setup, responses)`.
pub(crate) async fn run_once(setup: &ChatSetup, responses: Vec<AssistantMessage>) -> Ran {
    setup
        .faux
        .set_responses(responses.into_iter().map(Into::into).collect());
    let OpenChat { harness, root } = open_chat(Arc::new(MemoryStorage::new()), setup, None)
        .await
        .unwrap();
    let status = submit_and_wait(&root, "go").await;
    let entries = all_entries(&root, context()).await.unwrap();
    Ran {
        harness,
        root,
        status,
        entries,
    }
}

/// The tool result messages of `entries`, in order.
pub(crate) fn results(entries: &[EntryRecord]) -> Vec<ToolResultMessage> {
    super::support::results(entries)
}

/// Events delivered to a started stream, in order.
pub(crate) type Events = Arc<Mutex<Vec<AgentEvent>>>;

/// Attach to `conversation`'s events and collect every one from now on.
pub(crate) async fn listen(
    harness: &Harness,
    conversation: ConversationId,
) -> (AgentEventStream, Events) {
    let stream = watch_events(harness, conversation, context())
        .await
        .unwrap();
    let events: Events = Arc::default();
    let sink = Arc::clone(&events);
    stream
        .start(Arc::new(move |batch, _| {
            lock(&sink).extend(batch.iter().cloned());
            futures::future::ready(Ok(())).boxed()
        }))
        .unwrap();
    (stream, events)
}

/// The `tool_execution_end` event of `call_id`, if delivered.
pub(crate) fn end_of(events: &Events, call_id: &str) -> Option<AgentEvent> {
    lock(events)
        .iter()
        .find(|event| {
            matches!(event, AgentEvent::ToolExecutionEnd { call, .. } if call.tool_call_id == call_id)
        })
        .cloned()
}

/// The nested result of the `tool_execution_end` event of `call_id`.
pub(crate) fn end_result(events: &Events, call_id: &str) -> Option<NestedToolExecutionResult> {
    match end_of(events, call_id) {
        Some(AgentEvent::ToolExecutionEnd { result, .. }) => result,
        _ => None,
    }
}

/// `[type, toolCallId, parentToolCallId]` of tool start and end events.
pub(crate) fn starts_and_ends(events: &Events) -> Vec<(&'static str, String, Option<String>)> {
    lock(events)
        .iter()
        .filter_map(|event| match event {
            AgentEvent::ToolExecutionStart { call, .. }
            | AgentEvent::ToolExecutionEnd { call, .. } => Some((
                event.kind(),
                call.tool_call_id.clone(),
                call.parent_tool_call_id.clone(),
            )),
            _ => None,
        })
        .collect()
}

/// `pi.live` of `conversation`, if it exists.
pub(crate) async fn live(harness: &Harness, conversation: ConversationId) -> Option<LiveState> {
    harness
        .snapshot(&LIVE_DOC, conversation, context())
        .await
        .unwrap()
        .map(|value| from_json(&JsonValue::Object(value)).unwrap())
}

/// `expect(await harness.snapshot(LiveDoc, id)).toEqual({})`.
pub(crate) async fn assert_live_empty(harness: &Harness, conversation: ConversationId) {
    let value = harness
        .snapshot(&LIVE_DOC, conversation, context())
        .await
        .unwrap()
        .map(JsonValue::Object);
    assert_eq!(value, Some(JsonValue::object()));
}

/// `api.executeTool(name, args, cx)`.
pub(crate) fn exec(
    api: &Arc<dyn ToolExecutionApi>,
    name: &str,
    args: serde_json::Value,
    cx: &Context,
) -> BoxFuture<'static, SessionResult<NestedToolExecutionResult>> {
    api.execute_tool(name, object(args), cx, ExecuteToolOptions::default())
}

/// `api.executeTool(name, args, cx, { key })`.
pub(crate) fn exec_key(
    api: &Arc<dyn ToolExecutionApi>,
    name: &str,
    args: serde_json::Value,
    cx: &Context,
    key: &str,
) -> BoxFuture<'static, SessionResult<NestedToolExecutionResult>> {
    let options = ExecuteToolOptions {
        key: Some(key.to_owned()),
        progress: None,
    };
    api.execute_tool(name, object(args), cx, options)
}

/// A JSON value as `serde_json`, for order-insensitive comparisons.
pub(crate) fn plain<T: serde::Serialize>(value: &T) -> serde_json::Value {
    serde_json::to_value(value).expect("serializable")
}

/// A shared slot a tool fills.
pub(crate) type Slot<T> = Arc<Mutex<Option<T>>>;

pub(crate) fn taken<T: Clone>(slot: &Slot<T>) -> T {
    lock(slot).clone().expect("the slot was filled")
}

/// TS `aborted(callContext.abortSignal!)`: the error a call that runs until
/// its signal aborts fails with.
pub(crate) async fn hang(cx: &Context) -> crate::session::SessionError {
    crate::harness::tests::task_support::aborted(&cx.abort_signal().expect("a call signal")).await
}

/// TS `sqlitePath()`: a fresh directory (removed when dropped, the TS
/// `afterEach`) and the database path inside it.
pub(crate) fn sqlite_path(prefix: &str) -> (tempfile::TempDir, std::path::PathBuf) {
    let directory = tempfile::Builder::new()
        .prefix(prefix)
        .tempdir()
        .expect("create a temp dir");
    let path = directory.path().join("session.sqlite");
    (directory, path)
}

/// TS `openNodeSqliteStorage(path)`.
pub(crate) async fn sqlite(path: &std::path::Path) -> Arc<dyn crate::types::Storage> {
    use crate::storage::sqlite::{open_native_sqlite_storage, NativeSqliteStorageOptions};
    Arc::new(
        open_native_sqlite_storage(path, NativeSqliteStorageOptions::default())
            .await
            .expect("open the SQLite storage"),
    )
}

/// TS `open(path, setup)`: the SQLite chat, without starting scheduling.
pub(crate) async fn open_sqlite(path: &std::path::Path, setup: &ChatSetup) -> OpenChat {
    open_chat(sqlite(path).await, setup, None).await.unwrap()
}

/// Submit `go` and return the submission's ID.
pub(crate) async fn submit_go(root: &Conversation) -> crate::types::SubmissionId {
    root.submit(
        crate::harness::types::InputSubmissionDraft::new("go"),
        context(),
    )
    .await
    .unwrap()
    .id()
}

/// `(await harness.submission(id))!.wait()` status.
pub(crate) async fn settle(harness: &Harness, id: crate::types::SubmissionId) -> SubmissionStatus {
    harness
        .submission(id, context())
        .await
        .unwrap()
        .expect("the submission exists")
        .wait(context())
        .await
        .unwrap()
        .state
        .status()
}
