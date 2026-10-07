//! Shared helpers of the `test/harness-tools.test.ts` port: the echo tool
//! shape, tool-calling answers, one submitted run, and its tool results.

use std::future::Future;
use std::sync::Arc;

use eukhe_chord::context::Context;
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_text, faux_tool_call, FauxAssistantMessageOptions,
    FauxResponseStep,
};
use eukhe_pi_ai::typebox::{TSchema, Type};
use eukhe_types::pi_ai::{
    AssistantMessage, JsonValue as PiJsonValue, Message, StopReason, ToolResultMessage,
    UserContentBlock,
};
use futures::future::BoxFuture;

use crate::entries::TOOL_RESULT_ENTRY;
use crate::harness::define::define_tool;
use crate::harness::tests::chat_support::{all_entries, open_chat, ChatEnv, ChatSetup, OpenChat};
use crate::harness::tests::support::context;
use crate::harness::types::{
    InputSubmissionDraft, ToolExecutionApi, ToolExecutionResult, ToolRegistration,
};
use crate::harness::{Conversation, Harness};
use crate::session::SessionResult;
use crate::storage::MemoryStorage;
use crate::types::{EntryRecord, SubmissionStatus};

/// TS `EchoParameters`: `Type.Object({ text: Type.Optional(Type.String()) })`.
pub(crate) fn echo_parameters() -> TSchema {
    Type::object([("text", Type::optional(Type::string()))])
}

/// TS `tool(name, execute)`.
pub(crate) fn tool<F, Fut>(name: &str, execute: F) -> Arc<ToolRegistration>
where
    F: Fn(PiJsonValue, Arc<dyn ToolExecutionApi>, Context) -> Fut + Send + Sync + 'static,
    Fut: Future<Output = SessionResult<ToolExecutionResult>> + Send + 'static,
{
    tool_with(name, execute, |_| {})
}

/// TS `tool(name, execute, extra)`: `extra` sets the optional fields.
pub(crate) fn tool_with<F, Fut>(
    name: &str,
    execute: F,
    extra: impl FnOnce(&mut ToolRegistration),
) -> Arc<ToolRegistration>
where
    F: Fn(PiJsonValue, Arc<dyn ToolExecutionApi>, Context) -> Fut + Send + Sync + 'static,
    Fut: Future<Output = SessionResult<ToolExecutionResult>> + Send + 'static,
{
    let mut registration =
        ToolRegistration::new(name, format!("The {name} tool"), echo_parameters(), execute);
    extra(&mut registration);
    define_tool(registration)
}

/// A result with empty content (TS `{ content: [] }`).
pub(crate) fn empty_content() -> ToolExecutionResult {
    ToolExecutionResult {
        content: Some(Vec::new()),
        ..ToolExecutionResult::default()
    }
}

/// A tool-calling answer with one call per `(name, args, id)`.
pub(crate) fn calls(list: &[(&str, serde_json::Value, &str)]) -> AssistantMessage {
    faux_assistant_message(
        list.iter()
            .map(|(name, args, id)| {
                let serde_json::Value::Object(args) = args.clone() else {
                    panic!("tool arguments are an object");
                };
                faux_tool_call(*name, args, Some((*id).to_owned()))
            })
            .collect::<Vec<_>>(),
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::ToolUse),
            ..FauxAssistantMessageOptions::default()
        },
    )
}

/// TS `DONE`.
pub(crate) fn done() -> AssistantMessage {
    faux_assistant_message(
        vec![faux_text("done")],
        FauxAssistantMessageOptions::default(),
    )
}

/// What [`run`] returns.
pub(crate) struct Run {
    pub(crate) harness: Harness,
    pub(crate) root: Conversation,
    pub(crate) entries: Vec<EntryRecord>,
    pub(crate) status: SubmissionStatus,
}

/// Runs after opening, before the input is submitted.
pub(crate) type Prepare = Box<dyn FnOnce(Harness, Conversation) -> BoxFuture<'static, ()> + Send>;

/// Queue `responses`, open a chat over fresh storage, submit `go`, and wait
/// for it to settle.
pub(crate) async fn run(setup: &ChatSetup, responses: Vec<FauxResponseStep>) -> Run {
    run_with(setup, responses, None, None).await
}

/// [`run`] with a `prepare` step and the chat's environment.
pub(crate) async fn run_with(
    setup: &ChatSetup,
    responses: Vec<FauxResponseStep>,
    prepare: Option<Prepare>,
    env: Option<ChatEnv>,
) -> Run {
    setup.faux.set_responses(responses);
    let OpenChat { harness, root } = open_chat(Arc::new(MemoryStorage::new()), setup, env)
        .await
        .unwrap();
    if let Some(prepare) = prepare {
        prepare(harness.clone(), root.clone()).await;
    }
    let status = submit_and_wait(&root, "go").await;
    let entries = all_entries(&root, context()).await.unwrap();
    Run {
        harness,
        root,
        entries,
        status,
    }
}

/// Submit `content` as input and wait for it to settle.
pub(crate) async fn submit_and_wait(
    conversation: &Conversation,
    content: &str,
) -> SubmissionStatus {
    let settled = conversation
        .submit(InputSubmissionDraft::new(content), context())
        .await
        .unwrap()
        .wait(context())
        .await
        .unwrap();
    settled.state.status()
}

/// The tool result messages of `entries`, in order.
pub(crate) fn results(entries: &[EntryRecord]) -> Vec<ToolResultMessage> {
    entries
        .iter()
        .filter(|entry| TOOL_RESULT_ENTRY.is(Some(entry)))
        .map(|entry| match entry.model.as_deref() {
            Some([Message::ToolResult(message), ..]) => message.clone(),
            other => panic!("tool result entry without a tool result message: {other:?}"),
        })
        .collect()
}

/// Text items as text, other items as `[type]`, joined by `|`.
pub(crate) fn content_text(content: &[UserContentBlock]) -> String {
    content
        .iter()
        .map(|item| match item {
            UserContentBlock::Text(text) => text.text.clone(),
            UserContentBlock::Image(_) => "[image]".to_owned(),
        })
        .collect::<Vec<_>>()
        .join("|")
}

/// TS `resultText(message)`.
pub(crate) fn result_text(message: &ToolResultMessage) -> String {
    content_text(&message.content)
}
