//! Port of `test/harness-compaction.test.ts` (range selection and
//! serialization are unit tests of `harness::compaction`): a scripted faux
//! model that answers agent and summarization requests from separate queues.

mod automatic;
mod edge_cases;
mod inbox;
mod interactions;
mod manual;
mod outcomes;
mod recovery;

use std::collections::VecDeque;
use std::future::Future;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::json::{from_json, JsonValue};
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, FauxAssistantMessageOptions, FauxModelDefinition, FauxResponseStep,
    RegisterFauxProviderOptions,
};
use eukhe_pi_ai::types::SimpleStreamOptions;
use eukhe_pi_ai::utils::diagnostics::{ErrorObject, Thrown};
use eukhe_types::pi_ai::{
    AssistantMessage, CacheRetention, Message, StopReason, SystemContent, TextContent,
    UserContentBlock,
};
use futures::future::BoxFuture;
use futures::FutureExt;
use serde::de::DeserializeOwned;

use super::chat_support::{all_entries, chat_setup, open_chat, text_of, ChatSetup, OpenChat};
use super::support::{add_section, context, empty_object_schema};
use super::task_support::Deferred;
use crate::documents::DocToken;
use crate::harness::define::define_tool;
use crate::harness::live::{LiveState, LIVE_DOC};
use crate::harness::types::{
    CompactionPolicy, CompactionResult, ConversationStreamOptions, InputSubmissionDraft,
    PartialCompactionPolicy, PartialRetryPolicy, ToolExecutionResult, ToolRegistration,
};
use crate::harness::usage::{UsageState, USAGE_DOC};
use crate::harness::{Conversation, Harness};
use crate::storage::MemoryStorage;
use crate::types::{AnyTaskRecord, ConversationId, Storage, SubmissionStatus, TaskId, TaskOutcome};

/// Text of about `tokens` estimated tokens, starting with `label`.
pub(super) fn text(label: &str, tokens: usize) -> String {
    let fill = (tokens * 4).saturating_sub(label.len() + 1);
    format!("{label} {}", "x".repeat(fill))
}

/// One provider request the script answered.
#[derive(Clone)]
pub(super) struct Request {
    pub(super) messages: Vec<Message>,
    pub(super) options: Option<SimpleStreamOptions>,
    pub(super) model: String,
}

type StepFn =
    Arc<dyn Fn(Request) -> BoxFuture<'static, Result<AssistantMessage, Thrown>> + Send + Sync>;

/// A scripted answer, or a function of the request.
#[derive(Clone)]
pub(super) enum Step {
    Message(Box<AssistantMessage>),
    Run(StepFn),
}

impl From<AssistantMessage> for Step {
    fn from(message: AssistantMessage) -> Self {
        Self::Message(Box::new(message))
    }
}

/// A step computed from the request.
pub(super) fn step<F, Fut>(run: F) -> Step
where
    F: Fn(Request) -> Fut + Send + Sync + 'static,
    Fut: Future<Output = AssistantMessage> + Send + 'static,
{
    Step::Run(Arc::new(move |request| {
        let answer = run(request);
        async move { Ok(answer.await) }.boxed()
    }))
}

#[derive(Default)]
struct ScriptState {
    agent: VecDeque<Step>,
    summaries: VecDeque<Step>,
    agent_requests: Vec<Request>,
    summary_requests: Vec<Request>,
}

/// Scripted faux model that answers agent requests and summarization
/// requests from separate queues.
#[derive(Clone, Default)]
pub(super) struct Script(Arc<Mutex<ScriptState>>);

impl Script {
    fn state(&self) -> std::sync::MutexGuard<'_, ScriptState> {
        self.0.lock().unwrap_or_else(PoisonError::into_inner)
    }

    pub(super) fn agent(&self, step: impl Into<Step>) {
        self.state().agent.push_back(step.into());
    }

    pub(super) fn summary(&self, step: impl Into<Step>) {
        self.state().summaries.push_back(step.into());
    }

    pub(super) fn agent_requests(&self) -> Vec<Request> {
        self.state().agent_requests.clone()
    }

    pub(super) fn summary_requests(&self) -> Vec<Request> {
        self.state().summary_requests.clone()
    }

    /// Messages of the newest agent request.
    pub(super) fn last_agent_messages(&self) -> Vec<Message> {
        self.state()
            .agent_requests
            .last()
            .map(|request| request.messages.clone())
            .unwrap_or_default()
    }
}

fn is_summary_request(messages: &[Message]) -> bool {
    matches!(
        messages.first(),
        Some(Message::System(system))
            if matches!(&system.content, SystemContent::Text(content)
                if content.starts_with("You are a context summarization assistant"))
    )
}

pub(super) fn script(setup: &ChatSetup) -> Script {
    let script = Script::default();
    let responses = (0..500)
        .map(|_| {
            let script = script.clone();
            FauxResponseStep::Factory(Arc::new(move |transcript, options, _state, model| {
                let request = Request {
                    messages: transcript.messages().to_vec(),
                    options: options.cloned(),
                    model: model.id.clone(),
                };
                let summary = is_summary_request(&request.messages);
                let next = {
                    let mut state = script.state();
                    if summary {
                        state.summary_requests.push(request.clone());
                        state.summaries.pop_front()
                    } else {
                        state.agent_requests.push(request.clone());
                        state.agent.pop_front()
                    }
                };
                async move {
                    match next {
                        None => {
                            let kind = if summary { "summary" } else { "agent" };
                            Err(ErrorObject::new(format!("No scripted {kind} response")).thrown())
                        }
                        Some(Step::Message(message)) => Ok(*message),
                        Some(Step::Run(run)) => run(request).await,
                    }
                }
                .boxed()
            }))
        })
        .collect();
    setup.faux.set_responses(responses);
    script
}

/// A step that waits for `gate`, or rejects when the request is cancelled.
pub(super) fn gated(
    gate: &Deferred,
    message: AssistantMessage,
    reached: Option<&Deferred>,
) -> Step {
    let gate = gate.clone();
    let reached = reached.cloned();
    Step::Run(Arc::new(move |request| {
        if let Some(reached) = &reached {
            reached.resolve(());
        }
        let gate = gate.wait();
        let signal = request
            .options
            .as_ref()
            .and_then(|options| options.stream.request.signal.clone());
        let message = message.clone();
        async move {
            if let Some(signal) = signal {
                tokio::select! {
                    () = gate => Ok(message),
                    reason = signal.cancelled() => Err(reason),
                }
            } else {
                gate.await;
                Ok(message)
            }
        }
        .boxed()
    }))
}

pub(super) fn answer(content: &str) -> AssistantMessage {
    faux_assistant_message(content, FauxAssistantMessageOptions::default())
}

pub(super) fn failure(error_message: &str) -> AssistantMessage {
    faux_assistant_message(
        "",
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::Error),
            error_message: Some(error_message.to_owned()),
            ..FauxAssistantMessageOptions::default()
        },
    )
}

pub(super) fn with_stop(
    content: impl Into<eukhe_pi_ai::providers::faux::FauxContent>,
    stop_reason: StopReason,
) -> AssistantMessage {
    faux_assistant_message(
        content,
        FauxAssistantMessageOptions {
            stop_reason: Some(stop_reason),
            ..FauxAssistantMessageOptions::default()
        },
    )
}

pub(super) fn summary(content: &str) -> AssistantMessage {
    answer(content)
}

pub(super) const OVERFLOW: &str = "prompt is too long: 250000 tokens > 200000 maximum";

/// Small thresholds: no automatic compaction unless a test enables it.
pub(super) const MANUAL: CompactionPolicy = CompactionPolicy {
    enabled: false,
    reserve_tokens: 1000.0,
    keep_recent_tokens: 150.0,
    background_tokens: 0.0,
};

/// Background threshold at 500 and blocking threshold at 1500 tokens of a
/// 2000-token window.
pub(super) const BACKGROUND: CompactionPolicy = CompactionPolicy {
    enabled: true,
    reserve_tokens: 500.0,
    keep_recent_tokens: 150.0,
    background_tokens: 1000.0,
};

/// Blocking threshold at 700 tokens of a 1000-token window, no background
/// compaction.
pub(super) const BLOCKING: CompactionPolicy = CompactionPolicy {
    enabled: true,
    reserve_tokens: 300.0,
    keep_recent_tokens: 150.0,
    background_tokens: 0.0,
};

/// A chat over the scripted model.
pub(super) struct Chat {
    pub(super) harness: Harness,
    pub(super) root: Conversation,
    pub(super) setup: Arc<ChatSetup>,
    pub(super) faux: Script,
}

impl Chat {
    /// TS `setup.settings.compaction = policy`.
    pub(super) fn set_policy(&self, policy: CompactionPolicy) {
        set_policy(&self.setup, policy);
    }

    /// TS `setup.settings.retry = { enabled: true, maxRetries, baseDelayMs }`.
    pub(super) fn set_retry(&self, max_retries: u32, base_delay_ms: f64) {
        set_retry(&self.setup, max_retries, base_delay_ms);
    }

    /// TS `setup.settings.stream = stream`.
    pub(super) fn set_stream(&self, stream: ConversationStreamOptions) {
        self.setup
            .settings
            .update(|settings| settings.stream = Some(stream));
    }

    pub(super) fn id(&self) -> ConversationId {
        self.root.id()
    }
}

pub(super) fn set_policy(setup: &ChatSetup, policy: CompactionPolicy) {
    setup.settings.update(|settings| {
        settings.compaction = Some(PartialCompactionPolicy {
            enabled: Some(policy.enabled),
            reserve_tokens: Some(policy.reserve_tokens),
            keep_recent_tokens: Some(policy.keep_recent_tokens),
            background_tokens: Some(policy.background_tokens),
        });
    });
}

pub(super) fn set_retry(setup: &ChatSetup, max_retries: u32, base_delay_ms: f64) {
    setup.settings.update(|settings| {
        settings.retry = Some(PartialRetryPolicy {
            enabled: Some(true),
            max_retries: Some(max_retries),
            base_delay_ms: Some(base_delay_ms),
            max_agent_delay_ms: None,
        });
    });
}

/// TS `chatSetup({ models: [{ id: "faux-1", contextWindow, maxTokens: 900 }] })`.
pub(super) fn window_setup(context_window: u64) -> ChatSetup {
    chat_setup(RegisterFauxProviderOptions {
        models: Some(vec![FauxModelDefinition {
            context_window: Some(context_window),
            max_tokens: Some(900),
            ..FauxModelDefinition::new("faux-1")
        }]),
        ..RegisterFauxProviderOptions::default()
    })
}

/// Options of [`open`].
#[derive(Default)]
pub(super) struct OpenOptions {
    pub(super) policy: Option<CompactionPolicy>,
    pub(super) context_window: Option<u64>,
    pub(super) storage: Option<Arc<dyn Storage>>,
    pub(super) setup: Option<ChatSetup>,
}

pub(super) fn preamble(setup: &ChatSetup) {
    add_section(
        &setup.registry,
        "preamble",
        |_, _| async { Ok(Some("You are helpful.".to_owned())) }.boxed(),
        Some(false),
        None,
    )
    .unwrap();
}

pub(super) async fn open(options: OpenOptions) -> Chat {
    let setup = options
        .setup
        .unwrap_or_else(|| window_setup(options.context_window.unwrap_or(100_000)));
    let storage = options
        .storage
        .unwrap_or_else(|| Arc::new(MemoryStorage::new()));
    let policy = options.policy.unwrap_or(MANUAL);
    open_scripted(setup, storage, move |setup| {
        // These tests exercise compaction accounting and thresholds, not the
        // faux provider's cache simulation.
        setup.settings.update(|settings| {
            settings.stream = Some(ConversationStreamOptions {
                cache_retention: Some(CacheRetention::None),
                ..ConversationStreamOptions::default()
            });
        });
        set_policy(setup, policy);
        set_retry(setup, 2, 1.0);
    })
    .await
}

/// Script `setup`, add the preamble, open a chat over `storage`, apply
/// `configure`, and resume scheduling.
pub(super) async fn open_scripted(
    setup: ChatSetup,
    storage: Arc<dyn Storage>,
    configure: impl FnOnce(&ChatSetup),
) -> Chat {
    let setup = Arc::new(setup);
    let faux = script(&setup);
    preamble(&setup);
    let OpenChat { harness, root } = open_chat(storage, &setup, None).await.unwrap();
    configure(&setup);
    harness.resume().unwrap();
    Chat {
        harness,
        root,
        setup,
        faux,
    }
}

/// Submit `content` as input.
pub(super) async fn submit(chat: &Chat, content: &str) -> crate::harness::SubmissionHandle {
    chat.root
        .submit(InputSubmissionDraft::new(content.to_owned()), context())
        .await
        .unwrap()
}

/// Run one turn: `user` answered by `reply`.
pub(super) async fn turn(chat: &Chat, user: &str, reply: &str) {
    chat.faux.agent(answer(reply));
    let submission = submit(chat, user).await;
    assert_eq!(
        submission.wait(context()).await.unwrap().state.status(),
        SubmissionStatus::Done
    );
}

/// Three turns of about 100-token messages.
pub(super) async fn history(chat: &Chat) {
    turn(chat, &text("u1", 100), &text("a1", 100)).await;
    turn(chat, &text("u2", 100), &text("a2", 100)).await;
    turn(chat, &text("u3", 100), &text("a3", 100)).await;
}

/// Admit a manual compaction.
pub(super) async fn compact(chat: &Chat, instructions: Option<&str>) -> TaskId<CompactionResult> {
    chat.root
        .compact(instructions.map(str::to_owned), context())
        .await
        .unwrap()
}

/// The outcome of compaction `id` once terminal.
pub(super) async fn result(
    chat: &Chat,
    id: TaskId<CompactionResult>,
) -> TaskOutcome<CompactionResult> {
    let settled = chat.harness.wait_for_task(id, context()).await.unwrap();
    settled.decode::<CompactionResult>().unwrap().outcome
}

/// The submission ID of a completed conversation-owned compaction.
pub(super) fn submission_id(outcome: &TaskOutcome<CompactionResult>) -> crate::types::SubmissionId {
    match outcome {
        TaskOutcome::Completed { result } => result.submission_id.expect("a summary submission"),
        other => panic!("not completed: {other:?}"),
    }
}

/// The handle of submission `id`.
pub(super) async fn submission(
    chat: &Chat,
    id: crate::types::SubmissionId,
) -> crate::harness::SubmissionHandle {
    chat.harness
        .submission(id, context())
        .await
        .unwrap()
        .expect("the submission exists")
}

/// Status of submission `id` now.
pub(super) async fn status_of(chat: &Chat, id: crate::types::SubmissionId) -> SubmissionStatus {
    submission(chat, id)
        .await
        .status(context())
        .await
        .unwrap()
        .state
        .status()
}

pub(super) async fn kinds(conversation: &Conversation) -> Vec<String> {
    all_entries(conversation, context())
        .await
        .unwrap()
        .into_iter()
        .map(|entry| entry.kind)
        .collect()
}

/// A committed document of `conversation`, decoded.
pub(super) async fn doc<D, T>(
    harness: &Harness,
    token: &D,
    conversation: ConversationId,
) -> Option<T>
where
    D: for<'a> DocToken<Locator<'a> = ConversationId>,
    T: DeserializeOwned,
{
    harness
        .snapshot(token, conversation, context())
        .await
        .unwrap()
        .map(|value| from_json(&JsonValue::Object(value)).unwrap())
}

pub(super) async fn live(chat: &Chat) -> LiveState {
    doc(&chat.harness, &LIVE_DOC, chat.id())
        .await
        .unwrap_or_default()
}

pub(super) async fn usage(chat: &Chat) -> UsageState {
    doc(&chat.harness, &USAGE_DOC, chat.id())
        .await
        .expect("pi.usage exists")
}

/// Input tokens of `faux/faux-1` in the ledger.
pub(super) async fn input_tokens(chat: &Chat) -> u64 {
    usage(chat).await.models["faux/faux-1"].input
}

pub(super) fn user_text(message: Option<&Message>) -> String {
    text_of(message).unwrap_or_default()
}

/// Text of the first user message; a leading baseline system message comes
/// before it.
pub(super) fn first_user_text(messages: &[Message]) -> String {
    user_text(
        messages
            .iter()
            .find(|message| matches!(message, Message::User(_))),
    )
}

/// Compaction tasks that are still live.
pub(super) async fn compaction_tasks(chat: &Chat) -> Vec<AnyTaskRecord> {
    chat.harness
        .inspect(context())
        .await
        .unwrap()
        .tasks
        .into_iter()
        .map(|task| task.record)
        .filter(|record| record.kind == "pi.compaction")
        .collect()
}

/// TS `defineTool({ name, description: name, parameters: Type.Object({}), execute })`.
pub(super) fn tool_with<F, Fut>(name: &str, execute: F) -> Arc<ToolRegistration>
where
    F: Fn() -> Fut + Send + Sync + 'static,
    Fut: Future<Output = Vec<UserContentBlock>> + Send + 'static,
{
    let execute = Arc::new(execute);
    define_tool(ToolRegistration::new(
        name,
        name,
        empty_object_schema(),
        move |_, _, _| {
            let content = execute();
            async move {
                Ok(ToolExecutionResult {
                    output: Some(content.await),
                    ..ToolExecutionResult::default()
                })
            }
        },
    ))
}

/// A tool whose result is `result`.
pub(super) fn text_tool(name: &str, result: &str) -> Arc<ToolRegistration> {
    let result = result.to_owned();
    tool_with(name, move || {
        let result = result.clone();
        async move { vec![UserContentBlock::Text(TextContent::new(result))] }
    })
}
