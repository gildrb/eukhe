//! Persistent background subagents. One `subagent` tool lets the main agent start named subagents, message them
//! (steer or follow up), stop them mid-answer, and list them. Subagents keep working while the main agent
//! answers the user, and each answer is delivered back to the main agent as a new message once it arrives. Everything
//! survives a restart: the example closes the Harness while a subagent works and reopens it.
//! Uses `OpenAI` when `OPENAI_API_KEY` is set, and a scripted faux model otherwise.
//! Run:
//!   cargo run -p eukhe-durable --example 23-subagent-background
use std::future::Future;
use std::io::{IsTerminal, Write};
use std::path::Path;
use std::sync::{Arc, LazyLock};
use std::time::Duration;

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_chord::json::{from_json, to_json, JsonValue as DurableJson};
use eukhe_durable::documents::{ConversationDoc, DocDefinition};
use eukhe_durable::entries::ASSISTANT_ENTRY;
use eukhe_durable::harness::agent::configure;
use eukhe_durable::harness::define::{define_extension, define_tool};
use eukhe_durable::harness::registry::{create_registry, Registry};
use eukhe_durable::harness::types::{
    AgentChange, ConversationAbortOptions, Extension, ExtensionsChange, FieldChange,
    HarnessOptions, InputSubmissionDraft, ModelRef, ToolExecutionApi, ToolExecutionApiExt,
    ToolExecutionResult, ToolRegistration, ToolReplay, WhenBusy,
};
use eukhe_durable::harness::{
    watch_events, AgentEvent, AgentEventBatch, AgentEventStream, Conversation,
    ConversationEntryQuery, Harness, RootOptions, LIVE_DOC,
};
use eukhe_durable::session::{SessionError, SessionResult, Tx};
use eukhe_durable::storage::sqlite::{open_native_sqlite_storage, NativeSqliteStorageOptions};
use eukhe_durable::tasks::{define_task, NextTaskState, Task, TaskDefinition};
use eukhe_durable::types::{
    ConversationId, ConversationOwnership, DocumentReaderExt, EntryId, JsonObject, LatestFork,
    TaskId, TaskOptions, TaskOutcome, TaskOwnership,
};
use eukhe_pi_ai::models::{create_models, CreateModelsOptions, Models};
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_provider, faux_text, faux_tool_call, FauxAssistantMessageOptions,
    FauxResponseStep, RegisterFauxProviderOptions,
};
use eukhe_pi_ai::providers::openai::openai_provider;
use eukhe_pi_ai::typebox::Type;
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, IndexMap, JsonObject as PiJsonObject,
    JsonValue as PiJsonValue, Message, StopReason, TextContent, UserContent, UserContentBlock,
};
use futures::FutureExt;
use serde::{Deserialize, Serialize};
use tokio::sync::mpsc::{unbounded_channel, UnboundedReceiver, UnboundedSender};
use tokio::sync::watch;

type BoxError = Box<dyn std::error::Error + Send + Sync>;

#[tokio::main]
async fn main() -> Result<(), BoxError> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let key = std::env::var("OPENAI_API_KEY").ok();
    // TS colors its transcript only when stdout is a terminal.
    let style = if std::io::stdout().is_terminal() {
        Style::Color
    } else {
        Style::Plain
    };
    run_styled(&mut std::io::stdout(), &args, key.as_deref(), style).await
}

/// Runs the example, writing what the TS example prints to `out` (without colors).
///
/// `openai_api_key` selects the `OpenAI` branch; the provider itself reads
/// `OPENAI_API_KEY` from the environment, like TS `openaiProvider()`.
///
/// # Errors
///
/// Harness and storage failures.
pub async fn run(
    out: &mut (dyn Write + Send),
    args: &[String],
    openai_api_key: Option<&str>,
) -> Result<(), BoxError> {
    run_styled(out, args, openai_api_key, Style::Plain).await
}

/// [`run`] with ANSI colors when `style` is [`Style::Color`].
async fn run_styled(
    out: &mut (dyn Write + Send),
    _args: &[String],
    openai_api_key: Option<&str>,
    style: Style,
) -> Result<(), BoxError> {
    // Listeners print through a channel; this task writes its lines to `out` in order.
    let (print, mut lines) = unbounded_channel::<String>();
    let ui = Ui {
        print,
        style,
        progress: Arc::new(watch::Sender::new(Progress::default())),
    };
    drain(out, &mut lines, background(ui, openai_api_key.is_some())).await
}

/// Writes every printed line to `out` while `work` runs, then the rest.
async fn drain(
    out: &mut (dyn Write + Send),
    lines: &mut UnboundedReceiver<String>,
    work: impl Future<Output = Result<(), BoxError>>,
) -> Result<(), BoxError> {
    tokio::pin!(work);
    let result = loop {
        tokio::select! {
            biased;
            Some(line) = lines.recv() => writeln!(out, "{line}")?,
            result = &mut work => break result,
        }
    };
    while let Ok(line) = lines.try_recv() {
        writeln!(out, "{line}")?;
    }
    result
}

// ─── Product code ────────────────────────────────────────────────────────────

// Each subagent is its own conversation with its own transcript, so it remembers earlier messages. The main
// conversation keeps a small document that maps subagent names to their conversations. Documents are durable state
// next to a transcript, changed in commits like entries.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
struct Subagent {
    conversation_id: ConversationId,
    /// Answers already reported to the main agent: several messages can end in one answer, reported once.
    reported: Vec<EntryId>,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
struct SubagentsState {
    agents: IndexMap<String, Subagent>,
    reporters: IndexMap<String, TaskId>,
}

fn subagents_initial() -> SubagentsState {
    SubagentsState::default()
}

/// `app.subagents`; a fork of the main conversation starts without subagents.
static SUBAGENTS: ConversationDoc<SubagentsState> = match ConversationDoc::define(
    DocDefinition {
        kind: "app.subagents",
        version: 1,
        initial: subagents_initial,
        migrate: None,
        checkpoint_when: None,
    },
    LatestFork::Initial,
) {
    Ok(token) => token,
    Err(_) => panic!("invalid app.subagents definition"),
};

/// The Subagents document of a conversation, or the initial value.
async fn subagents_of(
    reader: &(impl DocumentReaderExt + ?Sized),
    id: ConversationId,
    cx: &Context,
) -> SessionResult<SubagentsState> {
    match reader.snapshot(&SUBAGENTS, id, cx).await? {
        Some(value) => from_json(&DurableJson::Object(value)).map_err(SessionError::other),
        None => Ok(SubagentsState::default()),
    }
}

// Every task and conversation has an owner, and that decides what an abort or an idle wait reaches: aborting a task
// aborts what it owns, and waiting for a conversation to be idle waits for its work. A subagent must outlive the main
// agent's turns, so its conversation is owned by an anchor: a background task that finishes at once. A background task
// is a boundary: the main agent's Esc and idle waits stop there, but `abort({ background: true })` still reaches past
// it, so a host can stop everything.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "phase", rename_all = "camelCase")]
enum AnchorState {
    Done,
}

type AnchorTask = Task<(), AnchorState, (), ()>;

static ANCHOR: LazyLock<AnchorTask> = LazyLock::new(|| {
    define_task(
        TaskDefinition::new(
            "app.subagent-anchor",
            1,
            |(): &()| Ok(AnchorState::Done),
            |_, runtime, task_context| async move {
                runtime
                    .commit(|_, _| async { Ok(Some(aborted())) }, &task_context)
                    .await
            },
        )
        .phase("done", |_, runtime, task_context| async move {
            runtime
                .commit(|_, _| async { Ok(Some(completed())) }, &task_context)
                .await
        }),
    )
});

fn completed<S>() -> NextTaskState<S, ()> {
    NextTaskState::Terminal {
        outcome: TaskOutcome::Completed { result: () },
    }
}

fn aborted<S>() -> NextTaskState<S, ()> {
    NextTaskState::Terminal {
        outcome: TaskOutcome::Aborted {
            reason: None,
            result: None,
        },
    }
}

// A reporter delivers one message to a subagent and reports the answer to the main agent. It is a background task
// too, so the main agent's Esc and idle waits leave it alone. Tasks are durable: each phase ends with a saved
// checkpoint, and after a restart the task continues from the last one. Request IDs make a repeated submission return
// the first one, so the subagent gets the message once and the main agent gets the report once.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
struct ReporterInput {
    name: String,
    conversation_id: ConversationId,
    message: String,
    follow_up: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "phase", rename_all = "camelCase")]
enum ReporterState {
    Deliver,
    Report {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        report: Option<String>,
    },
}

type ReporterTask = Task<ReporterInput, ReporterState, (), ()>;

static REPORTER: LazyLock<ReporterTask> = LazyLock::new(|| {
    define_task(
        TaskDefinition::new(
            "app.subagent-reporter",
            1,
            |_: &ReporterInput| Ok(ReporterState::Deliver),
            |_, runtime, task_context| async move {
                runtime
                    .commit(|_, _| async { Ok(Some(aborted())) }, &task_context)
                    .await
            },
        )
        // Send the message, wait for its answer, and decide what to report.
        .phase("deliver", |reporter, runtime, task_context| async move {
            let ReporterInput {
                name,
                conversation_id,
                message,
                follow_up,
            } = reporter.input;
            // While the subagent is busy, a steer reaches it at its next step and a follow-up after its current
            // answer.
            let subagent = runtime
                .conversation(conversation_id, &task_context)
                .await?
                .ok_or_else(|| {
                    SessionError::error(format!("Conversation {conversation_id} not found"))
                })?;
            let request = InputSubmissionDraft {
                request_id: Some(format!("subagent:{}", reporter.id)),
                content: UserContent::Text(message),
                when_busy: Some(if follow_up {
                    WhenBusy::FollowUp
                } else {
                    WhenBusy::Steer
                }),
            };
            let submission = subagent.submit(request, &task_context).await?;
            let settled = submission.wait(&task_context).await?;
            let main_id = runtime.conversation_id();
            // One commit decides the report and records the answer as delivered, so a restart does not decide again.
            runtime
                .commit(
                    move |tx, _| async move {
                        let next = |report: Option<String>| {
                            Some(NextTaskState::Running {
                                checkpoint: ReporterState::Report { report },
                            })
                        };
                        // `aborted`: stopped, or withdrawn while queued. Nothing to report.
                        if let Some(reason) = settled.state.reason() {
                            return Ok(next(
                                (reason != "aborted")
                                    .then(|| format!("[subagent {name} failed: {reason}]")),
                            ));
                        }
                        // Always an answered input here.
                        let Some(answer) = settled.state.answer() else {
                            return Ok(next(None));
                        };
                        let reported = tx
                            .doc(&SUBAGENTS, main_id)
                            .await?
                            .child("agents")?
                            .child(name.as_str())?
                            .child("reported")?;
                        let answer_json = to_json(&answer).map_err(SessionError::other)?;
                        let already = reported
                            .value()?
                            .as_array()
                            .is_some_and(|ids| ids.contains(&answer_json));
                        if already {
                            return Ok(next(None));
                        }
                        reported.push([answer_json])?;
                        let entry = tx.typed_entry(&ASSISTANT_ENTRY, answer).await?;
                        let text = match entry
                            .as_ref()
                            .and_then(|entry| entry.entry().model.as_ref())
                            .and_then(|model| model.first())
                        {
                            Some(Message::Assistant(message)) => text_of(message),
                            _ => String::new(),
                        };
                        Ok(next(Some(format!(
                            "[subagent {name} answered, no reply needed] {text}"
                        ))))
                    },
                    &task_context,
                )
                .await
        })
        // Post the report as a follow-up input: it starts a turn when the main agent is idle, or waits for its current
        // answer. If the user presses Esc while it waits in the main agent's queue, it is dropped with the other input;
        // a report that arrives after Esc starts a new turn.
        .phase("report", |reporter, runtime, task_context| async move {
            if let ReporterState::Report {
                report: Some(report),
            } = reporter.checkpoint
            {
                let main = runtime
                    .conversation(runtime.conversation_id(), &task_context)
                    .await?
                    .ok_or_else(|| SessionError::error("Main conversation not found"))?;
                let input = InputSubmissionDraft {
                    request_id: Some(format!("subagent-report:{}", reporter.id)),
                    content: UserContent::Text(report),
                    when_busy: Some(WhenBusy::FollowUp),
                };
                main.submit(input, &task_context).await?;
            }
            runtime
                .commit(|_, _| async { Ok(Some(completed())) }, &task_context)
                .await
        }),
    )
});

fn text_of(message: &AssistantMessage) -> String {
    message
        .content
        .iter()
        .filter_map(|content| match content {
            AssistantContentBlock::Text(text) => Some(text.text.as_str()),
            AssistantContentBlock::Thinking(_) | AssistantContentBlock::ToolCall(_) => None,
        })
        .collect()
}

/// Both tasks belong to the main conversation and are background: its Esc and idle waits skip them.
fn background_options(conversation_id: ConversationId) -> TaskOptions {
    TaskOptions {
        ownership: TaskOwnership::Conversation,
        conversation_id: Some(conversation_id),
        background: Some(true),
        abandon_on_restart: None,
    }
}

/// The tool's reply; a UI can attach to the subagent's conversation through the call's details.
fn reply(
    text: String,
    name: Option<&str>,
    conversation_id: Option<ConversationId>,
) -> SessionResult<ToolExecutionResult> {
    let details = match (conversation_id, name) {
        (Some(conversation_id), Some(name)) => {
            let mut details = JsonObject::new();
            details.insert("name", DurableJson::from(name));
            details.insert(
                "conversationId",
                to_json(&conversation_id).map_err(SessionError::other)?,
            );
            Some(DurableJson::Object(Arc::new(details)))
        }
        _ => None,
    };
    Ok(ToolExecutionResult {
        output: Some(vec![UserContentBlock::Text(TextContent::new(text))]),
        details,
        ..ToolExecutionResult::default()
    })
}

/// Arguments of the `subagent` tool.
#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct SubagentArgs {
    action: String,
    name: Option<String>,
    message: Option<String>,
    follow_up: Option<bool>,
}

#[expect(
    clippy::too_many_lines,
    reason = "the tool's actions, in the TS execute's order"
)]
async fn execute_subagent(
    args: SubagentArgs,
    api: Arc<dyn ToolExecutionApi>,
    call_context: Context,
) -> SessionResult<ToolExecutionResult> {
    let SubagentArgs {
        action,
        name,
        message,
        follow_up,
    } = args;
    let registry = subagents_of(&*api, api.conversation_id(), &call_context).await?;

    if action == "status" {
        let names: Vec<String> = match &name {
            None => registry.agents.keys().cloned().collect(),
            Some(name) => vec![name.clone()],
        };
        let mut lines = Vec::new();
        for each in names {
            let Some(found) = registry.agents.get(&each) else {
                continue;
            };
            // A conversation is busy while it has a run: from an input until its final answer.
            let busy = api
                .snapshot(&LIVE_DOC, found.conversation_id, &call_context)
                .await?
                .is_some_and(|live| live.get("run").is_some());
            lines.push(format!("{each}: {}", if busy { "working" } else { "idle" }));
        }
        let text = if lines.is_empty() {
            "No subagents.".to_owned()
        } else {
            lines.join("\n")
        };
        return reply(text, name.as_deref(), None);
    }
    let Some(name) = name else {
        return reply(format!("{action} needs a name."), None, None);
    };
    let agent = registry.agents.get(&name).cloned();
    if action != "spawn" && agent.is_none() {
        return reply(format!("No subagent named {name}."), Some(&name), None);
    }

    if action == "stop" {
        if let Some(agent) = agent {
            // Aborts the subagent's current answer and tools and drops its queued messages. It stays usable.
            api.conversation(agent.conversation_id, &call_context)
                .await?
                .ok_or_else(|| SessionError::error("Subagent conversation not found"))?
                .abort(ConversationAbortOptions::default(), &call_context)
                .await?;
            return reply(
                format!("Stopped {name}."),
                Some(&name),
                Some(agent.conversation_id),
            );
        }
    }
    let Some(message) = message else {
        return reply(format!("{action} needs a message."), Some(&name), None);
    };

    // spawn and send: one commit starts a reporter for the message.
    let (main_id, task_id) = (api.conversation_id(), api.task_id());
    let committed_name = name.clone();
    let result = api
        .commit(
            move |tx: Tx| async move {
                let name = committed_name;
                let state = tx.doc(&SUBAGENTS, main_id).await?;
                let agents = state.child("agents")?;
                if action == "spawn" {
                    if agents.has(name.as_str())? {
                        return Ok(format!("{name} already exists; use send."));
                    }
                    let anchor = tx
                        .create_task(
                            ANCHOR.erase().as_definition_ref(),
                            DurableJson::Null,
                            background_options(main_id),
                        )
                        .await?;
                    // Owned by a task of the main conversation: starts as a copy of the main agent.
                    let child = tx
                        .create_conversation(ConversationOwnership::Task { task_id: anchor })
                        .await?;
                    // Subagents cannot start subagents, and know who they are.
                    configure(
                        &tx,
                        child.id,
                        &AgentChange {
                            extensions: FieldChange::Set(ExtensionsChange::Edit {
                                add: None,
                                remove: Some(vec![Arc::clone(&SUBAGENT_TOOLS)]),
                            }),
                            instructions: FieldChange::Set(format!(
                                "You are the subagent \"{name}\". Answer the main agent's requests."
                            )),
                            ..AgentChange::default()
                        },
                    )
                    .await?;
                    let created = Subagent {
                        conversation_id: child.id,
                        reported: Vec::new(),
                    };
                    agents.set(
                        name.as_str(),
                        to_json(&created).map_err(SessionError::other)?,
                    )?;
                }
                let conversation_id: ConversationId =
                    from_json(&agents.child(name.as_str())?.value()?)
                        .map(|agent: Subagent| agent.conversation_id)
                        .map_err(SessionError::other)?;
                let input = ReporterInput {
                    name: name.clone(),
                    conversation_id,
                    message,
                    follow_up: action == "send" && follow_up == Some(true),
                };
                let reporter = tx
                    .create_task(
                        REPORTER.erase().as_definition_ref(),
                        to_json(&input).map_err(SessionError::other)?,
                        background_options(main_id),
                    )
                    .await?;
                state.child("reporters")?.set(
                    task_id.to_string(),
                    to_json(&reporter).map_err(SessionError::other)?,
                )?;
                Ok(if action == "send" {
                    format!("Sent to {name}.")
                } else {
                    format!("Started {name}.")
                })
            },
            &call_context,
        )
        .await?;
    let current = subagents_of(&*api, main_id, &call_context)
        .await?
        .agents
        .get(&name)
        .map(|agent| agent.conversation_id);
    reply(result, Some(&name), current)
}

fn subagent_tool() -> Arc<ToolRegistration> {
    let mut tool = ToolRegistration::new(
        "subagent",
        "Manage persistent subagents that work in the background. Actions: spawn (name, message), send (name, message; \
         followUp: true queues it after the current answer instead of steering), stop (name: aborts its current work), \
         status (name, or all subagents without one). Answers are reported back to you when they arrive.",
        Type::object([
            (
                "action",
                Type::union([
                    Type::literal("spawn"),
                    Type::literal("send"),
                    Type::literal("stop"),
                    Type::literal("status"),
                ]),
            ),
            ("name", Type::optional(Type::string())),
            ("message", Type::optional(Type::string())),
            ("followUp", Type::optional(Type::boolean())),
        ]),
        |args: PiJsonValue, api: Arc<dyn ToolExecutionApi>, call_context: Context| async move {
            let args: SubagentArgs = serde_json::from_value(args).map_err(SessionError::other)?;
            execute_subagent(args, api, call_context).await
        },
    );
    // A call interrupted by a crash is not rerun: repeating `stop` could stop newer work. The model sees that the call
    // was interrupted and can check with `status`.
    tool.replay = Some(ToolReplay::Unsafe);
    define_tool(tool)
}

// The task definitions come with the extension, so pending reporters resume after a restart once the host installs
// it again.
static SUBAGENT_TOOLS: LazyLock<Arc<Extension>> = LazyLock::new(|| {
    define_extension(Extension {
        tasks: vec![ANCHOR.erase(), REPORTER.erase()],
        tools: vec![subagent_tool()],
        ..Extension::named("subagent-tools")
    })
});

// ─── Host setup ─────────────────────────────────────────────────────────────

fn answer(text: &str) -> AssistantMessage {
    faux_assistant_message(
        vec![faux_text(text)],
        FauxAssistantMessageOptions::default(),
    )
}

fn call(input: &[(&str, &str)]) -> AssistantMessage {
    let arguments: PiJsonObject = input
        .iter()
        .map(|(key, value)| ((*key).to_owned(), PiJsonValue::from(*value)))
        .collect();
    faux_assistant_message(
        vec![faux_tool_call("subagent", arguments, None)],
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::ToolUse),
            ..FauxAssistantMessageOptions::default()
        },
    )
}

fn blocks_text(blocks: &[UserContentBlock]) -> String {
    blocks
        .iter()
        .filter_map(|part| match part {
            UserContentBlock::Text(text) => Some(text.text.as_str()),
            UserContentBlock::Image(_) => None,
        })
        .collect()
}

/// The main agent and the subagent share one scripted model, which answers each request by its last message.
fn route(messages: &[Message]) -> AssistantMessage {
    // System messages carry prompt changes; the request is about the message before them.
    let last = messages
        .iter()
        .rev()
        .find(|message| !matches!(message, Message::System(_)));
    let text = match last {
        Some(Message::User(message)) => match &message.content {
            UserContent::Text(text) => text.clone(),
            UserContent::Blocks(blocks) => blocks_text(blocks),
        },
        Some(Message::Assistant(message)) => text_of(message),
        Some(Message::ToolResult(message)) => blocks_text(&message.content),
        Some(Message::System(_)) | None => String::new(),
    };
    // The main agent repeats what the tool said.
    if matches!(last, Some(Message::ToolResult(_))) {
        return answer(&format!("OK. {text}"));
    }
    // The main agent.
    if text.contains("Start a subagent") {
        return call(&[
            ("action", "spawn"),
            ("name", "reader"),
            ("message", "Summarize the plot of Moby Dick."),
        ]);
    }
    if text.contains("whale's name") {
        return call(&[
            ("action", "send"),
            ("name", "reader"),
            ("message", "What is the whale called?"),
        ]);
    }
    if text.contains("every chapter") {
        return call(&[
            ("action", "send"),
            ("name", "reader"),
            ("message", "Now go through all chapters in detail."),
        ]);
    }
    if text.contains("Stop reader") {
        return call(&[("action", "stop"), ("name", "reader")]);
    }
    if text.contains("my subagents") {
        return call(&[("action", "status")]);
    }
    if text.contains("[subagent") {
        return answer("Noted.");
    }
    // The subagent: short answers, and a long chapter walk-through that is stopped halfway.
    if text.contains("Summarize the plot") {
        return answer("A whale, a captain, an obsession.");
    }
    if text.contains("whale called") {
        return answer("Moby Dick.");
    }
    let chapters: Vec<String> = (1..=135)
        .map(|index| format!("Chapter {index}: more whaling."))
        .collect();
    answer(&chapters.join("\n"))
}

async fn open(
    directory: &Path,
    models: &Models,
    registry: &Registry,
    model: &ModelRef,
) -> Result<(Harness, Conversation), BoxError> {
    let context = &*BACKGROUND_CONTEXT;
    let storage = open_native_sqlite_storage(
        &directory.join("session.sqlite"),
        NativeSqliteStorageOptions::default(),
    )
    .await?;
    let harness = Harness::open(
        Arc::new(storage),
        HarnessOptions::new(models.clone(), Arc::new(registry.clone())),
        context,
    )
    .await?;
    let root = harness
        .root(
            RootOptions {
                agent: Some(AgentChange {
                    model: FieldChange::Set(model.clone()),
                    ..AgentChange::default()
                }),
                ..RootOptions::default()
            },
            context,
        )
        .await?;
    Ok((harness, root))
}

// ─── UI: the main conversation's transcript, as a user would see it ───

/// Whether the transcript is printed with ANSI colors.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Style {
    Plain,
    Color,
}

/// What the transcript printed so far: the newest entry whose `message_end`
/// it handled, and how many tool results it showed.
#[derive(Debug, Clone, Copy, Default)]
struct Progress {
    last_entry: Option<EntryId>,
    tool_results: usize,
}

#[derive(Clone)]
struct Ui {
    print: UnboundedSender<String>,
    style: Style,
    /// Shared by every stream the UI follows, across the restart.
    progress: Arc<watch::Sender<Progress>>,
}

impl Ui {
    fn color(&self, code: u8, text: &str) -> String {
        match self.style {
            Style::Color => format!("\x1b[{code}m{text}\x1b[0m"),
            Style::Plain => text.to_owned(),
        }
    }

    fn line(&self, line: String) {
        // The receiver lives until `run` returns.
        let _ = self.print.send(line);
    }

    /// TS `/^\[subagent (\S+) ([^\]]*)\] ?(.*)$/s`: name, status, and rest of a subagent report.
    fn parse_report(text: &str) -> Option<(&str, &str, &str)> {
        let rest = text.strip_prefix("[subagent ")?;
        let name_end = rest.find(char::is_whitespace)?;
        let (name, rest) = rest.split_at(name_end);
        if name.is_empty() {
            return None;
        }
        let rest = rest.strip_prefix(' ')?;
        let close = rest.find(']')?;
        let (status, rest) = rest.split_at(close);
        let rest = &rest[1..];
        Some((name, status, rest.strip_prefix(' ').unwrap_or(rest)))
    }

    fn event(&self, event: &AgentEvent) {
        let AgentEvent::MessageEnd { entry } = event else {
            return;
        };
        self.print_entry(entry);
        let is_tool_result = matches!(
            entry.model.as_ref().and_then(|model| model.first()),
            Some(Message::ToolResult(_))
        );
        self.progress.send_modify(|progress| {
            progress.last_entry = progress.last_entry.max(Some(entry.id));
            progress.tool_results += usize::from(is_tool_result);
        });
    }

    fn print_entry(&self, entry: &eukhe_durable::types::EntryRecord) {
        match entry.model.as_ref().and_then(|model| model.first()) {
            Some(Message::User(message)) => {
                let text = match &message.content {
                    UserContent::Text(text) => text.clone(),
                    UserContent::Blocks(blocks) => blocks_text(blocks),
                };
                // Input is either the user or a subagent's report, which arrives whenever the subagent is done.
                match Self::parse_report(&text) {
                    None => self.line(format!(
                        "\n{} {}",
                        self.color(36, &self.color(1, ">")),
                        self.color(1, &text)
                    )),
                    Some((name, status, rest)) => {
                        let shown = if rest.is_empty() { status } else { rest };
                        self.line(format!(
                            "\n{} {shown}",
                            self.color(35, &self.color(1, &format!("> {name}:")))
                        ));
                    }
                }
            }
            Some(Message::Assistant(message)) => {
                for part in &message.content {
                    let AssistantContentBlock::ToolCall(call) = part else {
                        continue;
                    };
                    let field = |key: &str| call.arguments.get(key).and_then(PiJsonValue::as_str);
                    let action = field("action").unwrap_or("undefined");
                    let name = field("name")
                        .map(|name| format!(" {name}"))
                        .unwrap_or_default();
                    let quoted = field("message")
                        .map(|sent| format!(" {}", serde_json::to_string(sent).unwrap_or_default()))
                        .unwrap_or_default();
                    self.line(self.color(33, &format!("  {} {action}{name}{quoted}", call.name)));
                }
                let text = text_of(message);
                if !text.is_empty() {
                    self.line(text);
                }
            }
            Some(Message::ToolResult(message)) => {
                self.line(self.color(2, &format!("  → {}", blocks_text(&message.content))));
            }
            Some(Message::System(_)) | None => {}
        }
    }

    /// Resolve once the transcript printed the `message_end` of `entry`.
    async fn printed(&self, entry: EntryId) {
        // The sender lives in the UI, which outlives this wait.
        let _ = self
            .progress
            .subscribe()
            .wait_for(|progress| progress.last_entry >= Some(entry))
            .await;
    }

    /// Resolve once the transcript showed more than `count` tool results.
    async fn tool_results_beyond(&self, count: usize) {
        let _ = self
            .progress
            .subscribe()
            .wait_for(|progress| progress.tool_results > count)
            .await;
    }

    fn tool_results(&self) -> usize {
        self.progress.borrow().tool_results
    }

    /// Print the main conversation's messages as they are committed. Subagents work in their own conversations.
    async fn follow(
        &self,
        harness: &Harness,
        id: ConversationId,
    ) -> SessionResult<AgentEventStream> {
        let stream = watch_events(harness, id, &BACKGROUND_CONTEXT).await?;
        let ui = self.clone();
        stream.start(Arc::new(move |events: AgentEventBatch, _| {
            for event in events.iter() {
                ui.event(event);
            }
            futures::future::ready(Ok(())).boxed()
        }))?;
        Ok(stream)
    }
}

/// Say something to the main agent and wait for its answer.
async fn say(root: &Conversation, text: &str) -> SessionResult<()> {
    let context = &*BACKGROUND_CONTEXT;
    root.submit(
        InputSubmissionDraft {
            request_id: None,
            content: UserContent::Text(text.to_owned()),
            when_busy: None,
        },
        context,
    )
    .await?
    .wait(context)
    .await?;
    Ok(())
}

/// Wait until every message to a subagent was answered and reported, and the main agent has reacted.
async fn settle(harness: &Harness, root: &Conversation, ui: &Ui) -> SessionResult<()> {
    let context = &*BACKGROUND_CONTEXT;
    let reporters = subagents_of(harness, root.id(), context).await?.reporters;
    for id in reporters.into_values() {
        harness.wait_for_task(id, context).await?;
    }
    root.wait_for_idle(context).await?;
    // Event callbacks run after their commit; let the last ones print. TS waits 50 ms; this waits until the
    // transcript printed the newest message entry.
    let newest = root
        .entries(ConversationEntryQuery::default(), 20, None, context)
        .await?
        .items
        .into_iter()
        .find(|entry| entry.model.as_ref().is_some_and(|model| !model.is_empty()));
    if let Some(entry) = newest {
        ui.printed(entry.id).await;
    }
    Ok(())
}

/// Poll `check` for up to 10 seconds.
async fn until<F, Fut>(mut check: F) -> SessionResult<()>
where
    F: FnMut() -> Fut,
    Fut: Future<Output = SessionResult<bool>>,
{
    for _ in 0..1000 {
        if check().await? {
            break;
        }
        tokio::time::sleep(Duration::from_millis(10)).await;
    }
    Ok(())
}

async fn working(harness: &Harness, root: &Conversation, name: &str) -> SessionResult<bool> {
    let context = &*BACKGROUND_CONTEXT;
    let Some(agent) = subagents_of(harness, root.id(), context)
        .await?
        .agents
        .get(name)
        .cloned()
    else {
        return Ok(false);
    };
    Ok(harness
        .snapshot(&LIVE_DOC, agent.conversation_id, context)
        .await?
        .is_some_and(|live| live.get("run").is_some()))
}

async fn reporter_count(harness: &Harness, root: &Conversation) -> SessionResult<usize> {
    Ok(subagents_of(harness, root.id(), &BACKGROUND_CONTEXT)
        .await?
        .reporters
        .len())
}

async fn background(ui: Ui, openai: bool) -> Result<(), BoxError> {
    let context = &*BACKGROUND_CONTEXT;
    let models = create_models(CreateModelsOptions::default());
    let mut model = ModelRef {
        provider: "openai".to_owned(),
        model_id: "gpt-6-sol".to_owned(),
    };
    if openai {
        models.set_provider(openai_provider());
    } else {
        // It streams its answers at 50 tokens per second, like a slow real model.
        let faux = faux_provider(RegisterFauxProviderOptions {
            tokens_per_second: Some(50.0),
            ..RegisterFauxProviderOptions::default()
        });
        models.set_provider(faux.provider.clone());
        model = ModelRef {
            provider: "faux".to_owned(),
            model_id: "faux-1".to_owned(),
        };
        let step = FauxResponseStep::factory(|request, _, _, _| Ok(route(request.messages())));
        // More responses than the script needs; each request takes the next one.
        faux.set_responses(vec![step; 40]);
    }
    let registry = create_registry();
    registry.install(Arc::clone(&SUBAGENT_TOOLS))?;
    let directory = tempfile::Builder::new()
        .prefix("pi-durable-subagents-")
        .tempdir()?;

    let (mut harness, mut root) = open(directory.path(), &models, &registry, &model).await?;
    let mut streams = vec![ui.follow(&harness, root.id()).await?];

    // The main agent answers at once; the subagent's answer is reported back when it arrives.
    say(
        &root,
        "Start a subagent named reader that summarizes Moby Dick.",
    )
    .await?;
    settle(&harness, &root, &ui).await?;

    // A long request, stopped while the subagent is still answering.
    say(&root, "Ask reader to summarize every chapter.").await?;
    until(|| working(&harness, &root, "reader")).await?;
    say(&root, "Stop reader.").await?;
    settle(&harness, &root, &ui).await?;

    say(&root, "What are my subagents doing?").await?;
    settle(&harness, &root, &ui).await?;

    // The process stops while the subagent works on a message; after the restart its answer still arrives.
    let before = reporter_count(&harness, &root).await?;
    let shown = ui.tool_results();
    root.submit(
        InputSubmissionDraft {
            request_id: None,
            content: UserContent::Text("Ask reader for the whale's name.".to_owned()),
            when_busy: None,
        },
        context,
    )
    .await?;
    until(|| async { Ok(reporter_count(&harness, &root).await? > before) }).await?;
    // TS polls every 10 ms, by which time the tool's result is committed and shown; wait for it here.
    ui.tool_results_beyond(shown).await;
    harness.close(context).await?;
    ui.line(ui.color(2, "\n  (process restarts)"));
    (harness, root) = open(directory.path(), &models, &registry, &model).await?;
    streams.push(ui.follow(&harness, root.id()).await?);
    settle(&harness, &root, &ui).await?;

    harness.close(context).await?;
    drop(streams);
    directory.close()?;
    Ok(())
}
