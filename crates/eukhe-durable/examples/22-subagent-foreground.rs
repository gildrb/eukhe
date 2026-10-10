//! A foreground subagent tool: the parent's tool call creates a child conversation it owns, runs one task there, and
//! returns the child's answer. Aborting the tool call aborts the child. A UI finds the child through the tool's running
//! details and shows its events under the call.
//! Uses `OpenAI` when `OPENAI_API_KEY` is set, and a scripted faux model otherwise.
//! Run:
//!   cargo run -p eukhe-durable --example 22-subagent-foreground
use std::collections::HashSet;
use std::future::Future;
use std::io::Write;
use std::sync::{Arc, LazyLock, Mutex, PoisonError};

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_chord::json::JsonValue as DurableJson;
use eukhe_durable::entries::ASSISTANT_ENTRY;
use eukhe_durable::harness::agent::configure;
use eukhe_durable::harness::define::{define_extension, define_tool};
use eukhe_durable::harness::registry::create_registry;
use eukhe_durable::harness::types::{
    AgentChange, Extension, ExtensionsChange, FieldChange, HarnessOptions, InputSubmissionDraft,
    ModelRef, ToolExecutionApi, ToolExecutionApiExt, ToolExecutionResult, ToolRegistration,
    ToolReplay,
};
use eukhe_durable::harness::{
    watch_events, AgentEvent, AgentEventBatch, Conversation, ConversationEntryQuery, Harness,
    RootOptions,
};
use eukhe_durable::session::{SessionError, SessionResult, WatchListenerError};
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::types::{
    ConversationId, ConversationOwnership, ConversationQuery, EntryId, SubmissionStatus,
};
use eukhe_pi_ai::models::{create_models, CreateModelsOptions};
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_provider, faux_text, faux_tool_call, FauxAssistantMessageOptions,
    RegisterFauxProviderOptions,
};
use eukhe_pi_ai::providers::openai::openai_provider;
use eukhe_pi_ai::typebox::{Options, Type};
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, JsonObject, JsonValue, Message, StopReason,
    TextContent, UserContent, UserContentBlock,
};
use futures::future::BoxFuture;
use futures::FutureExt;
use tokio::sync::mpsc::{unbounded_channel, UnboundedReceiver, UnboundedSender};
use tokio::sync::watch;

type BoxError = Box<dyn std::error::Error + Send + Sync>;

#[tokio::main]
async fn main() -> Result<(), BoxError> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let key = std::env::var("OPENAI_API_KEY").ok();
    run(&mut std::io::stdout(), &args, key.as_deref()).await
}

/// Runs the example, writing what the TS example prints to `out`.
///
/// `openai_api_key` selects the `OpenAI` branch; the provider itself reads
/// `OPENAI_API_KEY` from the environment, like TS `openaiProvider()`.
///
/// # Errors
///
/// Harness failures.
pub async fn run(
    out: &mut (dyn Write + Send),
    _args: &[String],
    openai_api_key: Option<&str>,
) -> Result<(), BoxError> {
    // Listeners print through a channel; this task writes its lines to `out` in order.
    let (print, mut lines) = unbounded_channel::<String>();
    drain(out, &mut lines, foreground(print, openai_api_key.is_some())).await
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

// ─── Product code: the subagent extension ───────────────────────────────────

async fn answer_text(
    api: &Arc<dyn ToolExecutionApi>,
    answer: EntryId,
    call_context: &Context,
) -> SessionResult<String> {
    let entry = api
        .commit(
            move |tx| async move { tx.typed_entry(&ASSISTANT_ENTRY, answer).await },
            call_context,
        )
        .await?;
    match entry
        .as_ref()
        .and_then(|entry| entry.entry().model.as_ref())
        .and_then(|model| model.first())
    {
        Some(Message::Assistant(message)) => Ok(text_of(message)),
        _ => Err(SessionError::error(format!(
            "Entry {answer} is not an assistant answer"
        ))),
    }
}

fn details(conversation_id: ConversationId) -> SessionResult<DurableJson> {
    DurableJson::parse(&format!(r#"{{"conversationId":{conversation_id}}}"#))
        .map_err(SessionError::other)
}

/// The subagent extension (TS `const Subagent`); its tool removes it from the child it creates.
static SUBAGENT: LazyLock<Arc<Extension>> = LazyLock::new(subagent_extension);

fn subagent_extension() -> Arc<Extension> {
    let mut tool = ToolRegistration::new(
        "subagent",
        "Delegate a self-contained task to a subagent and get its answer back.",
        Type::object([(
            "task",
            Type::string_with(Options::new().set("description", "What the subagent should do")),
        )]),
        |args: JsonValue, api: Arc<dyn ToolExecutionApi>, call_context: Context| {
            async move {
                let task = args
                    .get("task")
                    .and_then(JsonValue::as_str)
                    .unwrap_or_default()
                    .to_owned();
                let task_id = api.task_id();
                // The child is owned by this tool call's task, so aborting the call aborts the child, and the call
                // finishes only once the child's work is done.
                let extension = Arc::clone(&SUBAGENT);
                let child = api
                    .commit(
                        move |tx| async move {
                            // Ownership records the child: a rerun of this call finds it instead of creating another.
                            let query = ConversationQuery {
                                owner_task_id: Some(task_id),
                                ..ConversationQuery::default()
                            };
                            if let Some(existing) =
                                tx.scan_conversations(query, 1, None).await?.items.first()
                            {
                                return Ok(existing.id);
                            }
                            // Starts as a copy of this conversation's agent: model, thinking level, cwd, extensions,
                            // tools.
                            let created = tx
                                .create_conversation(ConversationOwnership::Task { task_id })
                                .await?;
                            // Without this extension, the child is not offered this tool.
                            configure(
                                &tx,
                                created.id,
                                &AgentChange {
                                    extensions: FieldChange::Set(ExtensionsChange::Edit {
                                        add: None,
                                        remove: Some(vec![extension]),
                                    }),
                                    ..AgentChange::default()
                                },
                            )
                            .await?;
                            Ok(created.id)
                        },
                        &call_context,
                    )
                    .await?;
                // A UI watching the parent sees this and can attach to the child.
                api.details(details(child)?, &call_context).await?;

                let handle = api
                    .conversation(child, &call_context)
                    .await?
                    .ok_or_else(|| {
                        SessionError::error(format!("Conversation {child} not found"))
                    })?;
                // The request ID makes a rerun get back the submission it made before the crash.
                let request = InputSubmissionDraft {
                    request_id: Some(format!("subagent:{task_id}")),
                    content: UserContent::Text(task),
                    when_busy: None,
                };
                let settled = handle
                    .submit(request, &call_context)
                    .await?
                    .wait(&call_context)
                    .await?;
                let Some(answer) = settled.state.answer() else {
                    let status = match settled.state.status() {
                        SubmissionStatus::Queued => "queued",
                        SubmissionStatus::Placed => "placed",
                        SubmissionStatus::Done => "done",
                        SubmissionStatus::Unanswered => "unanswered",
                    };
                    return Err(SessionError::error(format!("Subagent failed: {status}")));
                };
                let text = answer_text(&api, answer, &call_context).await?;
                Ok(ToolExecutionResult {
                    output: Some(vec![UserContentBlock::Text(TextContent::new(text))]),
                    details: Some(details(child)?),
                    ..ToolExecutionResult::default()
                })
            }
        },
    );
    // Safe to rerun after a crash: a rerun finds the child it already created and the submission it already made.
    tool.replay = Some(ToolReplay::Safe);
    define_extension(Extension {
        tools: vec![define_tool(tool)],
        ..Extension::named("subagent")
    })
}

// ─── UI: the parent's events, with each subagent's events indented under its call ───

fn print_event(print: &UnboundedSender<String>, indent: &str, event: &AgentEvent) {
    let line = match event {
        AgentEvent::MessageEnd { entry } if entry.kind == "pi.assistant" => {
            match entry.model.as_ref().and_then(|model| model.first()) {
                Some(Message::Assistant(message)) => {
                    let text = text_of(message);
                    (!text.is_empty()).then(|| format!("{indent}assistant: {text}"))
                }
                _ => None,
            }
        }
        AgentEvent::ToolExecutionStart { call, args } => Some(format!(
            "{indent}tool {}({})",
            call.tool_name,
            serde_json::to_string(args).unwrap_or_default()
        )),
        _ => None,
    };
    if let Some(line) = line {
        // The receiver lives until `run` returns.
        let _ = print.send(line);
    }
}

#[derive(Clone)]
struct Ui {
    harness: Harness,
    print: UnboundedSender<String>,
    attached: Arc<Mutex<HashSet<ConversationId>>>,
    /// The newest entry whose `message_end` any attached stream printed.
    printed: Arc<watch::Sender<Option<EntryId>>>,
}

impl Ui {
    fn attach(&self, id: ConversationId, indent: String) -> BoxFuture<'static, SessionResult<()>> {
        let ui = self.clone();
        async move {
            ui.attached
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .insert(id);
            let stream = watch_events(&ui.harness, id, &BACKGROUND_CONTEXT).await?;
            let listener_ui = ui.clone();
            stream.start(Arc::new(move |events: AgentEventBatch, _| {
                let (ui, indent) = (listener_ui.clone(), indent.clone());
                async move {
                    for event in events.iter() {
                        print_event(&ui.print, &indent, event);
                        if let AgentEvent::MessageEnd { entry } = event {
                            ui.printed
                                .send_modify(|last| *last = (*last).max(Some(entry.id)));
                        }
                        let AgentEvent::ToolExecutionUpdate {
                            details: Some(details),
                            ..
                        } = event
                        else {
                            continue;
                        };
                        let Some(child) = details
                            .get("conversationId")
                            .and_then(DurableJson::as_u64)
                            .map(ConversationId::from_number)
                        else {
                            continue;
                        };
                        let known = ui
                            .attached
                            .lock()
                            .unwrap_or_else(PoisonError::into_inner)
                            .contains(&child);
                        if !known {
                            ui.attach(child, format!("{indent}  "))
                                .await
                                .map_err(|error| Arc::new(error) as WatchListenerError)?;
                        }
                    }
                    Ok(())
                }
                .boxed()
            }))?;
            Ok(())
        }
        .boxed()
    }
}

async fn foreground(print: UnboundedSender<String>, openai: bool) -> Result<(), BoxError> {
    let context = &*BACKGROUND_CONTEXT;
    // ─── Host setup ─────────────────────────────────────────────────────────────
    let models = create_models(CreateModelsOptions::default());
    let mut model = ModelRef {
        provider: "openai".to_owned(),
        model_id: "gpt-6-sol".to_owned(),
    };
    if openai {
        models.set_provider(openai_provider());
    } else {
        // The parent delegates, the child answers, and the parent reports.
        let faux = faux_provider(RegisterFauxProviderOptions::default());
        models.set_provider(faux.provider.clone());
        model = ModelRef {
            provider: "faux".to_owned(),
            model_id: "faux-1".to_owned(),
        };
        let mut task = JsonObject::new();
        task.insert(
            "task".to_owned(),
            JsonValue::from("Name three prime numbers."),
        );
        let delegate = faux_tool_call("subagent", task, Some("call-1".to_owned()));
        faux.set_responses(vec![
            faux_assistant_message(
                vec![delegate],
                FauxAssistantMessageOptions {
                    stop_reason: Some(StopReason::ToolUse),
                    ..FauxAssistantMessageOptions::default()
                },
            )
            .into(),
            faux_assistant_message(
                vec![faux_text("2, 3, and 5.")],
                FauxAssistantMessageOptions::default(),
            )
            .into(),
            faux_assistant_message(
                vec![faux_text("The subagent says: 2, 3, and 5.")],
                FauxAssistantMessageOptions::default(),
            )
            .into(),
        ]);
    }
    let registry = create_registry();
    registry.install(Arc::clone(&SUBAGENT))?;
    let harness = Harness::open(
        Arc::new(MemoryStorage::new()),
        HarnessOptions::new(models, Arc::new(registry)),
        context,
    )
    .await?;
    let root = harness
        .root(
            RootOptions {
                agent: Some(AgentChange {
                    model: FieldChange::Set(model),
                    ..AgentChange::default()
                }),
                ..RootOptions::default()
            },
            context,
        )
        .await?;

    let ui = Ui {
        harness: harness.clone(),
        print,
        attached: Arc::new(Mutex::new(HashSet::new())),
        printed: Arc::new(watch::Sender::new(None)),
    };
    ui.attach(root.id(), String::new()).await?;

    let submission = root
        .submit(
            InputSubmissionDraft {
                request_id: None,
                content: UserContent::Text(
                    "Use the subagent tool to find three prime numbers, then tell me what it said."
                        .to_owned(),
                ),
                when_busy: None,
            },
            context,
        )
        .await?;
    submission.wait(context).await?;
    harness.wait_for_idle(context).await?;
    // Event callbacks run after their commit; let the last ones print. TS waits one `setTimeout(0)`; this waits
    // until the parent's newest message was printed.
    ui.printed_newest(&root, context).await?;
    harness.close(context).await?;
    Ok(())
}

impl Ui {
    /// Resolve once an attached stream printed the newest message of `conversation`.
    async fn printed_newest(&self, conversation: &Conversation, cx: &Context) -> SessionResult<()> {
        let newest = conversation
            .entries(ConversationEntryQuery::default(), 20, None, cx)
            .await?
            .items
            .into_iter()
            .find(|entry| entry.model.as_ref().is_some_and(|model| !model.is_empty()));
        if let Some(entry) = newest {
            // The sender lives in the UI, which outlives this wait.
            let _ = self
                .printed
                .subscribe()
                .wait_for(|last| *last >= Some(entry.id))
                .await;
        }
        Ok(())
    }
}
