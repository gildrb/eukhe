//! A coding-agent tool turn on JSONL storage: the model reads, edits, and runs commands, then answers. A hook times a
//! `cat` of /tmp/1gb.txt (create it first to measure; without it that call ends in an error result). The storage
//! directory is left behind for inspection.
//! Run:
//!   cargo run -p eukhe-durable --example 17-coding-tools
use std::future::Future;
use std::io::Write;
use std::sync::{Arc, Mutex, PoisonError};
use std::time::Instant;

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::entries::{ASSISTANT_ENTRY, TOOL_RESULT_ENTRY};
use eukhe_durable::env::{ExecutionEnv, NativeExecutionEnv, NativeExecutionEnvOptions};
use eukhe_durable::harness::define::{define_extension, hook};
use eukhe_durable::harness::registry::create_registry;
use eukhe_durable::harness::types::{
    AgentChange, EnvFactory, EnvTarget, Extension, FieldChange, HarnessOptions,
    InputSubmissionDraft, ModelRef, ToolHooks,
};
use eukhe_durable::harness::{ConversationEntryQuery, Harness, RootOptions, TOOL_TASK};
use eukhe_durable::storage::jsonl::{open_native_jsonl_storage, JsonlStorageOptions};
use eukhe_durable::tools::CODING_TOOLS;
use eukhe_durable::types::SubmissionStatus;
use eukhe_pi_ai::models::{create_models, CreateModelsOptions};
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_provider, faux_text, faux_tool_call, FauxAssistantMessageOptions,
    RegisterFauxProviderOptions,
};
use eukhe_types::pi_ai::{
    AssistantMessage, JsonObject, JsonValue, Message, StopReason, ToolCall, UserContent,
    UserContentBlock,
};
use futures::FutureExt;
use tokio::sync::mpsc::{unbounded_channel, UnboundedReceiver, UnboundedSender};

type BoxError = Box<dyn std::error::Error + Send + Sync>;

#[tokio::main]
async fn main() -> Result<(), BoxError> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let key = std::env::var("OPENAI_API_KEY").ok();
    run(&mut std::io::stdout(), &args, key.as_deref()).await
}

/// Runs the example, writing what the TS example prints to `out`.
///
/// # Errors
///
/// Harness, storage, and file failures.
pub async fn run(
    out: &mut (dyn Write + Send),
    _args: &[String],
    _openai_api_key: Option<&str>,
) -> Result<(), BoxError> {
    // Hooks print from the Harness's tasks through a channel; this task writes its lines to `out` in order.
    let (print, mut lines) = unbounded_channel::<String>();
    drain(out, &mut lines, coding_tools(print)).await
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

fn arguments(pairs: &[(&str, JsonValue)]) -> JsonObject {
    pairs
        .iter()
        .map(|(key, value)| ((*key).to_owned(), value.clone()))
        .collect()
}

fn tool_call(name: &str, args: JsonObject, id: &str) -> AssistantMessage {
    faux_assistant_message(
        vec![faux_tool_call(name, args, Some(id.to_owned()))],
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::ToolUse),
            ..FauxAssistantMessageOptions::default()
        },
    )
}

/// Hooks see every call before and after execution; these time the big `cat`.
fn is_big_cat(call: &ToolCall) -> bool {
    call.name == "bash"
        && call
            .arguments
            .get("command")
            .and_then(JsonValue::as_str)
            .is_some_and(|command| command.contains("1gb.txt"))
}

/// TS `text.length > 200 ? `${text.slice(0, 200)}…` : text`, in UTF-16 code units.
fn clip(text: &str) -> String {
    if text.encode_utf16().count() <= 200 {
        return text.to_owned();
    }
    let mut units = 0;
    let mut clipped: String = text
        .chars()
        .take_while(|character| {
            units += character.len_utf16();
            units <= 200
        })
        .collect();
    clipped.push('…');
    clipped
}

#[expect(
    clippy::too_many_lines,
    reason = "one example, step by step in the TS file's order"
)]
async fn coding_tools(print: UnboundedSender<String>) -> Result<(), BoxError> {
    let context = &*BACKGROUND_CONTEXT;
    let directory = tempfile::Builder::new()
        .prefix("pi-durable-example-")
        .tempdir()?
        .keep();
    std::fs::write(directory.join("notes.txt"), "hello world\n")?;
    let directory_text = directory.to_string_lossy().into_owned();

    // The faux provider plays the model: four tool-calling answers, then a final answer.
    let faux = faux_provider(RegisterFauxProviderOptions::default());
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(faux.provider.clone());
    let mut edit = JsonObject::new();
    edit.insert("oldText".to_owned(), JsonValue::from("world"));
    edit.insert("newText".to_owned(), JsonValue::from("durable"));
    faux.set_responses(vec![
        tool_call("read", arguments(&[("path", "notes.txt".into())]), "r").into(),
        tool_call(
            "edit",
            arguments(&[
                ("path", "notes.txt".into()),
                ("edits", JsonValue::Array(vec![JsonValue::Object(edit)])),
            ]),
            "e",
        )
        .into(),
        tool_call(
            "bash",
            arguments(&[("command", "cat notes.txt".into())]),
            "b",
        )
        .into(),
        tool_call(
            "bash",
            arguments(&[("command", "cat /tmp/1gb.txt".into())]),
            "c",
        )
        .into(),
        faux_assistant_message(
            vec![faux_text("The file now greets durable.")],
            FauxAssistantMessageOptions::default(),
        )
        .into(),
    ]);

    let start: Arc<Mutex<Option<Instant>>> = Arc::new(Mutex::new(None));
    let before_start = Arc::clone(&start);
    let sink = print.clone();
    let timing = define_extension(Extension {
        hooks: vec![hook(
            &TOOL_TASK,
            ToolHooks {
                before_tool: Some(Arc::new(move |call, _, _| {
                    if is_big_cat(call) {
                        *before_start.lock().unwrap_or_else(PoisonError::into_inner) =
                            Some(Instant::now());
                    }
                    futures::future::ready(Ok(None)).boxed()
                })),
                after_tool: Some(Arc::new(move |call, _, _, _| {
                    if is_big_cat(call) {
                        let started = *start.lock().unwrap_or_else(PoisonError::into_inner);
                        let elapsed = started.map_or(0, |started| started.elapsed().as_millis());
                        // The receiver lives until `run` returns.
                        let _ = sink.send(format!("cat /tmp/1gb.txt took {elapsed} ms"));
                    }
                    futures::future::ready(Ok(None)).boxed()
                })),
            },
        )],
        ..Extension::named("timing")
    });
    let registry = create_registry();
    // CODING_TOOLS brings read, write, edit, and bash. Tools reach files and processes only through the environment
    // the Harness builds for each call.
    registry.install(Arc::clone(&CODING_TOOLS))?;
    registry.install(timing)?;

    // The environment is built per use and follows the conversation's agent `cwd`.
    let storage =
        open_native_jsonl_storage(&directory_text, context, JsonlStorageOptions::default()).await?;
    let mut options = HarnessOptions::new(models, Arc::new(registry));
    options.env = Some(Arc::new(|target: EnvTarget, _: &Context| {
        let cwd = match target.cwd {
            Some(cwd) => cwd,
            None => match std::env::current_dir() {
                Ok(cwd) => cwd.to_string_lossy().into_owned(),
                Err(error) => {
                    return futures::future::ready(Err(
                        eukhe_durable::session::SessionError::other(error),
                    ))
                    .boxed()
                }
            },
        };
        let env: Arc<dyn ExecutionEnv> =
            Arc::new(NativeExecutionEnv::new(NativeExecutionEnvOptions {
                cwd,
                ..NativeExecutionEnvOptions::default()
            }));
        futures::future::ready(Ok(Some(env))).boxed()
    }) as EnvFactory);
    let harness = Harness::open(Arc::new(storage), options, context).await?;
    let root = harness
        .root(
            RootOptions {
                agent: Some(AgentChange {
                    model: FieldChange::Set(ModelRef {
                        provider: "faux".to_owned(),
                        model_id: "faux-1".to_owned(),
                    }),
                    cwd: FieldChange::Set(directory_text.clone()),
                    ..AgentChange::default()
                }),
                ..RootOptions::default()
            },
            context,
        )
        .await?;

    // Each tool call runs as a durable pi.tool task owned by the generation, which waits for them and continues the
    // run with the next generation.
    let settled = root
        .submit(
            InputSubmissionDraft {
                request_id: None,
                content: UserContent::Text("Greet durable instead.".to_owned()),
                when_busy: None,
            },
            context,
        )
        .await?
        .wait(context)
        .await?;
    let status = match settled.state.status() {
        SubmissionStatus::Queued => "queued",
        SubmissionStatus::Placed => "placed",
        SubmissionStatus::Done => "done",
        SubmissionStatus::Unanswered => "unanswered",
    };
    send(&print, format!("status: {status}"));
    let transcript = root
        .entries(ConversationEntryQuery::default(), 20, None, context)
        .await?;
    for entry in transcript.items.iter().rev() {
        if !TOOL_RESULT_ENTRY.is(Some(entry)) {
            send(&print, entry.kind.clone());
            continue;
        }
        let Some(Message::ToolResult(result)) =
            entry.model.as_ref().and_then(|model| model.first())
        else {
            return Err(format!("entry {} has no tool result", entry.id).into());
        };
        let text: String = result
            .content
            .iter()
            .map(|item| match item {
                UserContentBlock::Text(text) => text.text.as_str(),
                UserContentBlock::Image(_) => "",
            })
            .collect();
        send(
            &print,
            format!(
                "{} {}: {}",
                entry.kind,
                result.tool_name,
                serde_json::to_string(&clip(&text))?
            ),
        );
    }
    if let Some(answer) = settled.state.answer() {
        let entry = root
            .commit(
                move |tx| async move { tx.typed_entry(&ASSISTANT_ENTRY, answer).await },
                context,
            )
            .await?;
        let message = entry
            .as_ref()
            .and_then(|entry| entry.entry().model.as_ref())
            .and_then(|model| model.first());
        let shown = match message {
            Some(Message::Assistant(message)) => serde_json::to_string(&message.content)?,
            Some(message) => serde_json::to_string(message)?,
            None => "undefined".to_owned(),
        };
        send(&print, format!("answer: {shown}"));
    }
    let file = std::fs::read_to_string(directory.join("notes.txt"))?;
    send(&print, format!("file: {}", serde_json::to_string(&file)?));
    harness.close(context).await?;
    send(&print, format!("storage: {directory_text}"));
    Ok(())
}

fn send(print: &UnboundedSender<String>, line: String) {
    // The receiver lives until `run` returns.
    let _ = print.send(line);
}
