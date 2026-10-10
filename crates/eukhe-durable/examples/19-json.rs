//! JSON mode: stream one prompt's run as JSON lines, like `pi --mode json`. Two modes:
//!   --events (default): the experimental agent events of `watch_events()`, starting with a `snapshot` event.
//!   --ops: the raw `ConversationView` frames, starting with the view itself; each later line holds one commit's ops.
//! --storage sqlite (default) | jsonl | memory: sqlite writes a temporary database file, jsonl a temporary directory;
//! neither is deleted, and the path is printed to stderr at the end.
//! Uses `OpenAI` when `OPENAI_API_KEY` is set, and a scripted faux model otherwise.
//! Run:
//!   cargo run -p eukhe-durable --example 19-json -- --events "What is in this directory?"
use std::future::Future;
use std::io::Write;
use std::sync::Arc;
use std::time::{SystemTime, UNIX_EPOCH};

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_chord::delta::Op;
use eukhe_chord::json::{to_json, JsonValue as DurableJson};
use eukhe_durable::env::{ExecutionEnv, NativeExecutionEnv, NativeExecutionEnvOptions};
use eukhe_durable::harness::define::{define_extension, section};
use eukhe_durable::harness::registry::create_registry;
use eukhe_durable::harness::types::{
    AgentChange, EnvFactory, Extension, FieldChange, HarnessOptions, InputSubmissionDraft, ModelRef,
};
use eukhe_durable::harness::{watch_events, AgentEvent, AgentEventBatch, Harness, RootOptions};
use eukhe_durable::session::Ops;
use eukhe_durable::storage::jsonl::{open_native_jsonl_storage, JsonlStorageOptions};
use eukhe_durable::storage::sqlite::{open_native_sqlite_storage, NativeSqliteStorageOptions};
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::tools::{create_bash_tool, create_read_tool, BashToolOptions, ReadToolOptions};
use eukhe_durable::types::Storage;
use eukhe_pi_ai::models::{create_models, CreateModelsOptions};
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_provider, faux_text, faux_tool_call, FauxAssistantMessageOptions,
    RegisterFauxProviderOptions,
};
use eukhe_pi_ai::providers::openai::openai_provider;
use eukhe_types::pi_ai::{JsonObject, JsonValue, StopReason, UserContent};
use futures::FutureExt;
use tokio::sync::mpsc::{unbounded_channel, UnboundedSender};
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
/// Harness and storage failures, and an unknown `--storage` kind.
pub async fn run(
    out: &mut (dyn Write + Send),
    args: &[String],
    openai_api_key: Option<&str>,
) -> Result<(), BoxError> {
    // Listeners print through a channel; this task writes its lines to `out` in order.
    let (print, mut lines) = unbounded_channel::<String>();
    let work = json_mode(print, args.to_vec(), openai_api_key.is_some());
    drain(out, &mut lines, work).await
}

/// Writes every printed line to `out` while `work` runs, then the rest.
async fn drain(
    out: &mut (dyn Write + Send),
    lines: &mut tokio::sync::mpsc::UnboundedReceiver<String>,
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

#[expect(
    clippy::cast_precision_loss,
    reason = "`Date.now()` is a whole number of milliseconds, far below 2^53"
)]
fn date_now() -> f64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0.0, |elapsed| elapsed.as_millis() as f64)
}

#[expect(
    clippy::too_many_lines,
    reason = "one example, step by step in the TS file's order"
)]
async fn json_mode(
    print: UnboundedSender<String>,
    args: Vec<String>,
    openai: bool,
) -> Result<(), BoxError> {
    let context = &*BACKGROUND_CONTEXT;
    let ops_mode = args.iter().any(|arg| arg == "--ops");
    let storage_index = args.iter().position(|arg| arg == "--storage");
    let storage_kind = match storage_index {
        None => Some("sqlite"),
        Some(index) => args.get(index + 1).map(String::as_str),
    };
    let prompt = args
        .iter()
        .enumerate()
        .find(|(index, arg)| {
            !arg.starts_with("--") && storage_index.is_none_or(|storage| *index != storage + 1)
        })
        .map_or("What is in this directory?", |(_, arg)| arg.as_str());

    let mut location: Option<String> = None;
    let storage: Arc<dyn Storage> = match storage_kind {
        Some("sqlite") => {
            let path = std::env::temp_dir().join(format!("pi-durable-json-{}.sqlite", date_now()));
            location = Some(path.to_string_lossy().into_owned());
            Arc::new(
                open_native_sqlite_storage(&path, NativeSqliteStorageOptions::default()).await?,
            )
        }
        Some("jsonl") => {
            let directory = tempfile::Builder::new()
                .prefix("pi-durable-json-")
                .tempdir()?
                .keep();
            let directory = directory.to_string_lossy().into_owned();
            let storage =
                open_native_jsonl_storage(&directory, context, JsonlStorageOptions::default())
                    .await?;
            location = Some(directory);
            Arc::new(storage)
        }
        Some("memory") => Arc::new(MemoryStorage::new()),
        other => {
            return Err(format!(
                "Unknown --storage {}; use sqlite, jsonl, or memory",
                other.unwrap_or("undefined")
            )
            .into())
        }
    };

    let models = create_models(CreateModelsOptions::default());
    let mut model = ModelRef {
        provider: "openai".to_owned(),
        model_id: "gpt-6-sol".to_owned(),
    };
    if openai {
        models.set_provider(openai_provider());
    } else {
        let faux = faux_provider(RegisterFauxProviderOptions {
            tokens_per_second: Some(200.0),
            ..RegisterFauxProviderOptions::default()
        });
        models.set_provider(faux.provider.clone());
        model = ModelRef {
            provider: "faux".to_owned(),
            model_id: "faux-1".to_owned(),
        };
        let mut ls = JsonObject::new();
        ls.insert("command".to_owned(), JsonValue::from("ls"));
        faux.set_responses(vec![
            faux_assistant_message(
                vec![faux_tool_call("bash", ls, Some("call-1".to_owned()))],
                FauxAssistantMessageOptions {
                    stop_reason: Some(StopReason::ToolUse),
                    ..FauxAssistantMessageOptions::default()
                },
            )
            .into(),
            faux_assistant_message(
                vec![faux_text(
                    "This directory holds the durable package sources, tests, and docs.",
                )],
                FauxAssistantMessageOptions::default(),
            )
            .into(),
        ]);
    }

    let registry = create_registry();
    registry.install(define_extension(Extension {
        tools: vec![
            create_read_tool(ReadToolOptions::default()),
            create_bash_tool(BashToolOptions::default()),
        ],
        sections: vec![section(
            "preamble",
            |_, _| {
                futures::future::ready(Ok(Some("You are a concise coding assistant.".to_owned())))
                    .boxed()
            },
            Some(false),
        )],
        ..Extension::named("coding")
    }))?;
    let env: Arc<dyn ExecutionEnv> = Arc::new(NativeExecutionEnv::new(NativeExecutionEnvOptions {
        cwd: std::env::current_dir()?.to_string_lossy().into_owned(),
        ..NativeExecutionEnvOptions::default()
    }));
    let mut options = HarnessOptions::new(models, Arc::new(registry));
    options.env = Some(Arc::new(move |_, _: &Context| {
        futures::future::ready(Ok(Some(Arc::clone(&env)))).boxed()
    }) as EnvFactory);
    let harness = Harness::open(storage, options, context).await?;
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

    // Attach before submitting, so the stream covers the whole run. `ended` is set once the listener printed the
    // commit that ends the run and books its usage, the last one the run writes.
    let ended = Arc::new(watch::Sender::new(RunEnd::Running));
    let stop: Box<dyn FnOnce() -> futures::future::BoxFuture<'static, ()> + Send> = if ops_mode {
        let watch = root.watch(context).await?;
        let mut view = eukhe_chord::json::JsonObject::new();
        view.insert("view", watch.value().to_json_value());
        send(&print, &DurableJson::Object(Arc::new(view)));
        let (sink, ended) = (print.clone(), Arc::clone(&ended));
        watch.start(Arc::new(move |_value, ops: Ops, _cx| {
            let mut frame = eukhe_chord::json::JsonObject::new();
            frame.insert("ops", ops.iter().map(Op::to_json).collect());
            let frame = DurableJson::Object(Arc::new(frame));
            send(&sink, &frame);
            let text = frame.to_string();
            ended.send_modify(|state| {
                state.observe(
                    text.contains(r#"["d",["docs","pi.live","run"]]"#),
                    text.contains(r#"["docs","pi.usage""#),
                );
            });
            futures::future::ready(Ok(())).boxed()
        }))?;
        Box::new(move || watch.stop().map(drop).boxed())
    } else {
        let stream = watch_events(&harness, root.id(), context).await?;
        send(
            &print,
            &to_json(&AgentEvent::Snapshot(stream.snapshot().clone()))?,
        );
        let (sink, ended) = (print.clone(), Arc::clone(&ended));
        stream.start(Arc::new(move |events: AgentEventBatch, _cx| {
            for event in events.iter() {
                if let Ok(json) = to_json(event) {
                    send(&sink, &json);
                }
                ended.send_modify(|state| {
                    state.observe(event.kind() == "run_end", event.kind() == "usage_changed");
                });
            }
            futures::future::ready(Ok(())).boxed()
        }))?;
        Box::new(move || stream.stop().map(drop).boxed())
    };

    let submission = root
        .submit(
            InputSubmissionDraft {
                request_id: None,
                content: UserContent::Text(prompt.to_owned()),
                when_busy: None,
            },
            context,
        )
        .await?;
    submission.wait(context).await?;
    harness.wait_for_idle(context).await?;
    // Let the last batch reach the listener before stopping. TS waits one `setTimeout(0)`; this waits until the
    // listener printed it.
    // The sender lives in `ended`, which this function holds.
    let _ = ended
        .subscribe()
        .wait_for(|state| *state == RunEnd::Booked)
        .await;
    stop().await;
    harness.close(context).await?;
    if let Some(location) = location {
        eprintln!("{} storage: {location}", storage_kind.unwrap_or_default());
    }
    Ok(())
}

fn send(print: &UnboundedSender<String>, value: &DurableJson) {
    // The receiver lives until `run` returns.
    let _ = print.send(value.to_string());
}

/// How far the printed stream got through the end of the run.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RunEnd {
    Running,
    /// The run ended; its usage is not printed yet.
    Ended,
    /// The run ended and its usage was printed.
    Booked,
}

impl RunEnd {
    fn observe(&mut self, run_ended: bool, usage: bool) {
        if run_ended && *self == Self::Running {
            *self = Self::Ended;
        }
        if usage && *self == Self::Ended {
            *self = Self::Booked;
        }
    }
}
