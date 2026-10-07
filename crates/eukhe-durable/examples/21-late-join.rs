//! Late join: a client attaches while a run is already underway. It gets the current state first, the conversation
//! view or the snapshot event, and then only what changes after that.
//! Run:
//!   cargo run -p eukhe-durable --example 21-late-join
use std::future::Future;
use std::io::Write;
use std::sync::{Arc, Mutex, PoisonError};
use std::time::Duration;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_chord::json::JsonValue as DurableJson;
use eukhe_durable::harness::define::{define_extension, define_tool};
use eukhe_durable::harness::registry::create_registry;
use eukhe_durable::harness::types::{
    AgentChange, Extension, FieldChange, HarnessOptions, InputSubmissionDraft, ModelRef,
    ToolExecutionResult, ToolOutputChunk, ToolRegistration,
};
use eukhe_durable::harness::{
    watch_events, AgentEvent, AgentEventBatch, Harness, MessageChange, RootOptions,
    ToolOutputUpdate, ToolSlotStatus,
};
use eukhe_durable::storage::MemoryStorage;
use eukhe_pi_ai::models::{create_models, CreateModelsOptions};
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_provider, faux_text, faux_tool_call, FauxAssistantMessageOptions,
    FauxTokenSize, RegisterFauxProviderOptions,
};
use eukhe_pi_ai::typebox::{TSchema, Type};
use eukhe_types::pi_ai::{JsonObject, StopReason, UserContent};
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
/// # Errors
///
/// Harness failures.
pub async fn run(
    out: &mut (dyn Write + Send),
    _args: &[String],
    _openai_api_key: Option<&str>,
) -> Result<(), BoxError> {
    // Listeners print through a channel; this task writes its lines to `out` in order.
    let (print, mut lines) = unbounded_channel::<String>();
    drain(out, &mut lines, late_join(print)).await
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

fn send(print: &UnboundedSender<String>, line: String) {
    // The receiver lives until `run` returns.
    let _ = print.send(line);
}

/// TS `JSON.stringify(value)` of an optional value: `undefined` when absent.
fn stringify(value: &DurableJson) -> String {
    if value.is_null() {
        "undefined".to_owned()
    } else {
        value.to_string()
    }
}

/// TS `text.slice(start)`, in UTF-16 code units.
fn slice_utf16(text: &str, start: usize) -> &str {
    let mut units = 0;
    for (index, character) in text.char_indices() {
        if units >= start {
            return &text[index..];
        }
        units += character.len_utf16();
    }
    ""
}

async fn pause(ms: u64) {
    tokio::time::sleep(Duration::from_millis(ms)).await;
}

#[expect(
    clippy::too_many_lines,
    reason = "one example, step by step in the TS file's order"
)]
async fn late_join(print: UnboundedSender<String>) -> Result<(), BoxError> {
    let context = &*BACKGROUND_CONTEXT;

    // A tool that prints a line every 100 ms, then a slowly streamed answer.
    let registry = create_registry();
    registry.install(define_extension(Extension {
        tools: vec![define_tool(ToolRegistration::new(
            "count",
            "Counts to ten",
            Type::object(Vec::<(String, TSchema)>::new()),
            |_, api, _| async move {
                for n in 1..=10 {
                    api.output(ToolOutputChunk::Text(&format!("{n}\n")), None)?;
                    pause(100).await;
                }
                Ok(ToolExecutionResult::default())
            },
        ))],
        ..Extension::named("count")
    }))?;
    let faux = faux_provider(RegisterFauxProviderOptions {
        tokens_per_second: Some(40.0),
        token_size: Some(FauxTokenSize {
            min: Some(1),
            max: Some(1),
        }),
        ..RegisterFauxProviderOptions::default()
    });
    faux.set_responses(vec![
        faux_assistant_message(
            vec![faux_tool_call(
                "count",
                JsonObject::new(),
                Some("call-1".to_owned()),
            )],
            FauxAssistantMessageOptions {
                stop_reason: Some(StopReason::ToolUse),
                ..FauxAssistantMessageOptions::default()
            },
        )
        .into(),
        faux_assistant_message(
            vec![faux_text("Counted to ten, and this answer streams slowly.")],
            FauxAssistantMessageOptions::default(),
        )
        .into(),
    ]);
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(faux.provider.clone());
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
                    model: FieldChange::Set(ModelRef {
                        provider: "faux".to_owned(),
                        model_id: "faux-1".to_owned(),
                    }),
                    ..AgentChange::default()
                }),
                ..RootOptions::default()
            },
            context,
        )
        .await?;

    let submission = root
        .submit(
            InputSubmissionDraft {
                request_id: None,
                content: UserContent::Text("Count to ten, then tell me.".to_owned()),
                when_busy: None,
            },
            context,
        )
        .await?;
    // Join while the tool is halfway through.
    pause(500).await;

    // Structural client: the view holds the committed transcript and documents, including the running tool's output.
    let view = root.view_state(context).await?;
    let value = view.value();
    let live = &value["docs"]["pi.live"];
    let kinds: Vec<String> = value["entries"]
        .as_array()
        .map(|entries| {
            entries
                .iter()
                .map(|entry| entry["kind"].as_str().unwrap_or_default().to_owned())
                .collect()
        })
        .unwrap_or_default();
    send(
        &print,
        format!("view entries: {}", serde_json::to_string(&kinds)?),
    );
    let slot = &live["tools"][0];
    send(
        &print,
        format!(
            "view tool slot: {} {}",
            slot["status"].as_str().unwrap_or("undefined"),
            stringify(&slot["output"])
        ),
    );
    let sink = print.clone();
    let _subscription = view.subscribe(move |value: DurableJson, _, _| {
        let slot = &value["docs"]["pi.live"]["tools"][0];
        if slot["status"].as_str() == Some("running") {
            send(
                &sink,
                format!("view output now: {}", stringify(&slot["output"])),
            );
        }
    });

    // Event client: the snapshot event carries the same state; later events apply on top of it.
    let stream = watch_events(&harness, root.id(), context).await?;
    let snapshot = stream.snapshot();
    let tools: Vec<String> = snapshot
        .tools
        .iter()
        .map(|slot| {
            let status = match slot.status {
                ToolSlotStatus::Pending => "pending",
                ToolSlotStatus::Running => "running",
                ToolSlotStatus::Done => "done",
            };
            format!("{} {status}", slot.name)
        })
        .collect();
    send(
        &print,
        format!("snapshot tools: {}", serde_json::to_string(&tools)?),
    );
    let output = Arc::new(Mutex::new(
        snapshot
            .tools
            .first()
            .and_then(|slot| slot.output.clone())
            .unwrap_or_default(),
    ));
    let sink = print.clone();
    // (run ended, its usage printed): the run's last commit reached the listener.
    let finished = Arc::new(watch::Sender::new((false, false)));
    let seen = Arc::clone(&finished);
    stream.start(Arc::new(move |events: AgentEventBatch, _| {
        for event in events.iter() {
            match event {
                AgentEvent::ToolExecutionUpdate {
                    output: Some(update),
                    ..
                } => {
                    let mut output = output.lock().unwrap_or_else(PoisonError::into_inner);
                    *output = match update {
                        ToolOutputUpdate::Set { set } => set.clone(),
                        ToolOutputUpdate::Window { trim_start, append } => format!(
                            "{}{}",
                            slice_utf16(&output, trim_start.unwrap_or(0)),
                            append.as_deref().unwrap_or_default()
                        ),
                    };
                    send(
                        &sink,
                        format!(
                            "event output now: {}",
                            serde_json::to_string(&*output).unwrap_or_default()
                        ),
                    );
                }
                AgentEvent::MessageUpdate { changes, .. } => {
                    let deltas: String = changes
                        .iter()
                        .filter_map(|change| match change {
                            MessageChange::TextDelta { delta, .. } => Some(delta.as_str()),
                            _ => None,
                        })
                        .collect();
                    send(
                        &sink,
                        format!(
                            "event text delta: {}",
                            serde_json::to_string(&deltas).unwrap_or_default()
                        ),
                    );
                }
                other => send(&sink, format!("event: {}", other.kind())),
            }
            // Signalled after the line is sent, so `run` writes it before returning.
            seen.send_modify(|(ended, booked)| {
                *ended |= event.kind() == "run_end";
                *booked |= *ended && event.kind() == "usage_changed";
            });
        }
        futures::future::ready(Ok(())).boxed()
    }))?;

    submission.wait(context).await?;
    harness.wait_for_idle(context).await?;
    // TS `setTimeout(0)` lets the last batch reach the listener; this waits until it printed it.
    // The sender lives in `finished`, which this function holds.
    let _ = finished.subscribe().wait_for(|(_, booked)| *booked).await;
    stream.stop().await;
    view.dispose()?;
    harness.close(context).await?;
    Ok(())
}
