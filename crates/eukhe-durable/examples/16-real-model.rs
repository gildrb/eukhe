//! A real model: stream an answer from `OpenAI`.
//! Run (needs `OPENAI_API_KEY`; without it the example only reports that requirement and makes no network call):
//!   `OPENAI_API_KEY=... cargo run -p eukhe-durable --example 16-real-model`
use std::future::Future;
use std::io::Write;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_chord::json::JsonValue as DurableJson;
use eukhe_durable::entries::ASSISTANT_ENTRY;
use eukhe_durable::harness::define::{define_extension, section};
use eukhe_durable::harness::registry::create_registry;
use eukhe_durable::harness::types::{
    AgentChange, Extension, FieldChange, HarnessOptions, InputSubmissionDraft, ModelRef,
};
use eukhe_durable::harness::{Harness, RootOptions, LIVE_DOC};
use eukhe_durable::session::ObservedDocumentValue;
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::types::DocumentObserverExt;
use eukhe_pi_ai::models::{create_models, CreateModelsOptions};
use eukhe_pi_ai::providers::openai::openai_provider;
use eukhe_types::pi_ai::{AssistantContentBlock, Message, ModelThinkingLevel, UserContent};
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
/// `openai_api_key` selects whether the example runs; the provider itself
/// reads `OPENAI_API_KEY` from the environment, like TS `openaiProvider()`.
///
/// # Errors
///
/// Harness and provider failures.
pub async fn run(
    out: &mut (dyn Write + Send),
    _args: &[String],
    openai_api_key: Option<&str>,
) -> Result<(), BoxError> {
    if openai_api_key.is_none() {
        writeln!(out, "skipped: OPENAI_API_KEY is not set")?;
        return Ok(());
    }
    // The watch prints through a channel; this task writes the text to `out` as it arrives.
    let (print, mut texts) = unbounded_channel::<String>();
    drain(out, &mut texts, real_model(print)).await
}

/// Writes every printed text to `out` while `work` runs, then the rest.
async fn drain(
    out: &mut (dyn Write + Send),
    texts: &mut UnboundedReceiver<String>,
    work: impl Future<Output = Result<(), BoxError>>,
) -> Result<(), BoxError> {
    tokio::pin!(work);
    let result = loop {
        tokio::select! {
            biased;
            Some(text) = texts.recv() => {
                write!(out, "{text}")?;
                out.flush()?;
            }
            result = &mut work => break result,
        }
    };
    while let Ok(text) = texts.try_recv() {
        write!(out, "{text}")?;
    }
    out.flush()?;
    result
}

/// Prints only what each committed partial adds to the text printed so far.
#[derive(Clone)]
struct Printer {
    print: UnboundedSender<String>,
    printed: Arc<Mutex<String>>,
}

impl Printer {
    fn write(&self, text: &str) {
        // The receiver lives until `run` returns.
        let _ = self.print.send(text.to_owned());
    }

    fn print_text(&self, text: &str) {
        let mut printed = self.printed.lock().unwrap_or_else(PoisonError::into_inner);
        // TS compares UTF-16 lengths; a prefix of `text` is shorter in either unit.
        if text.len() <= printed.len() || !text.starts_with(printed.as_str()) {
            return;
        }
        self.write(&text[printed.len()..]);
        text.clone_into(&mut printed);
    }
}

#[expect(
    clippy::too_many_lines,
    reason = "one example, step by step in the TS file's order"
)]
async fn real_model(print: UnboundedSender<String>) -> Result<(), BoxError> {
    let context = &*BACKGROUND_CONTEXT;
    // Production code passes a Models collection with real providers; the Harness never talks to a provider any
    // other way. openai_provider() reads OPENAI_API_KEY from the environment. While the answer streams, generation
    // commits throttled partials to the conversation's pi.live document. Watching that document streams the answer;
    // the watch sees only committed values.
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(openai_provider());
    let registry = create_registry();
    registry.install(define_extension(Extension {
        sections: vec![section(
            "preamble",
            |_, _| {
                futures::future::ready(Ok(Some("You are a concise assistant.".to_owned()))).boxed()
            },
            Some(false),
        )],
        ..Extension::named("concise")
    }))?;
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
                        provider: "openai".to_owned(),
                        model_id: "gpt-6-sol".to_owned(),
                    }),
                    thinking_level: FieldChange::Set(ModelThinkingLevel::High),
                    ..AgentChange::default()
                }),
                ..RootOptions::default()
            },
            context,
        )
        .await?;
    let live_watch = harness
        .watch_doc(&LIVE_DOC, root.id(), context)
        .await?
        .ok_or("pi.live is missing")?;
    let printer = Printer {
        print,
        printed: Arc::new(Mutex::new(String::new())),
    };
    let watcher = printer.clone();
    live_watch.start(Arc::new(move |value: ObservedDocumentValue, _, _| {
        let block = value.as_ref().and_then(|value| {
            value.get("generation")?.get("message")?["content"]
                .as_array()?
                .iter()
                .find(|content| content["type"].as_str() == Some("text"))
                .cloned()
        });
        if let Some(text) = block.as_ref().and_then(|block| block["text"].as_str()) {
            watcher.print_text(text);
        }
        futures::future::ready(Ok(())).boxed()
    }))?;
    harness.resume()?;
    printer.write("answer: ");
    let poem = root
        .submit(
            InputSubmissionDraft {
                request_id: None,
                content: UserContent::Text("Write a long poem".to_owned()),
                when_busy: None,
            },
            context,
        )
        .await?;
    let settled_poem = poem.wait(context).await?;
    live_watch.stop().await;
    if let Some(answer) = settled_poem.state.answer() {
        // The last throttle window may not have been committed as a partial; the answer entry has the rest.
        let entry = root
            .commit(
                move |tx| async move { tx.typed_entry(&ASSISTANT_ENTRY, answer).await },
                context,
            )
            .await?;
        if let Some(Message::Assistant(message)) = entry
            .as_ref()
            .and_then(|entry| entry.entry().model.as_ref())
            .and_then(|model| model.first())
        {
            let text = message.content.iter().find_map(|content| match content {
                AssistantContentBlock::Text(text) => Some(text.text.as_str()),
                AssistantContentBlock::Thinking(_) | AssistantContentBlock::ToolCall(_) => None,
            });
            if let Some(text) = text {
                printer.print_text(text);
            }
        }
        printer.write("\n");
    } else {
        let reason = settled_poem.state.reason().unwrap_or_default();
        let detail = settled_poem
            .state
            .detail()
            .map_or_else(|| "undefined".to_owned(), DurableJson::to_string);
        printer.write(&format!("unanswered: {reason} {detail}\n"));
    }
    harness.close(context).await?;
    Ok(())
}
