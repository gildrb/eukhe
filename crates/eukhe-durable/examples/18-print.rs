//! Print mode: submit one prompt and print its answer, like `pi -p`. The host awaits its own Submission, not global
//! idle. Uses `OpenAI` when `OPENAI_API_KEY` is set, and a scripted faux model otherwise.
//! Run:
//!   cargo run -p eukhe-durable --example 18-print -- "What is in this directory?"
use std::io::Write;
use std::sync::Arc;

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::entries::ASSISTANT_ENTRY;
use eukhe_durable::env::{ExecutionEnv, NativeExecutionEnv, NativeExecutionEnvOptions};
use eukhe_durable::harness::define::{define_extension, section};
use eukhe_durable::harness::registry::create_registry;
use eukhe_durable::harness::types::{
    AgentChange, EnvFactory, Extension, FieldChange, HarnessOptions, InputSubmissionDraft, ModelRef,
};
use eukhe_durable::harness::{Harness, RootOptions};
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::tools::{create_bash_tool, create_read_tool, BashToolOptions, ReadToolOptions};
use eukhe_durable::types::SubmissionStatus;
use eukhe_pi_ai::models::{create_models, CreateModelsOptions};
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_provider, faux_text, faux_tool_call, FauxAssistantMessageOptions,
    RegisterFauxProviderOptions,
};
use eukhe_pi_ai::providers::openai::openai_provider;
use eukhe_types::pi_ai::{
    AssistantContentBlock, JsonObject, JsonValue, Message, StopReason, UserContent,
};
use futures::FutureExt;

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
/// Harness failures, and an unanswered prompt (TS `process.exitCode = 1`).
#[expect(
    clippy::too_many_lines,
    reason = "one example, step by step in the TS file's order"
)]
pub async fn run(
    out: &mut (dyn Write + Send),
    args: &[String],
    openai_api_key: Option<&str>,
) -> Result<(), BoxError> {
    let context = &*BACKGROUND_CONTEXT;
    let prompt = args
        .first()
        .map_or("What is in this directory?", String::as_str);

    let models = create_models(CreateModelsOptions::default());
    let mut model = ModelRef {
        provider: "openai".to_owned(),
        model_id: "gpt-6-sol".to_owned(),
    };
    if openai_api_key.is_some() {
        models.set_provider(openai_provider());
    } else {
        let faux = faux_provider(RegisterFauxProviderOptions::default());
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
    let harness = Harness::open(Arc::new(MemoryStorage::new()), options, context).await?;
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
    let settled = submission.wait(context).await?;
    if let Some(answer) = settled.state.answer() {
        let entry = root
            .commit(
                move |tx| async move { tx.typed_entry(&ASSISTANT_ENTRY, answer).await },
                context,
            )
            .await?;
        let text: String = match entry
            .as_ref()
            .and_then(|entry| entry.entry().model.as_ref())
            .and_then(|model| model.first())
        {
            Some(Message::Assistant(message)) => message
                .content
                .iter()
                .filter_map(|content| match content {
                    AssistantContentBlock::Text(text) => Some(text.text.as_str()),
                    AssistantContentBlock::Thinking(_) | AssistantContentBlock::ToolCall(_) => None,
                })
                .collect(),
            _ => String::new(),
        };
        writeln!(out, "{text}")?;
    } else {
        let status = settled.state.status();
        let detail = if status == SubmissionStatus::Unanswered {
            settled.state.reason().unwrap_or_default().to_owned()
        } else {
            format!("{status:?}")
        };
        harness.close(context).await?;
        return Err(format!("unanswered: {detail}").into());
    }
    harness.close(context).await?;
    Ok(())
}
