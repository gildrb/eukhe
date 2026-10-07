//! Replace a tool for some conversations, and decorate whichever tool wins: a bash that runs inside a Python
//! virtualenv, and a wrapper that times every bash call.
//! Run:
//!   cargo run -p eukhe-durable --example 30-tool-override
use std::io::Write;
use std::sync::{Arc, Mutex, PoisonError};
use std::time::Instant;

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::entries::TOOL_RESULT_ENTRY;
use eukhe_durable::env::{ExecutionEnv, NativeExecutionEnv, NativeExecutionEnvOptions};
use eukhe_durable::harness::define::{define_extension, wrap_tool};
use eukhe_durable::harness::registry::create_registry;
use eukhe_durable::harness::types::{
    AgentChange, ConversationCreateOptions, EnvFactory, Extension, ExtensionsChange, FieldChange,
    HarnessOptions, HarnessSettings, InputSubmissionDraft, LiveSettings, ModelRef,
    ToolRegistration,
};
use eukhe_durable::harness::{Conversation, ConversationEntryQuery, Harness, RootOptions};
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::tools::{create_bash_tool, BashToolOptions, CODING_TOOLS};
use eukhe_durable::types::ConversationOwnership;
use eukhe_pi_ai::models::{create_models, CreateModelsOptions};
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_provider, faux_tool_call, FauxAssistantMessageOptions,
    FauxResponseStep, RegisterFauxProviderOptions,
};
use eukhe_types::pi_ai::{Message, StopReason, UserContentBlock};
use futures::FutureExt;

type BoxError = Box<dyn std::error::Error + Send + Sync>;

#[tokio::main]
async fn main() -> Result<(), BoxError> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let key = std::env::var("OPENAI_API_KEY").ok();
    run(&mut std::io::stdout(), &args, key.as_deref()).await
}

// ─── Product code ───────────────────────────────────────────────────────────

// A bash with the same name: where selected after CodingTools, it replaces CodingTools' bash in place.
fn venv_extension() -> Arc<Extension> {
    define_extension(Extension {
        tools: vec![create_bash_tool(BashToolOptions {
            command_prefix: Some("source .venv/bin/activate".to_owned()),
            ..BashToolOptions::default()
        })],
        ..Extension::named("venv")
    })
}

// Wraps the bash that won, whichever it is. Wrappers never capture a base tool, so reloading either bash keeps it.
fn timing_extension(timings: &Arc<Mutex<Vec<u128>>>) -> Arc<Extension> {
    let timings = Arc::clone(timings);
    define_extension(Extension {
        wraps: vec![wrap_tool(
            &create_bash_tool(BashToolOptions::default()),
            move |bash| {
                let execute = Arc::clone(&bash.execute);
                let timings = Arc::clone(&timings);
                Ok(Arc::new(ToolRegistration {
                    execute: Arc::new(move |args, api, call_context| {
                        let start = Instant::now();
                        let executed = execute(args, api, call_context);
                        let timings = Arc::clone(&timings);
                        async move {
                            let result = executed.await;
                            timings
                                .lock()
                                .unwrap_or_else(PoisonError::into_inner)
                                .push(start.elapsed().as_millis());
                            result
                        }
                        .boxed()
                    }),
                    ..(**bash).clone()
                }))
            },
        )],
        ..Extension::named("timing")
    })
}

// ─── Host setup ─────────────────────────────────────────────────────────────

fn probe() -> FauxResponseStep {
    let mut arguments = serde_json::Map::new();
    arguments.insert("command".to_owned(), "echo venv: $VIRTUAL_ENV".into());
    faux_assistant_message(
        faux_tool_call("bash", arguments, None),
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::ToolUse),
            ..FauxAssistantMessageOptions::default()
        },
    )
    .into()
}

fn done() -> FauxResponseStep {
    faux_assistant_message("Done.", FauxAssistantMessageOptions::default()).into()
}

fn model() -> ModelRef {
    ModelRef {
        provider: "faux".to_owned(),
        model_id: "faux-1".to_owned(),
    }
}

async fn probe_bash(conversation: &Conversation, cx: &Context) -> Result<String, BoxError> {
    conversation
        .submit(InputSubmissionDraft::new("Which venv?"), cx)
        .await?
        .wait(cx)
        .await?;
    let page = conversation
        .entries(ConversationEntryQuery::default(), 10, None, cx)
        .await?;
    let result = page
        .items
        .iter()
        .find(|entry| TOOL_RESULT_ENTRY.is(Some(entry)))
        .and_then(|entry| entry.model.as_ref()?.first());
    let Some(Message::ToolResult(result)) = result else {
        return Err("no tool result".into());
    };
    Ok(result
        .content
        .iter()
        .map(|part| match part {
            UserContentBlock::Text(text) => text.text.trim(),
            UserContentBlock::Image(_) => "",
        })
        .collect())
}

/// Runs the example, writing what the TS example prints to `out`.
///
/// # Errors
///
/// The first step that fails.
pub async fn run(
    out: &mut (dyn Write + Send),
    _args: &[String],
    _openai_api_key: Option<&str>,
) -> Result<(), BoxError> {
    let cx: &Context = &BACKGROUND_CONTEXT;
    let timings = Arc::new(Mutex::new(Vec::new()));
    let venv = venv_extension();
    let timing = timing_extension(&timings);

    let directory = tempfile::Builder::new()
        .prefix("pi-durable-venv-")
        .tempdir()?;
    let project = directory
        .path()
        .to_str()
        .ok_or("the temp directory path is UTF-8")?
        .to_owned();
    std::fs::create_dir_all(directory.path().join(".venv/bin"))?;
    std::fs::write(
        directory.path().join(".venv/bin/activate"),
        format!("export VIRTUAL_ENV=\"{project}/.venv\"\n"),
    )?;

    let faux = faux_provider(RegisterFauxProviderOptions::default());
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(faux.provider.clone());
    faux.set_responses(vec![probe(), done(), probe(), done()]);

    let registry = create_registry();
    registry.install(Arc::clone(&CODING_TOOLS))?;
    registry.install(Arc::clone(&timing))?;
    registry.install(Arc::clone(&venv))?;
    let cwd = project.clone();
    let env: EnvFactory = Arc::new(move |_, _| {
        let env: Arc<dyn ExecutionEnv> =
            Arc::new(NativeExecutionEnv::new(NativeExecutionEnvOptions {
                cwd: cwd.clone(),
                ..NativeExecutionEnvOptions::default()
            }));
        async move { Ok(Some(env)) }.boxed()
    });
    let mut options = HarnessOptions::new(models, Arc::new(registry));
    // Venv is installed but not selected by default.
    options.settings = Some(Arc::new(LiveSettings::new(HarnessSettings {
        extensions: Some(vec![Arc::clone(&CODING_TOOLS), Arc::clone(&timing)]),
        ..HarnessSettings::default()
    })));
    options.env = Some(env);
    let harness = Harness::open(Arc::new(MemoryStorage::new()), options, cx).await?;
    let plain = harness
        .root(
            RootOptions {
                agent: Some(AgentChange {
                    model: FieldChange::Set(model()),
                    ..AgentChange::default()
                }),
                ..RootOptions::default()
            },
            cx,
        )
        .await?;
    let python = harness
        .create_conversation(
            ConversationCreateOptions {
                agent: Some(AgentChange {
                    model: FieldChange::Set(model()),
                    extensions: FieldChange::Set(ExtensionsChange::Edit {
                        add: Some(vec![Arc::clone(&venv)]),
                        remove: None,
                    }),
                    ..AgentChange::default()
                }),
                ..ConversationCreateOptions::new(ConversationOwnership::Ownerless)
            },
            cx,
        )
        .await?;

    writeln!(out, "plain conversation: {}", probe_bash(&plain, cx).await?)?;
    writeln!(
        out,
        "python conversation: {}",
        probe_bash(&python, cx)
            .await?
            .replacen(&project, "<project>", 1)
    )?;
    let timed = timings.lock().unwrap_or_else(PoisonError::into_inner).len();
    writeln!(out, "timed bash calls: {timed}")?;

    harness.close(cx).await?;
    directory.close()?;
    Ok(())
}
