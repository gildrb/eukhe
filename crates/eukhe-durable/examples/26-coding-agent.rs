//! A small coding agent: the built-in coding tools, a prompt that knows the working directory, settings backed by the
//! app's settings file, and an environment that follows the conversation's directory.
//! Run:
//!   cargo run -p eukhe-durable --example 26-coding-agent
use std::io::Write;
use std::sync::atomic::{AtomicBool, AtomicU32, Ordering};
use std::sync::Arc;

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::entries::TOOL_RESULT_ENTRY;
use eukhe_durable::env::{ExecutionEnv, NativeExecutionEnv, NativeExecutionEnvOptions};
use eukhe_durable::harness::define::{define_extension, section};
use eukhe_durable::harness::registry::create_registry;
use eukhe_durable::harness::types::{
    AgentChange, EnvFactory, Extension, FieldChange, HarnessOptions, HarnessSettings,
    HarnessSettingsSource, InputSubmissionDraft, ModelRef, PartialRetryPolicy, ToolExecutionMode,
};
use eukhe_durable::harness::{Conversation, ConversationEntryQuery, Harness, RootOptions};
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::tools::CODING_TOOLS;
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

/// Settings the user edits while the agent runs, like a settings.json the app watches. Every Harness read calls
/// `current()` and sees the current file; nothing is copied or stored.
struct UserSettings {
    parallel_tools: AtomicBool,
    max_retries: AtomicU32,
}

impl HarnessSettingsSource for UserSettings {
    fn current(&self) -> Arc<HarnessSettings> {
        Arc::new(HarnessSettings {
            tool_execution: Some(if self.parallel_tools.load(Ordering::SeqCst) {
                ToolExecutionMode::Parallel
            } else {
                ToolExecutionMode::Sequential
            }),
            retry: Some(PartialRetryPolicy {
                max_retries: Some(self.max_retries.load(Ordering::SeqCst)),
                ..PartialRetryPolicy::default()
            }),
            ..HarnessSettings::default()
        })
    }
}

fn pwd() -> FauxResponseStep {
    let mut arguments = serde_json::Map::new();
    arguments.insert("command".to_owned(), "pwd".into());
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

async fn last_bash_output(root: &Conversation, cx: &Context) -> Result<String, BoxError> {
    let page = root
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
#[expect(
    clippy::too_many_lines,
    reason = "the TS example's steps, in order, in one function"
)]
pub async fn run(
    out: &mut (dyn Write + Send),
    _args: &[String],
    _openai_api_key: Option<&str>,
) -> Result<(), BoxError> {
    let cx: &Context = &BACKGROUND_CONTEXT;
    let directory = tempfile::Builder::new()
        .prefix("pi-durable-agent-")
        .tempdir()?;
    let workspace = directory
        .path()
        .to_str()
        .ok_or("the temp directory path is UTF-8")?
        .to_owned();
    std::fs::create_dir(directory.path().join("app"))?;

    // The app's own prompt, next to the coding tools.
    let coding = define_extension(Extension {
        sections: vec![
            section(
                "preamble",
                |_, _| {
                    async {
                        Ok(Some(
                            "You are a coding agent. Use the tools to inspect the project."
                                .to_owned(),
                        ))
                    }
                    .boxed()
                },
                Some(false),
            ),
            section(
                "cwd",
                |input, _| {
                    let cwd = input.env.as_ref().map(|env| env.cwd().to_owned());
                    async move { Ok(cwd) }.boxed()
                },
                None,
            ),
        ],
        ..Extension::named("coding")
    });
    let registry = create_registry();
    registry.install(Arc::clone(&CODING_TOOLS))?;
    registry.install(coding)?;

    let user_settings = Arc::new(UserSettings {
        parallel_tools: AtomicBool::new(true),
        max_retries: AtomicU32::new(3),
    });

    // The Harness calls this for every tool call and request with the conversation's `cwd`, so changing a
    // conversation's directory needs no restart.
    let default_cwd = workspace.clone();
    let env: EnvFactory = Arc::new(move |target, _| {
        let cwd = target.cwd.unwrap_or_else(|| default_cwd.clone());
        let env: Arc<dyn ExecutionEnv> =
            Arc::new(NativeExecutionEnv::new(NativeExecutionEnvOptions {
                cwd,
                ..NativeExecutionEnvOptions::default()
            }));
        async move { Ok(Some(env)) }.boxed()
    });

    let faux = faux_provider(RegisterFauxProviderOptions::default());
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(faux.provider.clone());
    faux.set_responses(vec![pwd(), done(), pwd(), done()]);

    let mut options = HarnessOptions::new(models, Arc::new(registry));
    options.settings = Some(Arc::clone(&user_settings) as _);
    options.env = Some(env);
    let harness = Harness::open(Arc::new(MemoryStorage::new()), options, cx).await?;
    let root = harness
        .root(
            RootOptions {
                agent: Some(AgentChange {
                    model: FieldChange::Set(ModelRef {
                        provider: "faux".to_owned(),
                        model_id: "faux-1".to_owned(),
                    }),
                    cwd: FieldChange::Set(workspace.clone()),
                    ..AgentChange::default()
                }),
                ..RootOptions::default()
            },
            cx,
        )
        .await?;

    root.submit(InputSubmissionDraft::new("Where are we?"), cx)
        .await?
        .wait(cx)
        .await?;
    writeln!(out, "bash ran in: {}", last_bash_output(&root, cx).await?)?;

    // The user switches the project directory and turns off parallel tools. Both apply from the next use.
    root.configure(
        AgentChange {
            cwd: FieldChange::Set(format!("{workspace}/app")),
            ..AgentChange::default()
        },
        cx,
    )
    .await?;
    user_settings.parallel_tools.store(false, Ordering::SeqCst);
    root.submit(InputSubmissionDraft::new("And now?"), cx)
        .await?
        .wait(cx)
        .await?;
    writeln!(out, "bash ran in: {}", last_bash_output(&root, cx).await?)?;

    harness.close(cx).await?;
    directory.close()?;
    Ok(())
}
