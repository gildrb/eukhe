//! Reload an extension while a call runs, then restart the process. Running work finishes on the code it started
//! with; stored choices are names, so they survive a restart and bind to whatever code the new process installs.
//! Run:
//!   cargo run -p eukhe-durable --example 31-reload-and-restart
use std::io::Write;
use std::path::Path;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::entries::TOOL_RESULT_ENTRY;
use eukhe_durable::harness::define::{define_extension, define_tool};
use eukhe_durable::harness::registry::{create_registry, Registry};
use eukhe_durable::harness::types::{
    AgentChange, Extension, ExtensionsChange, FieldChange, HarnessOptions, InputSubmissionDraft,
    ModelRef, ToolExecutionResult, ToolRegistration,
};
use eukhe_durable::harness::{Conversation, ConversationEntryQuery, Harness, RootOptions};
use eukhe_durable::storage::sqlite::{open_native_sqlite_storage, NativeSqliteStorageOptions};
use eukhe_pi_ai::models::{create_models, CreateModelsOptions, Models};
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_provider, faux_tool_call, FauxAssistantMessageOptions,
    FauxResponseStep, RegisterFauxProviderOptions,
};
use eukhe_pi_ai::typebox::{TSchema, Type};
use eukhe_types::pi_ai::{Message, StopReason, TextContent, UserContentBlock};
use tokio::sync::{oneshot, watch};

type BoxError = Box<dyn std::error::Error + Send + Sync>;

#[tokio::main]
async fn main() -> Result<(), BoxError> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let key = std::env::var("OPENAI_API_KEY").ok();
    run(&mut std::io::stdout(), &args, key.as_deref()).await
}

/// What a running `version` call reports to and waits on.
struct Gate {
    /// Resolved when the next call starts.
    started: Mutex<Option<oneshot::Sender<()>>>,
    /// Calls finish once this is `true`.
    open: watch::Sender<bool>,
}

// Stand-in for code loaded from disk: each call builds the extension as the file currently reads.
fn load_versioned(version: &str, gate: &Arc<Gate>) -> Arc<Extension> {
    let version = version.to_owned();
    let gate = Arc::clone(gate);
    define_extension(Extension {
        tools: vec![define_tool(ToolRegistration::new(
            "version",
            "Report the tool's code version",
            Type::object(Vec::<(String, TSchema)>::new()),
            move |_, _, _| {
                if let Some(started) = gate
                    .started
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .take()
                {
                    // The example may have stopped waiting; the call goes on either way.
                    let _ = started.send(());
                }
                let mut open = gate.open.subscribe();
                let version = version.clone();
                async move {
                    // The sender lives in the gate, which this tool keeps.
                    let _ = open.wait_for(|open| *open).await;
                    Ok(ToolExecutionResult {
                        content: Some(vec![UserContentBlock::Text(TextContent::new(version))]),
                        ..ToolExecutionResult::default()
                    })
                }
            },
        ))],
        ..Extension::named("versioned")
    })
}

fn call_version() -> FauxResponseStep {
    faux_assistant_message(
        faux_tool_call("version", serde_json::Map::new(), None),
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

async fn open(
    directory: &Path,
    models: &Models,
    registry: &Registry,
    cx: &Context,
) -> Result<Harness, BoxError> {
    let storage = open_native_sqlite_storage(
        directory.join("session.sqlite"),
        NativeSqliteStorageOptions::default(),
    )
    .await?;
    let options = HarnessOptions::new(models.clone(), Arc::new(registry.clone()));
    Ok(Harness::open(Arc::new(storage), options, cx).await?)
}

async fn last_result(root: &Conversation, cx: &Context) -> Result<String, BoxError> {
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
            UserContentBlock::Text(text) => text.text.as_str(),
            UserContentBlock::Image(_) => "",
        })
        .collect())
}

async fn tools(root: &Conversation, cx: &Context) -> Result<String, BoxError> {
    let names: Vec<String> = root
        .agent(cx)
        .await?
        .tools
        .iter()
        .map(|tool| tool.name.clone())
        .collect();
    Ok(serde_json::to_string(&names)?)
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
    let gate = Arc::new(Gate {
        started: Mutex::new(None),
        open: watch::channel(true).0,
    });

    let faux = faux_provider(RegisterFauxProviderOptions::default());
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(faux.provider.clone());
    faux.set_responses(vec![call_version(), done(), call_version(), done()]);

    let directory = tempfile::Builder::new()
        .prefix("pi-durable-reload-")
        .tempdir()?;

    // First process.
    let registry = create_registry();
    registry.install(load_versioned("v1", &gate))?;
    let harness = open(directory.path(), &models, &registry, cx).await?;
    let root = harness
        .root(
            RootOptions {
                // Selected by name. The name is what is stored, never the code.
                agent: Some(AgentChange {
                    model: FieldChange::Set(ModelRef {
                        provider: "faux".to_owned(),
                        model_id: "faux-1".to_owned(),
                    }),
                    extensions: FieldChange::Set(ExtensionsChange::Exactly(vec![load_versioned(
                        "v1", &gate,
                    )])),
                    ..AgentChange::default()
                }),
                ..RootOptions::default()
            },
            cx,
        )
        .await?;

    // The file changes while a call runs: the running call finishes on v1, the next call uses v2.
    gate.open.send_replace(false);
    let (started, running) = oneshot::channel();
    *gate.started.lock().unwrap_or_else(PoisonError::into_inner) = Some(started);
    let submission = root
        .submit(InputSubmissionDraft::new("Which version?"), cx)
        .await?;
    running.await?;
    registry.install(load_versioned("v2", &gate))?;
    gate.open.send_replace(true);
    submission.wait(cx).await?;
    writeln!(
        out,
        "call running during the reload: {}",
        last_result(&root, cx).await?
    )?;
    root.submit(InputSubmissionDraft::new("And now?"), cx)
        .await?
        .wait(cx)
        .await?;
    writeln!(out, "next call: {}", last_result(&root, cx).await?)?;
    harness.close(cx).await?;

    // Second process: the conversation still selects "versioned", but this process has not installed it yet.
    let registry = create_registry();
    let harness = open(directory.path(), &models, &registry, cx).await?;
    let root = harness.root(RootOptions::default(), cx).await?;
    writeln!(
        out,
        "after restart, before install: {}",
        tools(&root, cx).await?
    )?;
    registry.install(load_versioned("v3", &gate))?;
    writeln!(out, "after install: {}", tools(&root, cx).await?)?;

    harness.close(cx).await?;
    directory.close()?;
    Ok(())
}
