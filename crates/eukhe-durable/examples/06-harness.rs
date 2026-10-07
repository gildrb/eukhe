//! Open a Harness with a registry of extensions.
//! Run: `cargo run -p eukhe-durable --example 06-harness`
use std::io::Write;
use std::sync::Arc;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_chord::json::{JsonObject, JsonValue};
use eukhe_durable::documents::{DocDefinition, RewindableConversationDoc};
use eukhe_durable::harness::agent::AGENT_DOC;
use eukhe_durable::harness::define::{define_extension, define_tool};
use eukhe_durable::harness::registry::create_registry;
use eukhe_durable::harness::types::{
    AgentChange, Extension, FieldChange, HarnessOptions, ToolExecutionResult, ToolRegistration,
};
use eukhe_durable::harness::{Harness, RootOptions};
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::types::{DocumentReaderExt, RewindableFork};
use eukhe_pi_ai::models::{create_models, CreateModelsOptions};
use eukhe_pi_ai::typebox::Type;
use eukhe_types::pi_ai::{ModelThinkingLevel, TextContent, UserContentBlock};
use futures::FutureExt;
use serde::{Deserialize, Serialize};

type BoxError = Box<dyn std::error::Error + Send + Sync>;

#[derive(Debug, Default, Serialize, Deserialize)]
struct Notes {
    text: String,
}

static NOTES: RewindableConversationDoc<Notes> = match RewindableConversationDoc::define(
    DocDefinition {
        kind: "example.notes",
        version: 1,
        initial: Notes::default,
        migrate: None,
        checkpoint_when: None,
    },
    RewindableFork::AsOf,
) {
    Ok(token) => token,
    Err(_) => panic!("valid definition"),
};

#[tokio::main]
async fn main() -> Result<(), BoxError> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let key = std::env::var("OPENAI_API_KEY").ok();
    run(&mut std::io::stdout(), &args, key.as_deref()).await
}

/// `console.log` of a document snapshot: its JSON, or `undefined` when absent.
fn show(value: Option<Arc<JsonObject>>) -> String {
    value.map_or_else(
        || "undefined".to_owned(),
        |object| JsonValue::Object(object).to_string(),
    )
}

/// A JSON array of names.
fn names<'a>(items: impl Iterator<Item = &'a str>) -> JsonValue {
    JsonValue::from(items.map(JsonValue::from).collect::<Vec<_>>())
}

/// Runs the example, writing what the TS example prints to `out`.
///
/// # Errors
/// Harness and output failures.
pub async fn run(
    out: &mut (dyn Write + Send),
    _args: &[String],
    _openai_api_key: Option<&str>,
) -> Result<(), BoxError> {
    let context = &*BACKGROUND_CONTEXT;

    // A Harness is a Session plus conversation handles and durable tasks. Extension
    // code (tools, prompt sections, hooks, tasks) comes in named extensions
    // installed in a registry the application owns. Nothing in the registry is
    // saved; it is this process's code.
    let read = define_tool(ToolRegistration::new(
        "read",
        "Read a file",
        Type::object([("path", Type::string())]),
        |args, _api, _cx| async move {
            let path = args
                .get("path")
                .and_then(|path| path.as_str())
                .unwrap_or_default();
            Ok(ToolExecutionResult {
                content: Some(vec![UserContentBlock::Text(TextContent::new(format!(
                    "contents of {path}"
                )))]),
                ..ToolExecutionResult::default()
            })
        },
    ));
    let files = define_extension(Extension {
        tools: vec![read],
        ..Extension::named("files")
    });
    let registry = create_registry();
    registry.install(files)?;

    // `models` is pi-ai's model access; generation calls models through it.
    let harness = Harness::open(
        Arc::new(MemoryStorage::new()),
        HarnessOptions::new(
            create_models(CreateModelsOptions::default()),
            Arc::new(registry.clone()),
        ),
        context,
    )
    .await?;

    // The root conversation always has ID 1. The first root() call creates it,
    // its built-in documents, the `agent` choices, and whatever `init` writes, all
    // in one commit. Later calls, including after a restart, return it and ignore
    // both options.
    let root = harness
        .root(
            RootOptions {
                agent: Some(AgentChange {
                    thinking_level: FieldChange::Set(ModelThinkingLevel::Low),
                    ..AgentChange::default()
                }),
                init: Some(Box::new(|tx, root_id| {
                    async move {
                        tx.doc(&NOTES, root_id).await?.set("text", "root notes")?;
                        Ok(())
                    }
                    .boxed()
                })),
            },
            context,
        )
        .await?;
    let root_notes = harness.snapshot(&NOTES, root.id(), context).await?;
    writeln!(out, "root: {} {}", root.id(), show(root_notes))?;
    // The stored choices are names; agent() resolves them against the registry.
    let stored = harness.snapshot(&AGENT_DOC, root.id(), context).await?;
    writeln!(out, "stored agent: {}", show(stored))?;
    let agent = root.agent(context).await?;
    writeln!(
        out,
        "resolved: {} {} {}",
        agent.thinking_level,
        names(
            agent
                .extensions
                .iter()
                .map(|extension| extension.name.as_str())
        ),
        names(agent.tools.iter().map(|tool| tool.name.as_str())),
    )?;

    harness.close(context).await?;
    Ok(())
}
