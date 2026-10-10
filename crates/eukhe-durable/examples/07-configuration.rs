//! Per-conversation agent choices and Harness-wide settings.
//! Run: `cargo run -p eukhe-durable --example 07-configuration`
use std::io::Write;
use std::sync::Arc;

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_chord::json::{to_json, JsonObject, JsonValue};
use eukhe_durable::harness::agent::AGENT_DOC;
use eukhe_durable::harness::define::{define_extension, define_tool, section};
use eukhe_durable::harness::registry::create_registry;
use eukhe_durable::harness::types::{
    AgentChange, ConversationStreamOptions, Extension, ExtensionsChange, FieldChange,
    HarnessOptions, HarnessSettings, LiveSettings, ModelRef, PartialRetryPolicy, ToolExecutionMode,
    ToolExecutionResult, ToolRegistration, ToolsChange,
};
use eukhe_durable::harness::{Conversation, Harness, RootOptions};
use eukhe_durable::session::SessionResult;
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::types::DocumentReaderExt;
use eukhe_pi_ai::models::{create_models, CreateModelsOptions};
use eukhe_pi_ai::typebox::Type;
use eukhe_types::pi_ai::{ModelThinkingLevel, TextContent, UserContentBlock};
use futures::FutureExt;

type BoxError = Box<dyn std::error::Error + Send + Sync>;

/// Apps may attach their own metadata to tools, such as a prompt snippet
/// (TS `AppTool = ToolRegistration & { snippet?: string }`); Rust carries it
/// as the registration's `extra`.
struct Snippet(String);

fn example_tool(name: &str, description: &str) -> Arc<ToolRegistration> {
    let label = name.to_owned();
    define_tool(
        ToolRegistration::new(
            name,
            description,
            Type::object([("path", Type::string())]),
            move |args, _api, _cx| {
                let label = label.clone();
                async move {
                    let path = args
                        .get("path")
                        .and_then(|path| path.as_str())
                        .unwrap_or_default();
                    Ok(ToolExecutionResult {
                        output: Some(vec![UserContentBlock::Text(TextContent::new(format!(
                            "{label} {path}"
                        )))]),
                        ..ToolExecutionResult::default()
                    })
                }
            },
        )
        .with_extra(Snippet(format!("Use {name} for files."))),
    )
}

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

/// The names of the tools a request offers now, as a JSON array.
async fn tools(root: &Conversation, context: &Context) -> SessionResult<JsonValue> {
    let agent = root.agent(context).await?;
    Ok(JsonValue::from(
        agent
            .tools
            .iter()
            .map(|tool| JsonValue::from(tool.name.as_str()))
            .collect::<Vec<_>>(),
    ))
}

fn stream(timeout_ms: f64) -> ConversationStreamOptions {
    ConversationStreamOptions {
        timeout_ms: Some(timeout_ms),
        ..ConversationStreamOptions::default()
    }
}

/// Sections see the offered tools, so one can render their snippets.
fn snippets_extension() -> Arc<Extension> {
    define_extension(Extension {
        sections: vec![section(
            "tool_snippets",
            |input, _cx| {
                let text = input
                    .agent
                    .tools
                    .iter()
                    .map(|tool| {
                        tool.extra::<Snippet>()
                            .map_or("", |snippet| snippet.0.as_str())
                    })
                    .collect::<Vec<_>>()
                    .join("\n");
                async move { Ok(Some(text)) }.boxed()
            },
            None,
        )],
        ..Extension::named("snippets")
    })
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

    let read = example_tool("read", "Read a file");
    let write = example_tool("write", "Write a file");
    let grep = example_tool("grep", "Search files");
    let files = define_extension(Extension {
        tools: vec![Arc::clone(&read), Arc::clone(&write)],
        ..Extension::named("files")
    });
    let search = define_extension(Extension {
        tools: vec![grep],
        ..Extension::named("search")
    });
    let snippets = snippets_extension();

    let registry = create_registry();
    registry.install(Arc::clone(&files))?;
    registry.install(Arc::clone(&search))?;
    registry.install(snippets)?;

    // Settings are Harness-wide run policy, read at every use and never stored.
    // A live source makes a value changeable, such as one backed by the app's
    // settings file.
    let settings = Arc::new(LiveSettings::new(HarnessSettings {
        stream: Some(stream(60_000.0)),
        retry: Some(PartialRetryPolicy {
            max_retries: Some(5),
            ..PartialRetryPolicy::default()
        }),
        tool_execution: Some(ToolExecutionMode::Sequential),
        ..HarnessSettings::default()
    }));
    let mut options = HarnessOptions::new(
        create_models(CreateModelsOptions::default()),
        Arc::new(registry.clone()),
    );
    options.settings = Some(Arc::clone(&settings) as _);
    let harness = Harness::open(Arc::new(MemoryStorage::new()), options, context).await?;
    let root = harness.root(RootOptions::default(), context).await?;

    // A new conversation stores no choices and follows the host: every installed
    // extension, all of their tools.
    writeln!(out, "default tools: {}", tools(&root, context).await?)?;

    // configure() stores choices in the conversation's pi.agent document, one
    // commit per call. Extensions and tools are passed as objects and stored by
    // name, so a typo cannot slip in.
    root.configure(
        AgentChange {
            model: FieldChange::Set(ModelRef {
                provider: "anthropic".to_owned(),
                model_id: "claude-sonnet-4-5".to_owned(),
            }),
            thinking_level: FieldChange::Set(ModelThinkingLevel::High),
            tools: FieldChange::Set(ToolsChange::Exactly(vec![write, read])),
            ..AgentChange::default()
        },
        context,
    )
    .await?;
    let stored = harness.snapshot(&AGENT_DOC, root.id(), context).await?;
    writeln!(out, "stored: {}", show(stored))?;
    let agent = root.agent(context).await?;
    let model = agent.model.as_ref().map(to_json).transpose()?;
    writeln!(
        out,
        "model: {} thinking: {} tools: {}",
        model.map_or_else(|| "undefined".to_owned(), |model| model.to_string()),
        agent.thinking_level,
        tools(&root, context).await?
    )?;

    // Deselect an extension; `Clear` clears a stored field back to the host default.
    root.configure(
        AgentChange {
            extensions: FieldChange::Set(ExtensionsChange::Edit {
                add: None,
                remove: Some(vec![Arc::clone(&search)]),
            }),
            tools: FieldChange::Clear,
            ..AgentChange::default()
        },
        context,
    )
    .await?;
    writeln!(out, "without search: {}", tools(&root, context).await?)?;

    // Stored names outlive the code. The conversation selects exactly these two
    // extensions; uninstalling "files" leaves it selected, and requests just stop
    // offering its tools until it is back.
    root.configure(
        AgentChange {
            extensions: FieldChange::Set(ExtensionsChange::Exactly(vec![
                Arc::clone(&files),
                search,
            ])),
            ..AgentChange::default()
        },
        context,
    )
    .await?;
    registry.uninstall(&files);
    writeln!(out, "files uninstalled: {}", tools(&root, context).await?)?;
    registry.install(files)?;
    writeln!(out, "files reinstalled: {}", tools(&root, context).await?)?;

    // Settings changes need no commit; the next request uses the new timeout.
    settings.update(|settings| settings.stream = Some(stream(120_000.0)));

    harness.close(context).await?;
    Ok(())
}
