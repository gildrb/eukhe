//! Reload extension code through the registry.
//! Run from the workspace:
//!   cargo run -p eukhe-durable --example 10-registry-reload
use std::io::Write;
use std::sync::Arc;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_durable::harness::define::{define_extension, define_tool, wrap_tool};
use eukhe_durable::harness::registry::create_registry;
use eukhe_durable::harness::types::{
    Extension, HarnessOptions, ToolExecutionResult, ToolRegistration,
};
use eukhe_durable::harness::{Conversation, Harness, RootOptions};
use eukhe_durable::storage::MemoryStorage;
use eukhe_pi_ai::models::{create_models, CreateModelsOptions};
use eukhe_pi_ai::typebox::Type;
use eukhe_types::pi_ai::{TextContent, UserContentBlock};

type BoxError = Box<dyn std::error::Error + Send + Sync>;

#[tokio::main]
async fn main() -> Result<(), BoxError> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let key = std::env::var("OPENAI_API_KEY").ok();
    run(&mut std::io::stdout(), &args, key.as_deref()).await
}

fn example_tool(name: &str, description: &str) -> Arc<ToolRegistration> {
    let tool_name = name.to_owned();
    define_tool(ToolRegistration::new(
        name,
        description,
        Type::object([("path", Type::string())]),
        move |args, _api, _cx| {
            let path = args
                .get("path")
                .and_then(|path| path.as_str())
                .unwrap_or_default()
                .to_owned();
            let text = format!("{tool_name} {path}");
            async move {
                Ok(ToolExecutionResult {
                    content: Some(vec![UserContentBlock::Text(TextContent::new(text))]),
                    ..ToolExecutionResult::default()
                })
            }
        },
    ))
}

fn files(tools: Vec<Arc<ToolRegistration>>) -> Arc<Extension> {
    define_extension(Extension {
        tools,
        ..Extension::named("files")
    })
}

/// The root agent's tools as `name: description`, JSON-encoded.
async fn tools(root: &Conversation) -> Result<String, BoxError> {
    let agent = root.agent(&BACKGROUND_CONTEXT).await?;
    let described: Vec<String> = agent
        .tools
        .iter()
        .map(|tool| format!("{}: {}", tool.name, tool.description))
        .collect();
    Ok(serde_json::to_string(&described)?)
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
    let context = &*BACKGROUND_CONTEXT;
    let read = example_tool("read", "Read a file");
    let registry = create_registry();
    registry.install(files(vec![
        Arc::clone(&read),
        example_tool("grep", "Search files"),
    ]))?;
    let harness = Harness::open(
        Arc::new(MemoryStorage::new()),
        HarnessOptions::new(
            create_models(CreateModelsOptions::default()),
            Arc::new(registry.clone()),
        ),
        context,
    )
    .await?;
    let root = harness.root(RootOptions::default(), context).await?;

    // Reloading is installing a new object with the same name: it replaces
    // the old one in place, in one publication, so no conversation ever sees
    // it missing. A task phase that already started keeps the snapshot it
    // took; the next phase uses the new code.
    registry.install(files(vec![
        Arc::clone(&read),
        example_tool("grep", "Search files, faster"),
    ]))?;
    writeln!(out, "after reload: {}", tools(&root).await?)?;

    // Another extension may wrap a tool by name. The wrap applies where the
    // wrapping extension is selected, and survives reloads of the wrapped
    // tool.
    let audit = define_extension(Extension {
        wraps: vec![wrap_tool(&read, |tool| {
            Ok(Arc::new(ToolRegistration {
                description: format!("{} (audited)", tool.description),
                ..ToolRegistration::clone(tool)
            }))
        })],
        ..Extension::named("audit")
    });
    registry.install(Arc::clone(&audit))?;
    writeln!(out, "with audit: {}", tools(&root).await?)?;

    // Uninstall removes an extension by name; conversations that select it
    // stop getting its code.
    registry.uninstall(&audit);
    writeln!(out, "after uninstall: {}", tools(&root).await?)?;

    harness.close(context).await?;
    Ok(())
}
