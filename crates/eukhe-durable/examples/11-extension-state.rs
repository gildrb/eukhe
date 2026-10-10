//! An extension that keeps its own per-conversation document.
//! Run from the workspace:
//!   cargo run -p eukhe-durable --example 11-extension-state
use std::io::Write;
use std::sync::Arc;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_chord::json::{from_json, JsonValue};
use eukhe_durable::documents::{DocDefinition, RewindableConversationDoc};
use eukhe_durable::harness::define::{define_extension, define_tool, section};
use eukhe_durable::harness::registry::create_registry;
use eukhe_durable::harness::types::{
    AgentChange, Extension, FieldChange, HarnessOptions, InputSubmissionDraft, ModelRef,
    ToolExecutionApiExt, ToolExecutionResult, ToolRegistration,
};
use eukhe_durable::harness::{Harness, RootOptions};
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::types::{DocumentReaderExt, RewindableFork};
use eukhe_pi_ai::models::{create_models, CreateModelsOptions};
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_provider, faux_tool_call, FauxAssistantMessageOptions,
    RegisterFauxProviderOptions,
};
use eukhe_pi_ai::typebox::Type;
use eukhe_types::pi_ai::{JsonObject, Message, StopReason, TextContent, UserContentBlock};
use futures::FutureExt;
use serde::{Deserialize, Serialize};

type BoxError = Box<dyn std::error::Error + Send + Sync>;

#[tokio::main]
async fn main() -> Result<(), BoxError> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let key = std::env::var("OPENAI_API_KEY").ok();
    run(&mut std::io::stdout(), &args, key.as_deref()).await
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
struct TodoList {
    items: Vec<String>,
}

// A todo list per conversation. Rewindable with `AsOf`, so a fork starts with
// the todos its parent had at the fork entry.
static TODOS: RewindableConversationDoc<TodoList> = match RewindableConversationDoc::define(
    DocDefinition {
        kind: "example.todos",
        version: 1,
        initial: TodoList::default,
        migrate: None,
        checkpoint_when: None,
    },
    RewindableFork::AsOf,
) {
    Ok(token) => token,
    Err(_) => panic!("example.todos has a valid version"),
};

// The tool writes the document; the section shows it to the model before
// every request. Nothing needs to create it up front: tx.doc() creates it on
// first write, and the section treats a missing document as an empty list.
fn todo_extension() -> Arc<Extension> {
    define_extension(Extension {
        tools: vec![define_tool(ToolRegistration::new(
            "todo",
            "Add an item to your todo list",
            Type::object([("item", Type::string())]),
            |args, api, cx| async move {
                let item = args
                    .get("item")
                    .and_then(|item| item.as_str())
                    .unwrap_or_default()
                    .to_owned();
                let conversation_id = api.conversation_id();
                let pushed = item.clone();
                api.commit(
                    move |tx| async move {
                        tx.doc(&TODOS, conversation_id)
                            .await?
                            .child("items")?
                            .push([JsonValue::from(pushed)])?;
                        Ok(())
                    },
                    &cx,
                )
                .await?;
                Ok(ToolExecutionResult {
                    output: Some(vec![UserContentBlock::Text(TextContent::new(format!(
                        "added {item}"
                    )))]),
                    ..ToolExecutionResult::default()
                })
            },
        ))],
        sections: vec![section(
            "todos",
            |input, render_context| {
                let snapshot = input
                    .read
                    .snapshot(&TODOS, input.conversation_id, render_context);
                async move {
                    let Some(todos) = snapshot.await? else {
                        return Ok(None);
                    };
                    let todos: TodoList = from_json(&JsonValue::Object(todos))?;
                    Ok((!todos.items.is_empty()).then(|| todos.items.join("\n")))
                }
                .boxed()
            },
            None,
        )],
        ..Extension::named("todo")
    })
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
    let faux = faux_provider(RegisterFauxProviderOptions::default());
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(faux.provider.clone());
    let registry = create_registry();
    registry.install(todo_extension())?;
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

    let mut arguments = JsonObject::new();
    arguments.insert("item".to_owned(), "fix the build".into());
    faux.set_responses(vec![
        faux_assistant_message(
            faux_tool_call("todo", arguments, None),
            FauxAssistantMessageOptions {
                stop_reason: Some(StopReason::ToolUse),
                ..FauxAssistantMessageOptions::default()
            },
        )
        .into(),
        faux_assistant_message("Noted.", FauxAssistantMessageOptions::default()).into(),
        faux_assistant_message("Working on it.", FauxAssistantMessageOptions::default()).into(),
    ]);
    root.submit(
        InputSubmissionDraft::new("Remember to fix the build."),
        context,
    )
    .await?
    .wait(context)
    .await?;
    let todos = harness.snapshot(&TODOS, root.id(), context).await?;
    writeln!(
        out,
        "todos: {}",
        todos.map_or_else(
            || "undefined".to_owned(),
            |todos| { JsonValue::Object(todos).to_string() }
        )
    )?;

    // The next request's system prompt carries the list. The first system
    // message only announced the todo tool; no section had text yet.
    root.submit(InputSubmissionDraft::new("What is next?"), context)
        .await?
        .wait(context)
        .await?;
    let messages = root
        .context(
            context,
            eukhe_durable::harness::types::ContextOptions::default(),
        )
        .await?
        .messages;
    let mut system = Vec::new();
    for message in &messages {
        let Message::System(message) = message else {
            continue;
        };
        // `undefined` fields are left out, as JSON drops them.
        let mut shown = serde_json::Map::new();
        if let Some(sections) = &message.sections {
            shown.insert("sections".to_owned(), serde_json::to_value(sections)?);
        }
        if let Some(tools) = &message.tools_added {
            let names: Vec<&str> = tools.iter().map(|tool| tool.name.as_str()).collect();
            shown.insert("toolsAdded".to_owned(), serde_json::to_value(names)?);
        }
        system.push(serde_json::Value::Object(shown));
    }
    writeln!(out, "system messages: {}", serde_json::to_string(&system)?)?;

    harness.close(context).await?;
    Ok(())
}
