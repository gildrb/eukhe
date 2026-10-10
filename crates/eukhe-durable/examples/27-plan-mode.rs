//! Plan mode: the user switches a conversation into a read-only planning mode, the agent writes a plan into the
//! extension's own document, and switching back restores the full tool set.
//! Run:
//!   cargo run -p eukhe-durable --example 27-plan-mode
use std::collections::BTreeMap;
use std::io::Write;
use std::sync::Arc;

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_chord::json::JsonValue;
use eukhe_durable::documents::{DocDefinition, RewindableConversationDoc};
use eukhe_durable::env::{ExecutionEnv, NativeExecutionEnv, NativeExecutionEnvOptions};
use eukhe_durable::harness::define::{define_extension, define_tool, section};
use eukhe_durable::harness::registry::create_registry;
use eukhe_durable::harness::types::{
    AgentChange, EnvFactory, Extension, ExtensionsChange, FieldChange, HarnessOptions,
    HarnessSettings, InputSubmissionDraft, LiveSettings, ModelRef, ToolControl,
    ToolExecutionApiExt, ToolExecutionResult, ToolRegistration, ToolsChange,
};
use eukhe_durable::harness::{Conversation, Harness, RootOptions};
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::tools::{create_read_tool, ReadToolOptions, CODING_TOOLS};
use eukhe_durable::types::{DocumentReaderExt, RewindableFork};
use eukhe_pi_ai::models::{create_models, CreateModelsOptions};
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_provider, faux_tool_call, FauxAssistantMessageOptions,
    FauxResponseStep, RegisterFauxProviderOptions,
};
use eukhe_pi_ai::typebox::Type;
use eukhe_types::pi_ai::{Message, StopReason, TextContent, UserContentBlock};
use futures::FutureExt;

type BoxError = Box<dyn std::error::Error + Send + Sync>;

#[tokio::main]
async fn main() -> Result<(), BoxError> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let key = std::env::var("OPENAI_API_KEY").ok();
    run(&mut std::io::stdout(), &args, key.as_deref()).await
}

// ─── Product code: the plan extension ───────────────────────────────────────

// The current plan of a conversation: `{ steps: string[] }`. A fork keeps the plan it had at the fork entry.
const PLAN_DOC: RewindableConversationDoc<JsonValue> = match RewindableConversationDoc::define(
    DocDefinition {
        kind: "app.plan",
        version: 1,
        initial: || JsonValue::from(BTreeMap::from([("steps", JsonValue::array())])),
        migrate: None,
        checkpoint_when: None,
    },
    RewindableFork::AsOf,
) {
    Ok(token) => token,
    Err(_) => panic!("app.plan is a valid document definition"),
};

fn submit_plan() -> Arc<ToolRegistration> {
    define_tool(ToolRegistration::new(
        "submit_plan",
        "Submit the plan as a list of steps.",
        Type::object([("steps", Type::array(Type::string()))]),
        |args, api, cx| async move {
            let steps = JsonValue::from(&args["steps"]);
            let conversation_id = api.conversation_id();
            api.commit(
                move |tx| async move {
                    tx.doc(&PLAN_DOC, conversation_id)
                        .await?
                        .set("steps", steps)?;
                    Ok(())
                },
                &cx,
            )
            .await?;
            Ok(ToolExecutionResult {
                output: Some(vec![UserContentBlock::Text(TextContent::new(
                    "Plan submitted.",
                ))]),
                control: Some(ToolControl {
                    terminate: true,
                    ..ToolControl::default()
                }),
                ..ToolExecutionResult::default()
            })
        },
    ))
}

fn plan_extension(submit_plan: &Arc<ToolRegistration>) -> Arc<Extension> {
    define_extension(Extension {
        tools: vec![Arc::clone(submit_plan)],
        sections: vec![section(
            "plan_mode",
            |_, _| {
                async {
                    Ok(Some(
                        "You are in plan mode. Read the code, then call submit_plan. Change nothing."
                            .to_owned(),
                    ))
                }
                .boxed()
            },
            None,
        )],
        ..Extension::named("plan")
    })
}

// ─── Host setup ─────────────────────────────────────────────────────────────

fn tool_use(name: &str, arguments: serde_json::Value) -> FauxResponseStep {
    let arguments = match arguments {
        serde_json::Value::Object(arguments) => arguments,
        _ => serde_json::Map::new(),
    };
    faux_assistant_message(
        faux_tool_call(name, arguments, None),
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::ToolUse),
            ..FauxAssistantMessageOptions::default()
        },
    )
    .into()
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
    let submit_plan = submit_plan();
    let plan = plan_extension(&submit_plan);

    // Plan mode is a change to the conversation's agent: select the plan extension and offer only reading and
    // submitting. Clearing both returns to the host's default selection and every tool.
    let read = create_read_tool(ReadToolOptions::default());
    let enter_plan_mode = AgentChange {
        extensions: FieldChange::Set(ExtensionsChange::Edit {
            add: Some(vec![Arc::clone(&plan)]),
            remove: None,
        }),
        tools: FieldChange::Set(ToolsChange::Exactly(vec![read, Arc::clone(&submit_plan)])),
        ..AgentChange::default()
    };
    let leave_plan_mode = AgentChange {
        extensions: FieldChange::Clear,
        tools: FieldChange::Clear,
        ..AgentChange::default()
    };

    let directory = tempfile::Builder::new()
        .prefix("pi-durable-plan-")
        .tempdir()?;
    std::fs::write(directory.path().join("server.ts"), "app.listen(3000);\n")?;
    let cwd = directory
        .path()
        .to_str()
        .ok_or("the temp directory path is UTF-8")?
        .to_owned();

    let faux = faux_provider(RegisterFauxProviderOptions::default());
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(faux.provider.clone());
    faux.set_responses(vec![
        tool_use("read", serde_json::json!({ "path": "server.ts" })),
        tool_use(
            "submit_plan",
            serde_json::json!({ "steps": ["Read PORT from the environment", "Default to 3000"] }),
        ),
        faux_assistant_message(
            "Implementing step 1.",
            FauxAssistantMessageOptions::default(),
        )
        .into(),
    ]);

    let registry = create_registry();
    registry.install(Arc::clone(&CODING_TOOLS))?;
    registry.install(Arc::clone(&plan))?;
    let env: EnvFactory = Arc::new(move |_, _| {
        let env: Arc<dyn ExecutionEnv> =
            Arc::new(NativeExecutionEnv::new(NativeExecutionEnvOptions {
                cwd: cwd.clone(),
                ..NativeExecutionEnvOptions::default()
            }));
        async move { Ok(Some(env)) }.boxed()
    });
    let mut options = HarnessOptions::new(models, Arc::new(registry));
    // Installed, but only CodingTools is selected by default: conversations opt into plan mode.
    options.settings = Some(Arc::new(LiveSettings::new(HarnessSettings {
        extensions: Some(vec![Arc::clone(&CODING_TOOLS)]),
        ..HarnessSettings::default()
    })));
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
                    ..AgentChange::default()
                }),
                ..RootOptions::default()
            },
            cx,
        )
        .await?;
    writeln!(out, "tools: {}", tools(&root, cx).await?)?;

    root.configure(enter_plan_mode, cx).await?;
    writeln!(out, "plan mode tools: {}", tools(&root, cx).await?)?;
    root.submit(InputSubmissionDraft::new("Make the port configurable."), cx)
        .await?
        .wait(cx)
        .await?;
    let plan_doc = harness.snapshot(&PLAN_DOC, root.id(), cx).await?;
    let steps = plan_doc
        .as_ref()
        .and_then(|plan| plan.get("steps"))
        .map(serde_json::Value::from);
    writeln!(
        out,
        "plan: {}",
        steps.map_or_else(|| "undefined".to_owned(), |steps| steps.to_string())
    )?;

    root.configure(leave_plan_mode, cx).await?;
    writeln!(out, "tools again: {}", tools(&root, cx).await?)?;
    root.submit(InputSubmissionDraft::new("Go ahead."), cx)
        .await?
        .wait(cx)
        .await?;

    // The model saw each switch as a system prompt change in its transcript.
    let view = root
        .context(cx, eukhe_durable::harness::types::ContextOptions::default())
        .await?;
    for message in &view.messages {
        let Message::System(message) = message else {
            continue;
        };
        // A null section value removes it; absent fields print nothing, as `undefined` in JSON.
        let mut shown = serde_json::Map::new();
        if let Some(sections) = &message.sections {
            shown.insert("sections".to_owned(), serde_json::to_value(sections)?);
        }
        if let Some(added) = &message.tools_added {
            let names: Vec<&str> = added.iter().map(|tool| tool.name.as_str()).collect();
            shown.insert("added".to_owned(), serde_json::to_value(names)?);
        }
        if let Some(removed) = &message.tools_removed {
            let names: Vec<&str> = removed.iter().map(|tool| tool.name.as_str()).collect();
            shown.insert("removed".to_owned(), serde_json::to_value(names)?);
        }
        writeln!(out, "system: {}", serde_json::Value::Object(shown))?;
    }

    harness.close(cx).await?;
    directory.close()?;
    Ok(())
}
