//! A reviewer agent next to the main one: a cheaper model, a review role and loop, read-only tools, and its own
//! checkout of the project.
//! Run:
//!   cargo run -p eukhe-durable --example 28-reviewer
use std::io::Write;
use std::sync::Arc;

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::entries::ASSISTANT_ENTRY;
use eukhe_durable::env::{ExecutionEnv, NativeExecutionEnv, NativeExecutionEnvOptions};
use eukhe_durable::harness::define::{define_extension, hook, section};
use eukhe_durable::harness::registry::create_registry;
use eukhe_durable::harness::types::{
    AgentChange, ConversationCreateOptions, EnvFactory, Extension, ExtensionsChange, FieldChange,
    GenerationHooks, HarnessOptions, HarnessSettings, InputSubmissionDraft, LiveSettings, ModelRef,
    ToolsChange, YieldContinuation,
};
use eukhe_durable::harness::{ConversationEntryQuery, Harness, RootOptions, GENERATION_TASK};
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::tools::{create_read_tool, ReadToolOptions, CODING_TOOLS};
use eukhe_durable::types::ConversationOwnership;
use eukhe_pi_ai::models::{create_models, CreateModelsOptions};
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_provider, faux_tool_call, FauxAssistantMessageOptions,
    FauxModelDefinition, RegisterFauxProviderOptions,
};
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, Message, StopReason, UserContent,
};
use futures::FutureExt;

type BoxError = Box<dyn std::error::Error + Send + Sync>;

#[tokio::main]
async fn main() -> Result<(), BoxError> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let key = std::env::var("OPENAI_API_KEY").ok();
    run(&mut std::io::stdout(), &args, key.as_deref()).await
}

fn text_of(message: &AssistantMessage) -> String {
    message
        .content
        .iter()
        .filter_map(|part| match part {
            AssistantContentBlock::Text(text) => Some(text.text.as_str()),
            AssistantContentBlock::Thinking(_) | AssistantContentBlock::ToolCall(_) => None,
        })
        .collect()
}

// ─── Product code: the reviewer extension ───────────────────────────────────

const DONE: &str = "No further findings.";

// A role and a review loop: every answer that still has findings gets a second pass.
fn reviewer_extension() -> Arc<Extension> {
    define_extension(Extension {
        sections: vec![section(
            "role",
            |_, _| {
                async {
                    Ok(Some(
                        "You review diffs. Report problems as a list. Never edit files.".to_owned(),
                    ))
                }
                .boxed()
            },
            None,
        )],
        hooks: vec![hook(
            &GENERATION_TASK,
            GenerationHooks {
                on_yield: Some(Arc::new(|answer, _, _| {
                    let decision = if text_of(answer).contains(DONE) {
                        None
                    } else {
                        Some(YieldContinuation {
                            r#continue: UserContent::Text(format!(
                                "Look again for anything you missed. Say \"{DONE}\" when there is nothing left."
                            )),
                        })
                    };
                    async move { Ok(decision) }.boxed()
                })),
                ..GenerationHooks::default()
            },
        )],
        ..Extension::named("reviewer")
    })
}

// ─── Host setup ─────────────────────────────────────────────────────────────

fn model(model_id: &str) -> ModelRef {
    ModelRef {
        provider: "faux".to_owned(),
        model_id: model_id.to_owned(),
    }
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
    let reviewer_ext = reviewer_extension();

    // The reviewer works in its own checkout, in practice a `git worktree add`.
    let directory = tempfile::Builder::new()
        .prefix("pi-durable-review-")
        .tempdir()?;
    std::fs::write(
        directory.path().join("user.ts"),
        "export const name = (user) => user.name;\n",
    )?;
    let worktree = directory
        .path()
        .to_str()
        .ok_or("the temp directory path is UTF-8")?
        .to_owned();

    let faux = faux_provider(RegisterFauxProviderOptions {
        models: Some(vec![
            FauxModelDefinition::new("big"),
            FauxModelDefinition::new("small"),
        ]),
        ..RegisterFauxProviderOptions::default()
    });
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(faux.provider.clone());
    let mut read_args = serde_json::Map::new();
    read_args.insert("path".to_owned(), "user.ts".into());
    faux.set_responses(vec![
        faux_assistant_message(
            faux_tool_call("read", read_args, None),
            FauxAssistantMessageOptions {
                stop_reason: Some(StopReason::ToolUse),
                ..FauxAssistantMessageOptions::default()
            },
        )
        .into(),
        faux_assistant_message(
            "1. `name` does not handle a missing user.",
            FauxAssistantMessageOptions::default(),
        )
        .into(),
        faux_assistant_message(
            format!("2. `user` has no type. {DONE}"),
            FauxAssistantMessageOptions::default(),
        )
        .into(),
    ]);

    let registry = create_registry();
    registry.install(Arc::clone(&CODING_TOOLS))?;
    registry.install(Arc::clone(&reviewer_ext))?;
    let process_cwd = std::env::current_dir()?
        .to_str()
        .ok_or("the working directory path is UTF-8")?
        .to_owned();
    let env: EnvFactory = Arc::new(move |target, _| {
        let env: Arc<dyn ExecutionEnv> =
            Arc::new(NativeExecutionEnv::new(NativeExecutionEnvOptions {
                cwd: target.cwd.unwrap_or_else(|| process_cwd.clone()),
                ..NativeExecutionEnvOptions::default()
            }));
        async move { Ok(Some(env)) }.boxed()
    });
    let mut options = HarnessOptions::new(models, Arc::new(registry));
    // The main agent selects only CodingTools; the reviewer opts in.
    options.settings = Some(Arc::new(LiveSettings::new(HarnessSettings {
        extensions: Some(vec![Arc::clone(&CODING_TOOLS)]),
        ..HarnessSettings::default()
    })));
    options.env = Some(env);
    let harness = Harness::open(Arc::new(MemoryStorage::new()), options, cx).await?;
    harness
        .root(
            RootOptions {
                agent: Some(AgentChange {
                    model: FieldChange::Set(model("big")),
                    ..AgentChange::default()
                }),
                ..RootOptions::default()
            },
            cx,
        )
        .await?;

    // Everything the reviewer is, stored on its conversation: the model, exactly these extensions in this order,
    // only the read tool, and its directory. A restart keeps all of it.
    let reviewer = harness
        .create_conversation(
            ConversationCreateOptions {
                agent: Some(AgentChange {
                    model: FieldChange::Set(model("small")),
                    extensions: FieldChange::Set(ExtensionsChange::Exactly(vec![
                        Arc::clone(&CODING_TOOLS),
                        Arc::clone(&reviewer_ext),
                    ])),
                    tools: FieldChange::Set(ToolsChange::Exactly(vec![create_read_tool(
                        ReadToolOptions::default(),
                    )])),
                    cwd: FieldChange::Set(worktree.clone()),
                    ..AgentChange::default()
                }),
                ..ConversationCreateOptions::new(ConversationOwnership::Ownerless)
            },
            cx,
        )
        .await?;
    let agent = reviewer.agent(cx).await?;
    let extensions: Vec<&str> = agent
        .extensions
        .iter()
        .map(|extension| extension.name.as_str())
        .collect();
    let tools: Vec<&str> = agent.tools.iter().map(|tool| tool.name.as_str()).collect();
    writeln!(
        out,
        "reviewer: {} {} {} {}",
        agent
            .model
            .as_ref()
            .map_or("undefined", |model| model.model_id.as_str()),
        serde_json::to_string(&extensions)?,
        serde_json::to_string(&tools)?,
        agent.cwd.as_deref() == Some(worktree.as_str())
    )?;

    reviewer
        .submit(InputSubmissionDraft::new("Review user.ts."), cx)
        .await?
        .wait(cx)
        .await?;
    let page = reviewer
        .entries(ConversationEntryQuery::default(), 20, None, cx)
        .await?;
    for entry in page.items.iter().rev() {
        let message = entry.model.as_ref().and_then(|model| model.first());
        if let Some(Message::User(user)) = message {
            match &user.content {
                UserContent::Text(text) => writeln!(out, "> {text}")?,
                UserContent::Blocks(blocks) => {
                    writeln!(out, "> {}", serde_json::to_string(blocks)?)?;
                }
            }
        }
        if let Some(Message::Assistant(answer)) = message {
            if ASSISTANT_ENTRY.is(Some(entry)) && !text_of(answer).is_empty() {
                writeln!(out, "reviewer: {}", text_of(answer))?;
            }
        }
    }

    harness.close(cx).await?;
    directory.close()?;
    Ok(())
}
