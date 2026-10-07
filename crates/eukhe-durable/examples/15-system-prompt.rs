//! System prompt sections and per-conversation instructions.
//! Run from the workspace:
//!   cargo run -p eukhe-durable --example 15-system-prompt
use std::io::Write;
use std::sync::Arc;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_durable::entries::SYSTEM_ENTRY;
use eukhe_durable::env::{ExecutionEnv, NativeExecutionEnv, NativeExecutionEnvOptions};
use eukhe_durable::harness::define::{define_extension, section, wrap_section};
use eukhe_durable::harness::registry::create_registry;
use eukhe_durable::harness::types::{
    AgentChange, ConversationCreateOptions, EnvFactory, Extension, ExtensionsChange, FieldChange,
    HarnessOptions, InputSubmissionDraft, ModelRef, PromptSection,
};
use eukhe_durable::harness::{Conversation, ConversationEntryQuery, Harness, RootOptions};
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::types::ConversationOwnership;
use eukhe_pi_ai::models::{create_models, CreateModelsOptions};
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_provider, FauxAssistantMessageOptions, RegisterFauxProviderOptions,
};
use eukhe_types::pi_ai::Message;
use futures::future::ready;
use futures::FutureExt;

type BoxError = Box<dyn std::error::Error + Send + Sync>;

#[tokio::main]
async fn main() -> Result<(), BoxError> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let key = std::env::var("OPENAI_API_KEY").ok();
    run(&mut std::io::stdout(), &args, key.as_deref()).await
}

/// The `pi.system` messages of a conversation, oldest first, JSON-encoded.
async fn system_entries(conversation: &Conversation) -> Result<String, BoxError> {
    let page = conversation
        .entries(
            ConversationEntryQuery::default(),
            20,
            None,
            &BACKGROUND_CONTEXT,
        )
        .await?;
    let messages: Vec<Message> = page
        .items
        .into_iter()
        .rev()
        .filter(|entry| SYSTEM_ENTRY.is(Some(entry)))
        .flat_map(|entry| entry.model.unwrap_or_default())
        .collect();
    Ok(serde_json::to_string(&messages)?)
}

fn faux_model() -> ModelRef {
    ModelRef {
        provider: "faux".to_owned(),
        model_id: "faux-1".to_owned(),
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
    let context = &*BACKGROUND_CONTEXT;
    let faux = faux_provider(RegisterFauxProviderOptions::default());
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(faux.provider.clone());
    faux.set_responses(
        ["Done.", "Done.", "Done."]
            .into_iter()
            .map(|text| faux_assistant_message(text, FauxAssistantMessageOptions::default()).into())
            .collect(),
    );

    // Pico stores no prompt state. Before each model request, the sections of
    // the conversation's selected extensions render the desired prompt, and
    // only the difference to what the model already saw is appended to the
    // transcript as a `pi.system` entry.
    let coding = define_extension(Extension {
        sections: vec![
            // `Some(false)` sends the text as is; by default it is wrapped in
            // <key>...</key>.
            section(
                "preamble",
                |_, _| ready(Ok(Some("You are a coding agent.".to_owned()))).boxed(),
                Some(false),
            ),
            // Sections see the environment built for this request, here its
            // working directory.
            section(
                "cwd",
                |input, _| ready(Ok(input.env.as_ref().map(|env| env.cwd().to_owned()))).boxed(),
                None,
            ),
        ],
        ..Extension::named("coding")
    });
    let agents_md = define_extension(Extension {
        sections: vec![section(
            "agents_md",
            |_, _| ready(Ok(Some("Run npm run check after changes.".to_owned()))).boxed(),
            None,
        )],
        ..Extension::named("agents-md")
    });
    // Another extension decorates a section by key without replacing it.
    let terse = define_extension(Extension {
        wraps: vec![wrap_section("preamble", |preamble| {
            let inner = Arc::clone(&preamble.render);
            Ok(Arc::new(PromptSection {
                render: Arc::new(move |input, render_context| {
                    let rendered = inner(input, render_context);
                    async move {
                        // TS template literal: `undefined` renders as text.
                        let text = rendered.await?;
                        Ok(Some(format!(
                            "{} Be terse.",
                            text.as_deref().unwrap_or("undefined")
                        )))
                    }
                    .boxed()
                }),
                ..PromptSection::clone(preamble)
            }))
        })],
        ..Extension::named("terse")
    });

    let registry = create_registry();
    registry.install(Arc::clone(&coding))?;
    registry.install(Arc::clone(&agents_md))?;
    registry.install(Arc::clone(&terse))?;
    // The environment follows each conversation's agent `cwd`.
    let env: EnvFactory = Arc::new(|target, _| {
        let env: Arc<dyn ExecutionEnv> =
            Arc::new(NativeExecutionEnv::new(NativeExecutionEnvOptions {
                cwd: target.cwd.unwrap_or_else(|| "/".to_owned()),
                ..NativeExecutionEnvOptions::default()
            }));
        ready(Ok(Some(env))).boxed()
    });
    let mut options = HarnessOptions::new(models, Arc::new(registry));
    options.env = Some(env);
    let harness = Harness::open(Arc::new(MemoryStorage::new()), options, context).await?;
    let root = harness
        .root(
            RootOptions {
                agent: Some(AgentChange {
                    model: FieldChange::Set(faux_model()),
                    cwd: FieldChange::Set("/repo".to_owned()),
                    ..AgentChange::default()
                }),
                ..RootOptions::default()
            },
            context,
        )
        .await?;

    // A subagent deselects AGENTS.md and gets its own instructions, rendered
    // last as the `instructions` section.
    let subagent = harness
        .create_conversation(
            ConversationCreateOptions {
                agent: Some(AgentChange {
                    model: FieldChange::Set(faux_model()),
                    cwd: FieldChange::Set("/repo".to_owned()),
                    extensions: FieldChange::Set(ExtensionsChange::Edit {
                        add: None,
                        remove: Some(vec![Arc::clone(&agents_md)]),
                    }),
                    instructions: FieldChange::Set("Only read; never edit files.".to_owned()),
                    ..AgentChange::default()
                }),
                ..ConversationCreateOptions::new(ConversationOwnership::Ownerless)
            },
            context,
        )
        .await?;

    root.submit(InputSubmissionDraft::new("Fix the build."), context)
        .await?
        .wait(context)
        .await?;
    subagent
        .submit(InputSubmissionDraft::new("Read the logs."), context)
        .await?
        .wait(context)
        .await?;
    writeln!(out, "root system prompt: {}", system_entries(&root).await?)?;
    writeln!(
        out,
        "subagent system prompt: {}",
        system_entries(&subagent).await?
    )?;

    // When a section's output changes, the next request appends only the
    // change.
    root.configure(
        AgentChange {
            cwd: FieldChange::Set("/repo/packages".to_owned()),
            ..AgentChange::default()
        },
        context,
    )
    .await?;
    root.submit(InputSubmissionDraft::new("Now the package."), context)
        .await?
        .wait(context)
        .await?;
    writeln!(
        out,
        "root system entries after cwd change: {}",
        system_entries(&root).await?
    )?;

    harness.close(context).await?;
    Ok(())
}
