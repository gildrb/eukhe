//! One sandbox per conversation: the app records each conversation's sandbox in its own document, and the Harness
//! environment function looks it up for every tool call. Here a sandbox is a directory; a hosted product would
//! return an `ExecutionEnv` that runs inside the conversation's container.
//! Run:
//!   cargo run -p eukhe-durable --example 29-sandbox-per-conversation
use std::io::Write;
use std::sync::Arc;

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_chord::json::{JsonObject, JsonValue};
use eukhe_durable::documents::{ConversationDoc, DocDefinition};
use eukhe_durable::env::{ExecutionEnv, NativeExecutionEnv, NativeExecutionEnvOptions};
use eukhe_durable::harness::registry::create_registry;
use eukhe_durable::harness::types::{
    AgentChange, ConversationCreateOptions, EnvFactory, FieldChange, HarnessOptions,
    InputSubmissionDraft, ModelRef,
};
use eukhe_durable::harness::{Conversation, Harness};
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::tools::CODING_TOOLS;
use eukhe_durable::types::{ConversationOwnership, DocumentReaderExt, LatestFork};
use eukhe_pi_ai::models::{create_models, CreateModelsOptions};
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_provider, faux_tool_call, FauxAssistantMessageOptions,
    FauxResponseStep, RegisterFauxProviderOptions,
};
use eukhe_types::pi_ai::StopReason;
use futures::FutureExt;
use tempfile::TempDir;

type BoxError = Box<dyn std::error::Error + Send + Sync>;

#[tokio::main]
async fn main() -> Result<(), BoxError> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let key = std::env::var("OPENAI_API_KEY").ok();
    run(&mut std::io::stdout(), &args, key.as_deref()).await
}

// Which sandbox a conversation runs in: `{ path?: string }`. `LatestFork::Initial`: a fork gets no sandbox until
// the app assigns one.
const SANDBOX: ConversationDoc<JsonValue> = match ConversationDoc::define(
    DocDefinition {
        kind: "app.sandbox",
        version: 1,
        initial: || JsonValue::from(JsonObject::new()),
        migrate: None,
        checkpoint_when: None,
    },
    LatestFork::Initial,
) {
    Ok(token) => token,
    Err(_) => panic!("app.sandbox is a valid document definition"),
};

fn note(text: &str) -> FauxResponseStep {
    let mut arguments = serde_json::Map::new();
    arguments.insert("path".to_owned(), "note.txt".into());
    arguments.insert("content".to_owned(), text.into());
    faux_assistant_message(
        faux_tool_call("write", arguments, None),
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::ToolUse),
            ..FauxAssistantMessageOptions::default()
        },
    )
    .into()
}

fn saved() -> FauxResponseStep {
    faux_assistant_message("Saved.", FauxAssistantMessageOptions::default()).into()
}

// Each user's conversation gets a fresh sandbox in the creating commit.
async fn conversation_for(
    harness: &Harness,
    user: &str,
    cx: &Context,
) -> Result<(Conversation, TempDir), BoxError> {
    let sandbox = tempfile::Builder::new()
        .prefix(&format!("pi-durable-sandbox-{user}-"))
        .tempdir()?;
    let path = sandbox
        .path()
        .to_str()
        .ok_or("the temp directory path is UTF-8")?
        .to_owned();
    let conversation = harness
        .create_conversation(
            ConversationCreateOptions {
                agent: Some(AgentChange {
                    model: FieldChange::Set(ModelRef {
                        provider: "faux".to_owned(),
                        model_id: "faux-1".to_owned(),
                    }),
                    ..AgentChange::default()
                }),
                init: Some(Box::new(move |tx, id| {
                    async move {
                        tx.doc(&SANDBOX, id).await?.set("path", path.as_str())?;
                        Ok(())
                    }
                    .boxed()
                })),
                ..ConversationCreateOptions::new(ConversationOwnership::Ownerless)
            },
            cx,
        )
        .await?;
    Ok((conversation, sandbox))
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
    let faux = faux_provider(RegisterFauxProviderOptions::default());
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(faux.provider.clone());
    faux.set_responses(vec![note("from alice"), saved(), note("from bob"), saved()]);

    let registry = create_registry();
    registry.install(Arc::clone(&CODING_TOOLS))?;
    // Committed reads only; a conversation without a sandbox gets no environment, so its tools fail cleanly.
    let env: EnvFactory = Arc::new(|target, env_context| {
        let sandbox = target
            .read
            .snapshot(&SANDBOX, target.conversation_id, env_context);
        async move {
            let path = sandbox.await?.and_then(|sandbox| {
                sandbox
                    .get("path")
                    .and_then(JsonValue::as_str)
                    .map(str::to_owned)
            });
            Ok(path.map(|cwd| {
                Arc::new(NativeExecutionEnv::new(NativeExecutionEnvOptions {
                    cwd,
                    ..NativeExecutionEnvOptions::default()
                })) as Arc<dyn ExecutionEnv>
            }))
        }
        .boxed()
    });
    let mut options = HarnessOptions::new(models, Arc::new(registry));
    options.env = Some(env);
    let harness = Harness::open(Arc::new(MemoryStorage::new()), options, cx).await?;

    let (alice, alice_sandbox) = conversation_for(&harness, "alice", cx).await?;
    let (bob, bob_sandbox) = conversation_for(&harness, "bob", cx).await?;
    alice
        .submit(InputSubmissionDraft::new("Leave a note."), cx)
        .await?
        .wait(cx)
        .await?;
    bob.submit(InputSubmissionDraft::new("Leave a note."), cx)
        .await?
        .wait(cx)
        .await?;
    writeln!(
        out,
        "alice's sandbox: {}",
        std::fs::read_to_string(alice_sandbox.path().join("note.txt"))?
    )?;
    writeln!(
        out,
        "bob's sandbox: {}",
        std::fs::read_to_string(bob_sandbox.path().join("note.txt"))?
    )?;

    harness.close(cx).await?;
    alice_sandbox.close()?;
    bob_sandbox.close()?;
    Ok(())
}
