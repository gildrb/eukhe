//! Conversation handles, typed entries, created conversations, and forks.
//! Run from the workspace:
//!   cargo run -p eukhe-durable --example 08-harness-conversations
use std::io::Write;
use std::sync::Arc;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_durable::entries::{define_entry, Entry};
use eukhe_durable::harness::registry::create_registry;
use eukhe_durable::harness::types::{
    AgentChange, ConversationCreateOptions, FieldChange, HarnessOptions,
};
use eukhe_durable::harness::{Harness, RootOptions};
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::types::{ConversationOwnership, TypedEntryDraft};
use eukhe_pi_ai::models::{create_models, CreateModelsOptions};
use eukhe_types::pi_ai::{Message, ModelThinkingLevel, UserContent, UserMessage};
use serde::{Deserialize, Serialize};

type BoxError = Box<dyn std::error::Error + Send + Sync>;

#[tokio::main]
async fn main() -> Result<(), BoxError> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let key = std::env::var("OPENAI_API_KEY").ok();
    run(&mut std::io::stdout(), &args, key.as_deref()).await
}

/// The `data` of a `message` entry.
#[derive(Debug, Clone, Serialize, Deserialize)]
struct MessageData {
    from: String,
}

/// An entry token types an entry kind's `data`.
static MESSAGE: Entry<MessageData> = match define_entry("message") {
    Ok(token) => token,
    Err(_) => panic!("`message` is a non-empty kind"),
};

/// The lowercase name TS prints for a thinking level.
fn level_name(level: ModelThinkingLevel) -> Result<String, BoxError> {
    match serde_json::to_value(level)? {
        serde_json::Value::String(name) => Ok(name),
        other => Err(format!("thinking level serialized as {other}").into()),
    }
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
    let harness = Harness::open(
        Arc::new(MemoryStorage::new()),
        HarnessOptions::new(
            create_models(CreateModelsOptions::default()),
            Arc::new(create_registry()),
        ),
        context,
    )
    .await?;
    let root = harness.root(RootOptions::default(), context).await?;
    root.configure(
        AgentChange {
            thinking_level: FieldChange::Set(ModelThinkingLevel::High),
            ..AgentChange::default()
        },
        context,
    )
    .await?;

    // Conversation handles are stateless; compare them by id. They bind
    // commits to their conversation. An entry token types an entry kind's
    // `data`.
    let root_id = root.id();
    let hello = root
        .commit(
            move |tx| async move {
                tx.append_typed_entry(
                    &MESSAGE,
                    root_id,
                    TypedEntryDraft {
                        data: MessageData {
                            from: "example".to_owned(),
                        },
                        model: Some(vec![Message::User(UserMessage {
                            content: UserContent::Text("hello".to_owned()),
                            timestamp: 1,
                        })]),
                        head: None,
                        edits: None,
                    },
                )
                .await
            },
            context,
        )
        .await?;
    writeln!(
        out,
        "typed entry: {} {}",
        MESSAGE.is(Some(hello.entry())),
        hello.data().from
    )?;

    // create_conversation() and fork() apply `agent` and run `init` in the
    // creating commit. A fork starts with the agent the parent had at the fork
    // entry.
    let helper = harness
        .create_conversation(
            ConversationCreateOptions {
                agent: Some(AgentChange {
                    thinking_level: FieldChange::Set(ModelThinkingLevel::Minimal),
                    ..AgentChange::default()
                }),
                ..ConversationCreateOptions::new(ConversationOwnership::Ownerless)
            },
            context,
        )
        .await?;
    let retry = root
        .fork(
            hello.id,
            ConversationCreateOptions::new(ConversationOwnership::Ownerless),
            context,
        )
        .await?;
    writeln!(
        out,
        "helper thinking: {}",
        level_name(helper.agent(context).await?.thinking_level)?
    )?;
    writeln!(
        out,
        "fork thinking: {}",
        level_name(retry.agent(context).await?.thinking_level)?
    )?;
    let found = harness.conversation(retry.id(), context).await?;
    writeln!(
        out,
        "lookup: {}",
        found.is_some_and(|conversation| conversation.id() == retry.id())
    )?;

    harness.close(context).await?;
    Ok(())
}
