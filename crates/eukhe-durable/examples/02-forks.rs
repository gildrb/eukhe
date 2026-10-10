//! Fork a conversation.
//! Run: `cargo run -p eukhe-durable --example 02-forks`
use std::io::Write;
use std::sync::Arc;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_chord::json::{JsonObject, JsonValue};
use eukhe_durable::documents::{DocDefinition, RewindableConversationDoc};
use eukhe_durable::session::create_session;
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::types::{ConversationOwnership, EntryDraft, EntryQuery, RewindableFork};
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

fn note(data: &str) -> EntryDraft {
    let mut draft = EntryDraft::new("note");
    draft.data = Some(JsonValue::from(data));
    draft
}

/// Runs the example, writing what the TS example prints to `out`.
///
/// # Errors
/// Session and output failures.
pub async fn run(
    out: &mut (dyn Write + Send),
    _args: &[String],
    _openai_api_key: Option<&str>,
) -> Result<(), BoxError> {
    let context = &*BACKGROUND_CONTEXT;
    let session = create_session(
        Arc::new(MemoryStorage::new()),
        eukhe_durable::session::SessionOptions::default(),
    );

    let chat = session
        .commit(
            |tx| async move {
                tx.create_conversation(ConversationOwnership::Ownerless)
                    .await
            },
            context,
        )
        .await?;
    let first_entry = session
        .commit(
            move |tx| async move {
                let entry = tx.append_entry(chat.id, note("hello")).await?;
                tx.doc(&NOTES, chat.id).await?.set("text", "after hello")?;
                Ok(entry)
            },
            context,
        )
        .await?;
    session
        .commit(
            move |tx| async move {
                tx.append_entry(chat.id, note("goodbye")).await?;
                tx.doc(&NOTES, chat.id)
                    .await?
                    .set("text", "after goodbye")?;
                Ok(())
            },
            context,
        )
        .await?;

    // A fork is a new conversation that continues from one entry of another. It
    // sees the parent's transcript up to that entry, and each document follows its
    // own fork policy. NOTES uses `AsOf`, so the fork starts with the notes
    // value from the fork entry.
    let branch = session
        .commit(
            move |tx| async move {
                tx.fork_conversation(chat.id, first_entry.id, ConversationOwnership::Ownerless)
                    .await
            },
            context,
        )
        .await?;

    // scan_entries() pages through visible entries, newest first. The fork sees
    // "hello" (inherited from the parent) but not "goodbye", which came later.
    let branch_entries = session
        .commit(
            move |tx| async move { tx.scan_entries(EntryQuery::new(branch.id), 10, None).await },
            context,
        )
        .await?;
    let transcript: Vec<JsonValue> = branch_entries
        .items
        .iter()
        .map(|entry| entry.data.clone().unwrap_or(JsonValue::Null))
        .collect();
    writeln!(out, "fork transcript: {}", JsonValue::from(transcript))?;
    let fork_notes = session.snapshot(&NOTES, branch.id, context).await?;
    writeln!(out, "fork notes: {}", show(fork_notes))?;

    // The fork's copy is independent: editing it leaves the parent unchanged.
    session
        .commit(
            move |tx| async move {
                tx.doc(&NOTES, branch.id)
                    .await?
                    .set("text", "changed only in the fork")?;
                Ok(())
            },
            context,
        )
        .await?;
    let fork_notes = session.snapshot(&NOTES, branch.id, context).await?;
    writeln!(out, "fork notes after edit: {}", show(fork_notes))?;
    let parent_notes = session.snapshot(&NOTES, chat.id, context).await?;
    writeln!(out, "parent notes after edit: {}", show(parent_notes))?;

    session.close(context).await?;
    Ok(())
}
