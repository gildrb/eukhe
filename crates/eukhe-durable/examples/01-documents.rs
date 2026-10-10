//! Store document state next to transcript entries.
//! Run: `cargo run -p eukhe-durable --example 01-documents`
use std::io::Write;
use std::sync::Arc;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_chord::json::{JsonObject, JsonValue};
use eukhe_durable::documents::{DocDefinition, RewindableConversationDoc};
use eukhe_durable::session::create_session;
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::types::{ConversationOwnership, EntryDraft, RewindableFork};
use serde::{Deserialize, Serialize};

type BoxError = Box<dyn std::error::Error + Send + Sync>;

#[derive(Debug, Default, Serialize, Deserialize)]
struct Notes {
    text: String,
}

// A document is a JSON object attached to something; here, one per conversation.
// "rewindable" keeps old values readable, so you can ask what the document
// looked like when a particular entry was written.
// The fork policy says what a forked copy of the conversation starts with (see 02-forks.rs).
static NOTES: RewindableConversationDoc<Notes> = match RewindableConversationDoc::define(
    DocDefinition {
        kind: "example.notes",
        version: 1,
        initial: Notes::default,
        migrate: None,
        checkpoint_when: None,
    },
    // A fork starts with the value these notes had at the fork entry.
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

    // tx.doc() returns an editable draft of the document (created on first use).
    // Writes to it are saved when the commit finishes.
    let first_entry = session
        .commit(
            move |tx| async move {
                let mut draft = EntryDraft::new("note");
                draft.data = Some(JsonValue::from("hello"));
                let entry = tx.append_entry(chat.id, draft).await?;
                tx.doc(&NOTES, chat.id).await?.set("text", "after hello")?;
                Ok(entry)
            },
            context,
        )
        .await?;

    let second_entry = session
        .commit(
            move |tx| async move {
                let mut draft = EntryDraft::new("note");
                draft.data = Some(JsonValue::from("goodbye"));
                let entry = tx.append_entry(chat.id, draft).await?;
                tx.doc(&NOTES, chat.id)
                    .await?
                    .set("text", "after goodbye")?;
                Ok(entry)
            },
            context,
        )
        .await?;

    // snapshot() reads the latest value. snapshot_as_of() reads the value that
    // was saved in the same commit as the given entry.
    let latest = session.snapshot(&NOTES, chat.id, context).await?;
    writeln!(out, "latest notes: {}", show(latest))?;
    let at_first = session
        .snapshot_as_of(&NOTES, chat.id, first_entry.id, context)
        .await?;
    writeln!(out, "notes at first entry: {}", show(at_first))?;
    let at_second = session
        .snapshot_as_of(&NOTES, chat.id, second_entry.id, context)
        .await?;
    writeln!(out, "notes at second entry: {}", show(at_second))?;

    session.close(context).await?;
    Ok(())
}
