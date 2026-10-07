//! Expose a document through Chord.
//! Run: `cargo run -p eukhe-durable --example 04-chord-state`
use std::io::Write;
use std::sync::Arc;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_chord::DeliveryKind;
use eukhe_durable::documents::{DocDefinition, RewindableConversationDoc};
use eukhe_durable::session::create_session;
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::types::{ConversationOwnership, RewindableFork};
use serde::{Deserialize, Serialize};
use tokio::sync::mpsc;

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

/// Runs the example, writing what the TS example prints to `out`.
///
/// # Errors
/// Session, Chord, and output failures.
pub async fn run(
    out: &mut (dyn Write + Send),
    _args: &[String],
    _openai_api_key: Option<&str>,
) -> Result<(), BoxError> {
    let context = &*BACKGROUND_CONTEXT;
    let session = create_session(Arc::new(MemoryStorage::new()));

    let chat = session
        .commit(
            |tx| async move {
                let conversation = tx
                    .create_conversation(ConversationOwnership::Ownerless)
                    .await?;
                tx.doc(&NOTES, conversation.id)
                    .await?
                    .set("text", "first")?;
                Ok(conversation)
            },
            context,
        )
        .await?;

    // document_state() never creates a document. It returns a hydrated read-only
    // Chord state bound to the current concrete incarnation.
    let Some(notes_state) = session.document_state(&NOTES, chat.id, context).await? else {
        return Err("notes are absent".into());
    };
    // The listener sends each line to `run`, which writes it to `out` in
    // delivery order. Chord delivers asynchronously (TS: on a microtask that
    // runs before `await session.commit()` resumes); Rust tasks give no such
    // ordering, so `run` waits for the update delivery before unsubscribing.
    let (sink, mut lines) = mpsc::unbounded_channel();
    let stop_notes = notes_state.subscribe(move |value, _delivery_context, delivery| {
        // A closed receiver only means `run` stopped listening.
        let _ = sink.send((
            delivery.kind,
            format!(
                "Chord notes: {} {} {value}",
                delivery.kind.as_str(),
                delivery.sequence
            ),
        ));
    });
    session
        .commit(
            move |tx| async move {
                tx.doc(&NOTES, chat.id)
                    .await?
                    .set("text", "published through Chord")?;
                Ok(())
            },
            context,
        )
        .await?;
    loop {
        let (kind, line) = lines
            .recv()
            .await
            .ok_or("the state ended before an update")?;
        writeln!(out, "{line}")?;
        if kind == DeliveryKind::Update {
            break;
        }
    }
    stop_notes.dispose();
    notes_state.dispose()?;

    session.close(context).await?;
    Ok(())
}
