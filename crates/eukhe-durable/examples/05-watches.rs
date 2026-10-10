//! Serialize asynchronous document work with a watch.
//! Run: `cargo run -p eukhe-durable --example 05-watches`
use std::io::Write;
use std::sync::Arc;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_chord::json::JsonValue;
use eukhe_durable::documents::{DocDefinition, RewindableConversationDoc};
use eukhe_durable::session::{create_session, ObservedDocumentValue};
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::types::{ConversationOwnership, RewindableFork};
use futures::FutureExt;
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

/// `console.log` of an observed value: its JSON, or `null` once retired.
fn show(value: ObservedDocumentValue) -> String {
    value.map_or_else(
        || "null".to_owned(),
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

    // A watch starts from one stable acquisition revision. Slow callbacks never
    // overlap; exact committed frames buffer, with a full-value reset after 100.
    let Some(notes_watch) = session.watch_doc(&NOTES, chat.id, context).await? else {
        return Err("notes are absent".into());
    };
    writeln!(out, "watch baseline: {}", show(notes_watch.value()))?;
    // The listener sends each line to `run`, which writes it to `out`.
    let (delivered, mut updates) = mpsc::unbounded_channel();
    notes_watch.start(Arc::new(move |value, _ops, _delivery_context| {
        // A closed receiver only means `run` stopped listening.
        let _ = delivered.send(format!("watch update: {}", show(value)));
        async { Ok(()) }.boxed()
    }))?;
    session
        .commit(
            move |tx| async move {
                tx.doc(&NOTES, chat.id)
                    .await?
                    .set("text", "observed asynchronously")?;
                Ok(())
            },
            context,
        )
        .await?;
    let line = updates
        .recv()
        .await
        .ok_or("the watch ended before an update")?;
    writeln!(out, "{line}")?;
    notes_watch.stop().await;

    session.close(context).await?;
    Ok(())
}
