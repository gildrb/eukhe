//! A Session stores conversations, transcript entries, tasks, and documents.
//! Run: `cargo run -p eukhe-durable --example 00-conversation`
use std::io::Write;
use std::sync::Arc;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_chord::json::to_json;
use eukhe_durable::session::create_session;
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::types::ConversationOwnership;

type BoxError = Box<dyn std::error::Error + Send + Sync>;

#[tokio::main]
async fn main() -> Result<(), BoxError> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let key = std::env::var("OPENAI_API_KEY").ok();
    run(&mut std::io::stdout(), &args, key.as_deref()).await
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
    // MemoryStorage keeps everything in memory; other storage backends keep it on disk.
    let session = create_session(
        Arc::new(MemoryStorage::new()),
        eukhe_durable::session::SessionOptions::default(),
    );

    // Every Session call takes a context, which is used for cancellation.
    // BACKGROUND_CONTEXT means "never cancel".
    let context = &*BACKGROUND_CONTEXT;

    // All writes happen inside session.commit(). The callback receives a
    // transaction `tx`; everything it writes is saved together when the callback
    // returns, or discarded if it fails.
    // "ownerless" means no task created this conversation.
    let standalone = session
        .commit(
            |tx| async move {
                tx.create_conversation(ConversationOwnership::Ownerless)
                    .await
            },
            context,
        )
        .await?;
    writeln!(out, "standalone conversation: {}", to_json(&standalone)?)?;

    session.close(context).await?;
    Ok(())
}
