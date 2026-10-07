//! A chat turn.
//! Run from the workspace:
//!   cargo run -p eukhe-durable --example 14-chat
use std::io::Write;
use std::sync::Arc;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_durable::entries::ASSISTANT_ENTRY;
use eukhe_durable::harness::define::{define_extension, section};
use eukhe_durable::harness::registry::create_registry;
use eukhe_durable::harness::types::{
    AgentChange, Extension, FieldChange, HarnessOptions, InputSubmissionDraft, ModelRef,
};
use eukhe_durable::harness::{ConversationEntryQuery, Harness, RootOptions};
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::types::{InputSubmission, SubmissionState};
use eukhe_pi_ai::models::{create_models, CreateModelsOptions};
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_provider, FauxAssistantMessageOptions, RegisterFauxProviderOptions,
};
use eukhe_types::pi_ai::Message;
use futures::FutureExt;

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
///
/// The first step that fails.
pub async fn run(
    out: &mut (dyn Write + Send),
    _args: &[String],
    _openai_api_key: Option<&str>,
) -> Result<(), BoxError> {
    let context = &*BACKGROUND_CONTEXT;

    // The faux provider stands in for a real model (see 16-real-model.rs).
    let faux = faux_provider(RegisterFauxProviderOptions::default());
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(faux.provider.clone());
    faux.set_responses(vec![faux_assistant_message(
        "Paris.",
        FauxAssistantMessageOptions::default(),
    )
    .into()]);

    let registry = create_registry();
    registry.install(define_extension(Extension {
        sections: vec![section(
            "preamble",
            |_, _| futures::future::ready(Ok(Some("You answer in one word.".to_owned()))).boxed(),
            Some(false),
        )],
        ..Extension::named("terse")
    }))?;
    let harness = Harness::open(
        Arc::new(MemoryStorage::new()),
        HarnessOptions::new(models, Arc::new(registry)),
        context,
    )
    .await?;
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
            context,
        )
        .await?;

    // submit() durably admits user input and returns a submission handle.
    // The built-in pi.generation task prepares the system prompt from the
    // agent's sections, calls the model, and appends the answer; wait()
    // resolves once the input is answered or has failed.
    let capital = root
        .submit(InputSubmissionDraft::new("Capital of France?"), context)
        .await?;
    let answered = capital.wait(context).await?;
    if let SubmissionState::Input(InputSubmission::Done { answer, .. }) = answered.state {
        let entry = root
            .commit(move |tx| async move { tx.entry(answer).await }, context)
            .await?
            .filter(|entry| ASSISTANT_ENTRY.is(Some(entry)));
        let reply = entry.and_then(|entry| entry.model.and_then(|model| model.into_iter().next()));
        let shown = match &reply {
            Some(Message::Assistant(reply)) => serde_json::to_string(&reply.content)?,
            Some(reply) => serde_json::to_string(reply)?,
            None => "undefined".to_owned(),
        };
        writeln!(out, "answer: {shown}")?;
    }

    // The transcript holds the user input, the positional system prompt, and
    // the answer.
    let transcript = root
        .entries(ConversationEntryQuery::default(), 10, None, context)
        .await?;
    let kinds: Vec<&str> = transcript
        .items
        .iter()
        .rev()
        .map(|entry| entry.kind.as_str())
        .collect();
    writeln!(out, "transcript: {}", serde_json::to_string(&kinds)?)?;
    harness.close(context).await?;
    Ok(())
}
