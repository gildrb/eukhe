//! The inbox: what happens to submissions while a conversation is busy.
//! Run:
//!   cargo run -p eukhe-durable --example 20-inbox
use std::io::Write;
use std::sync::Arc;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_chord::json::{from_json, JsonValue};
use eukhe_durable::harness::registry::create_registry;
use eukhe_durable::harness::types::{
    AgentChange, FieldChange, HarnessOptions, HarnessSettings, InputSubmissionDraft, LiveSettings,
    ModelRef, QueueMode, WhenBusy, WriteSubmissionDraft,
};
use eukhe_durable::harness::{
    ConversationEntryQuery, Harness, InboxItem, InboxState, RootOptions, SubmissionHandle,
    INBOX_DOC,
};
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::types::{DocumentReaderExt, EntryDraft, SubmissionStatus};
use eukhe_pi_ai::models::{create_models, CreateModelsOptions};
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_provider, FauxAssistantMessageOptions, FauxResponseStep,
    RegisterFauxProviderOptions,
};
use eukhe_types::pi_ai::UserContent;
use futures::FutureExt;

type BoxError = Box<dyn std::error::Error + Send + Sync>;

#[tokio::main]
async fn main() -> Result<(), BoxError> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let key = std::env::var("OPENAI_API_KEY").ok();
    run(&mut std::io::stdout(), &args, key.as_deref()).await
}

fn input(content: &str, when_busy: Option<WhenBusy>) -> InputSubmissionDraft {
    InputSubmissionDraft {
        request_id: None,
        content: UserContent::Text(content.to_owned()),
        when_busy,
    }
}

fn status_name(status: SubmissionStatus) -> &'static str {
    match status {
        SubmissionStatus::Queued => "queued",
        SubmissionStatus::Placed => "placed",
        SubmissionStatus::Done => "done",
        SubmissionStatus::Unanswered => "unanswered",
    }
}

/// Runs the example, writing what the TS example prints to `out`.
///
/// # Errors
///
/// Harness failures.
#[expect(
    clippy::too_many_lines,
    reason = "one example, step by step in the TS file's order"
)]
pub async fn run(
    out: &mut (dyn Write + Send),
    _args: &[String],
    _openai_api_key: Option<&str>,
) -> Result<(), BoxError> {
    let context = &*BACKGROUND_CONTEXT;

    // The first answer waits until we let it go, so the conversation stays busy while we submit more.
    let (release, held) = tokio::sync::watch::channel(false);
    let slow = FauxResponseStep::Factory(Arc::new(move |_, _, _, _| {
        let mut held = held.clone();
        async move {
            // A dropped sender also releases the answer.
            let _ = held.wait_for(|released| *released).await;
            Ok(faux_assistant_message(
                "Answer to the first question.",
                FauxAssistantMessageOptions::default(),
            ))
        }
        .boxed()
    }));
    let faux = faux_provider(RegisterFauxProviderOptions::default());
    faux.set_responses(vec![
        slow,
        faux_assistant_message(
            "Answer to the follow-up and the steer.",
            FauxAssistantMessageOptions::default(),
        )
        .into(),
    ]);
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(faux.provider.clone());

    // Settings apply to every conversation: place every queued follow-up at once instead of one per run.
    let mut options = HarnessOptions::new(models, Arc::new(create_registry()));
    options.settings = Some(Arc::new(LiveSettings::new(HarnessSettings {
        follow_up_mode: Some(QueueMode::All),
        ..HarnessSettings::default()
    })));
    let harness = Harness::open(Arc::new(MemoryStorage::new()), options, context).await?;
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

    let first = root.submit(input("First question", None), context).await?;

    // While busy, input queues as a follow-up (the default) or a steer, and writes queue too.
    let follow_up = root.submit(input("A follow-up", None), context).await?;
    let steer = root
        .submit(input("A steer", Some(WhenBusy::Steer)), context)
        .await?;
    let mut note_entry = EntryDraft::new("app.note");
    note_entry.data = Some(JsonValue::from("noted while busy"));
    let note = root
        .submit(
            WriteSubmissionDraft {
                request_id: None,
                entry: note_entry,
            },
            context,
        )
        .await?;
    let withdrawn = root.submit(input("Never mind", None), context).await?;
    // whenBusy: "reject" refuses instead of queueing.
    if let Err(error) = root
        .submit(input("Now or never", Some(WhenBusy::Reject)), context)
        .await
    {
        writeln!(out, "rejected: {error}")?;
    }
    // A queued submission can be withdrawn until a boundary places it.
    writeln!(
        out,
        "withdraw: {}",
        withdrawn.abort(context).await?.as_str()
    )?;

    let inbox: Option<InboxState> = harness
        .snapshot(&INBOX_DOC, root.id(), context)
        .await?
        .map(|value| from_json(&JsonValue::Object(value)))
        .transpose()?;
    let items: Vec<String> = inbox
        .map(|inbox| inbox.items)
        .unwrap_or_default()
        .iter()
        .map(|item| {
            let mode = match item {
                InboxItem::Steer { .. } => "steer",
                InboxItem::FollowUp { .. } => "followUp",
                InboxItem::Write { .. } => "write",
            };
            format!("{} {mode}", item.id())
        })
        .collect();
    writeln!(out, "inbox: {}", serde_json::to_string(&items)?)?;

    // The first answer ends the run at a final boundary: the write is placed first, then the steer and the
    // follow-up, which start the next run together.
    release.send_replace(true);
    for (name, submission) in [
        ("first", &first),
        ("follow-up", &follow_up),
        ("steer", &steer),
        ("note", &note),
        ("withdrawn", &withdrawn),
    ] {
        status(out, name, submission).await?;
    }

    let page = root
        .entries(ConversationEntryQuery::default(), 20, None, context)
        .await?;
    let kinds: Vec<&str> = page
        .items
        .iter()
        .rev()
        .map(|entry| entry.kind.as_str())
        .collect();
    writeln!(out, "transcript: {}", serde_json::to_string(&kinds)?)?;
    harness.close(context).await?;
    Ok(())
}

async fn status(
    out: &mut (dyn Write + Send),
    name: &str,
    submission: &SubmissionHandle,
) -> Result<(), BoxError> {
    let record = submission.wait(&BACKGROUND_CONTEXT).await?;
    let status = record.state.status();
    let reason = if status == SubmissionStatus::Unanswered {
        record.state.reason().unwrap_or_default()
    } else {
        ""
    };
    writeln!(out, "{name}: {} {reason}", status_name(status))?;
    Ok(())
}
