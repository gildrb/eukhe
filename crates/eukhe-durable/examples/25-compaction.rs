//! Compaction: a long trip-planning chat whose older messages are summarized so the model context stays small.
//! Run:
//!   cargo run -p eukhe-durable --example 25-compaction
use std::io::Write;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_chord::json::{from_json, JsonValue};
use eukhe_durable::entries::COMPACTION_ENTRY;
use eukhe_durable::harness::registry::create_registry;
use eukhe_durable::harness::types::InputSubmissionDraft;
use eukhe_durable::harness::types::{
    AgentChange, CompactionResult, FieldChange, HarnessOptions, HarnessSettings, LiveSettings,
    ModelRef, PartialCompactionPolicy,
};
use eukhe_durable::harness::{
    Conversation, ConversationEntryQuery, Harness, LiveState, RootOptions, LIVE_DOC,
};
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::types::{
    DocumentReaderExt, InputSubmission, SubmissionState, SubmissionStatus, WriteSubmission,
};
use eukhe_pi_ai::models::{create_models, CreateModelsOptions};
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_provider, FauxAssistantMessageOptions, FauxModelDefinition,
    FauxResponseStep, RegisterFauxProviderOptions,
};
use eukhe_types::pi_ai::{
    AssistantContentBlock, Message, StopReason, SystemContent, UserContent, UserContentBlock,
};
use futures::FutureExt;
use tokio::sync::oneshot;

type BoxError = Box<dyn std::error::Error + Send + Sync>;

// One thread, like the JS event loop: the background compaction races the chat, and a single-threaded runtime
// interleaves them in the same order on every run, as Node does.
#[tokio::main(flavor = "current_thread")]
async fn main() -> Result<(), BoxError> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let key = std::env::var("OPENAI_API_KEY").ok();
    run(&mut std::io::stdout(), &args, key.as_deref()).await
}

/// The fake model's script state.
#[derive(Default)]
struct Script {
    overflow_once: AtomicBool,
    summaries: AtomicU64,
    /// While set, the next chat answer waits for it, which keeps the conversation busy.
    hold: Mutex<Option<oneshot::Receiver<()>>>,
}

// A fake model with a tiny 3000-token window. It answers chat messages, writes summaries when asked to summarize,
// and once rejects a request as too long, the way real providers report a context overflow.
fn respond(script: &Arc<Script>) -> FauxResponseStep {
    let script = Arc::clone(script);
    FauxResponseStep::Factory(Arc::new(move |transcript, _, _, _| {
        let messages = transcript.messages();
        if let Some(Message::System(first)) = messages.first() {
            if let SystemContent::Text(content) = &first.content {
                if content.contains("summarization") {
                    let summaries = script.summaries.fetch_add(1, Ordering::SeqCst) + 1;
                    let answer = faux_assistant_message(
                        format!("## Goal\nPlan a week in Lisbon (summary #{summaries})."),
                        FauxAssistantMessageOptions::default(),
                    );
                    return async move { Ok(answer) }.boxed();
                }
            }
        }
        if script.overflow_once.swap(false, Ordering::SeqCst) {
            let answer = faux_assistant_message(
                "",
                FauxAssistantMessageOptions {
                    stop_reason: Some(StopReason::Error),
                    error_message: Some("prompt is too long".to_owned()),
                    ..FauxAssistantMessageOptions::default()
                },
            );
            return async move { Ok(answer) }.boxed();
        }
        let held = script
            .hold
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .take();
        let question = messages
            .iter()
            .rev()
            .find(|message| matches!(message, Message::User(_)));
        let answer = format!(
            "A detailed answer to \"{}\": {}",
            text(question),
            "details ".repeat(200)
        );
        async move {
            if let Some(held) = held {
                // A dropped sender releases the answer too.
                let _ = held.await;
            }
            Ok(faux_assistant_message(
                answer,
                FauxAssistantMessageOptions::default(),
            ))
        }
        .boxed()
    }))
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
    let script = Arc::new(Script::default());
    let faux = faux_provider(RegisterFauxProviderOptions {
        models: Some(vec![FauxModelDefinition {
            context_window: Some(3000),
            max_tokens: Some(1000),
            ..FauxModelDefinition::new("tiny")
        }]),
        ..RegisterFauxProviderOptions::default()
    });
    faux.set_responses((0..100).map(|_| respond(&script)).collect());
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(faux.provider.clone());

    // Generation blocks to compact above 3000 - 1000 = 2000 tokens and starts a background compaction above
    // 2000 - 800. Settings are read at every use, so updating them changes `backgroundTokens` live.
    let compaction = |background_tokens: f64| PartialCompactionPolicy {
        enabled: None,
        reserve_tokens: Some(1000.0),
        keep_recent_tokens: Some(400.0),
        background_tokens: Some(background_tokens),
    };
    let settings = Arc::new(LiveSettings::new(HarnessSettings {
        compaction: Some(compaction(800.0)),
        ..HarnessSettings::default()
    }));
    let mut options = HarnessOptions::new(models, Arc::new(create_registry()));
    options.settings = Some(Arc::clone(&settings) as _);
    let harness = Harness::open(Arc::new(MemoryStorage::new()), options, cx).await?;
    let root = harness
        .root(
            RootOptions {
                agent: Some(AgentChange {
                    model: FieldChange::Set(ModelRef {
                        provider: "faux".to_owned(),
                        model_id: "tiny".to_owned(),
                    }),
                    ..AgentChange::default()
                }),
                ..RootOptions::default()
            },
            cx,
        )
        .await?;

    // 1. A long chat: once the context crosses the background threshold, a compaction runs while the chat goes
    // on, and its summary lands at once when the conversation is idle, otherwise at the next turn boundary.
    for question in [
        "Where should we stay?",
        "What should we eat?",
        "Which day trips?",
        "Any museums?",
        "Nightlife?",
    ] {
        ask(out, &harness, &root, question, cx).await?;
    }

    // 2. A manual compaction while an answer is still being written. The summary is ready first, waits in the
    // inbox, and is placed right after the answer.
    let (finish_answer, held) = oneshot::channel();
    *script.hold.lock().unwrap_or_else(PoisonError::into_inner) = Some(held);
    // Both commits are enqueued here, in this order, before the answer's generation prepares its request: with a
    // compaction already live, that request starts no background compaction. Node's event loop gives the same
    // order to the two sequential awaits; on a Rust runtime the generation could otherwise get there first.
    let busy = root.submit(InputSubmissionDraft::new("How do we get around?"), cx);
    let manual = root.compact(Some("Keep the hotel shortlist".to_owned()), cx);
    let busy = busy.await?;
    let manual = manual.await?;
    let settled = harness.wait_for_task(manual, cx).await?;
    let placement = match settled.outcome {
        eukhe_durable::types::TaskOutcome::Completed { result } => {
            from_json::<CompactionResult>(&result)?.submission_id
        }
        _ => None,
    }
    .ok_or("the manual compaction placed no summary")?;
    let summary = harness
        .submission(placement, cx)
        .await?
        .ok_or("the summary submission exists")?;
    writeln!(
        out,
        "\nmanual compaction finished; its summary is {}",
        status_name(summary.status(cx).await?.state.status())
    )?;
    // The receiver may already be gone if the answer was released otherwise.
    let _ = finish_answer.send(());
    busy.wait(cx).await?;
    writeln!(
        out,
        "after the answer, the summary is {}",
        status_name(summary.wait(cx).await?.record().state.status())
    )?;
    show(out, &root, "after compact()", cx).await?;

    // 3. The provider rejects a request as too long: generation compacts and retries it once. Background
    // compaction is turned off so the summary below is the overflow one.
    settings.update(|settings| settings.compaction = Some(compaction(0.0)));
    ask(out, &harness, &root, "What should we pack?", cx).await?;
    script.overflow_once.store(true, Ordering::SeqCst);
    ask(
        out,
        &harness,
        &root,
        "Summarize the plan for my partner",
        cx,
    )
    .await?;

    harness.close(cx).await?;
    Ok(())
}

async fn ask(
    out: &mut (dyn Write + Send),
    harness: &Harness,
    root: &Conversation,
    question: &str,
    cx: &Context,
) -> Result<(), BoxError> {
    let submission = root.submit(InputSubmissionDraft::new(question), cx).await?;
    let record = submission.wait(cx).await?.into_record();
    // Let a background compaction started by this turn finish, so its summary shows below.
    let live = harness.snapshot(&LIVE_DOC, root.id(), cx).await?;
    let running = match live {
        Some(live) => from_json::<LiveState>(&JsonValue::Object(live))?
            .compactions
            .unwrap_or_default(),
        None => Vec::new(),
    };
    for compaction in running {
        harness.wait_for_task(compaction.task_id, cx).await?;
    }
    let outcome = match &record.state {
        SubmissionState::Input(InputSubmission::Done { .. })
        | SubmissionState::Write(WriteSubmission::Done { .. }) => "answered".to_owned(),
        SubmissionState::Input(InputSubmission::Unanswered { reason, .. })
        | SubmissionState::Write(WriteSubmission::Unanswered { reason, .. }) => reason.clone(),
        SubmissionState::Input(InputSubmission::Queued | InputSubmission::Placed { .. })
        | SubmissionState::Write(WriteSubmission::Queued) => {
            return Err("a settled submission has a terminal status".into())
        }
    };
    show(out, root, &format!("after \"{question}\" ({outcome})"), cx).await
}

/// The TS `status` string of a submission.
fn status_name(status: SubmissionStatus) -> &'static str {
    match status {
        SubmissionStatus::Queued => "queued",
        SubmissionStatus::Placed => "placed",
        SubmissionStatus::Done => "done",
        SubmissionStatus::Unanswered => "unanswered",
    }
}

/// Print the model context: one line per message, and the number of stored entries behind it.
async fn show(
    out: &mut (dyn Write + Send),
    conversation: &Conversation,
    label: &str,
    cx: &Context,
) -> Result<(), BoxError> {
    let view = conversation.context(cx).await?;
    let stored = conversation
        .entries(ConversationEntryQuery::default(), 1000, None, cx)
        .await?
        .items
        .len();
    writeln!(
        out,
        "\n{label}: {} messages in context, {stored} entries stored",
        view.messages.len()
    )?;
    if COMPACTION_ENTRY.is(view.head.as_ref()) {
        if let Some(reason) = view
            .head
            .as_ref()
            .and_then(|head| head.data.as_ref())
            .and_then(|data| data["reason"].as_str())
        {
            writeln!(out, "  ({reason} compaction summary first)")?;
        }
    }
    for message in &view.messages {
        let shown = if matches!(message, Message::System(_)) {
            "(system prompt)".to_owned()
        } else {
            text(Some(message)).chars().take(70).collect()
        };
        writeln!(out, "  {:<9} {shown}", message.role())?;
    }
    Ok(())
}

fn text(message: Option<&Message>) -> String {
    let blocks = match message {
        None | Some(Message::System(_)) => return String::new(),
        Some(Message::User(message)) => match &message.content {
            UserContent::Text(text) => return text.clone(),
            UserContent::Blocks(blocks) => blocks.iter().find_map(|block| match block {
                UserContentBlock::Text(text) => Some(text.text.clone()),
                UserContentBlock::Image(_) => None,
            }),
        },
        Some(Message::Assistant(message)) => message.content.iter().find_map(|block| match block {
            AssistantContentBlock::Text(text) => Some(text.text.clone()),
            AssistantContentBlock::Thinking(_) | AssistantContentBlock::ToolCall(_) => None,
        }),
        Some(Message::ToolResult(message)) => {
            message.content.iter().find_map(|block| match block {
                UserContentBlock::Text(text) => Some(text.text.clone()),
                UserContentBlock::Image(_) => None,
            })
        }
    };
    blocks.map_or_else(String::new, |text| text.replace('\n', " "))
}
