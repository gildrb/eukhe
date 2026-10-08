//! `eukhe.compaction` on a durable Harness: the eukhe summary (wrapper,
//! update mode, live delta sink) and the manual-compaction flow. The model
//! is the faux provider, so everything is deterministic. The head-parsing
//! battery lives in [`super::head`].

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_durable::harness::types::{InputSubmissionDraft, ModelRef};
use eukhe_durable::harness::ConversationEntryQuery;
use eukhe_pi_ai::models::{create_models, CreateModelsOptions, Models};
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_provider, faux_text, FauxAssistantMessageOptions,
    FauxProviderHandle, FauxResponseStep, RegisterFauxProviderOptions,
};
use eukhe_types::pi_ai::{StopReason, UserContent};
use tempfile::TempDir;

use crate::durable::{open_session, EukheSession, SessionConfig, SessionStorage};

fn cx() -> &'static eukhe_chord::context::Context {
    &BACKGROUND_CONTEXT
}

/// Directories and the faux model collection of one session.
struct Fixture {
    dir: TempDir,
    faux: FauxProviderHandle,
    models: Models,
    deltas: Arc<Mutex<Vec<String>>>,
}

impl Fixture {
    fn new() -> Self {
        let dir = TempDir::new().expect("temp dir");
        for sub in ["agent", "work"] {
            std::fs::create_dir_all(dir.path().join(sub)).expect("fixture dir");
        }
        // A tiny keep window so a manual compaction of the short test
        // conversation still finds a cut.
        std::fs::write(
            dir.path().join("agent").join("settings.json"),
            r#"{"compaction":{"keepRecentTokens":1}}"#,
        )
        .expect("settings file");
        let faux = faux_provider(RegisterFauxProviderOptions::default());
        let models = create_models(CreateModelsOptions::default());
        models.set_provider(faux.provider.clone());
        Self {
            dir,
            faux,
            models,
            deltas: Arc::new(Mutex::new(Vec::new())),
        }
    }

    async fn open(&self) -> EukheSession {
        let mut config = SessionConfig::new(
            self.dir.path().join("agent"),
            self.dir.path().join("work"),
            "019a0000-0000-7000-8000-00000000000c",
            SessionStorage::Jsonl {
                dir: self.dir.path().join("sessions").join("session-c"),
                fsync: false,
            },
        );
        config.models = Some(self.models.clone());
        config.model = Some(
            ModelRef {
                provider: "faux".to_owned(),
                model_id: "faux-1".to_owned(),
            }
            .into(),
        );
        let deltas = Arc::clone(&self.deltas);
        config.summary_delta = Some(Arc::new(move |delta: &str| {
            deltas
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(delta.to_owned());
        }));
        open_session(config, cx()).await.expect("session opens")
    }

    /// Queue one assistant reply.
    fn reply(&self, text: &str) {
        self.faux.append_responses(vec![faux_assistant_message(
            vec![faux_text(text)],
            FauxAssistantMessageOptions {
                stop_reason: Some(StopReason::Stop),
                ..FauxAssistantMessageOptions::default()
            },
        )
        .into()]);
    }

    /// One user turn answered by `text`, settled.
    async fn turn(&self, session: &EukheSession, prompt: &str, reply_text: &str) {
        self.reply(reply_text);
        session
            .root()
            .submit(
                InputSubmissionDraft {
                    request_id: None,
                    content: UserContent::Text(prompt.to_owned()),
                    when_busy: None,
                },
                cx(),
            )
            .await
            .unwrap();
        session.root().wait_for_idle(cx()).await.unwrap();
    }
}

/// The model text of the newest `pi.compaction` entry, when one exists.
/// The scan is newest-first, so the first match wins.
async fn newest_summary_text(session: &EukheSession) -> Option<String> {
    let root = session.root();
    let mut cursor = None;
    loop {
        let page = root
            .entries(ConversationEntryQuery::default(), 64, cursor, cx())
            .await
            .unwrap();
        for entry in &page.items {
            if entry.kind == "pi.compaction" {
                return entry.model.as_deref().and_then(|messages| {
                    messages.first().and_then(|message| match message {
                        eukhe_types::pi_ai::Message::User(user) => match &user.content {
                            UserContent::Text(text) => Some(text.clone()),
                            UserContent::Blocks(blocks) => Some(
                                blocks
                                    .iter()
                                    .filter_map(|block| match block {
                                        eukhe_types::pi_ai::UserContentBlock::Text(text) => {
                                            Some(text.text.as_str())
                                        }
                                        eukhe_types::pi_ai::UserContentBlock::Image(_) => None,
                                    })
                                    .collect::<String>(),
                            ),
                        },
                        _ => None,
                    })
                });
            }
        }
        match page.next {
            Some(next) => cursor = Some(next),
            None => return None,
        }
    }
}

#[tokio::test]
async fn the_summary_lands_wrapped_and_streams_its_deltas() {
    let fixture = Fixture::new();
    let session = fixture.open().await;
    fixture
        .turn(&session, "tell me a story", "once upon a time")
        .await;
    // The summarizer reply.
    fixture.reply("the story of the turn");
    session.root().compact(None, cx()).await.unwrap();
    session.root().wait_for_idle(cx()).await.unwrap();
    let text = newest_summary_text(&session)
        .await
        .expect("compaction entry");
    // The durable wrapper outside, the eukhe `[compaction-summary]` wrapper
    // and the summarizer's text inside.
    assert!(text.starts_with(
        "The conversation history before this point was compacted into the following summary:"
    ));
    assert!(text.contains("[compaction-summary]"));
    assert!(text.contains("the story of the turn"));
    assert!(text.contains("<summary>"));
    // The live sink carried the summarizer text (the delta stream), in
    // order, and nothing else (no files were touched, so no file block).
    // The sink sees the summarizer's chunks; a client accumulates them.
    let deltas = fixture
        .deltas
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone();
    assert_eq!(deltas.concat(), "the story of the turn".to_owned());
    session.close(cx()).await.unwrap();
}

#[tokio::test]
async fn a_second_compaction_summarizes_in_update_mode_over_the_previous_summary() {
    let fixture = Fixture::new();
    let session = fixture.open().await;
    fixture.turn(&session, "one", "answer one").await;
    fixture.turn(&session, "two", "answer two").await;
    fixture.reply("first summary");
    session.root().compact(None, cx()).await.unwrap();
    session.root().wait_for_idle(cx()).await.unwrap();
    fixture.turn(&session, "three", "answer three").await;
    fixture.reply("updated summary");
    session.root().compact(None, cx()).await.unwrap();
    session.root().wait_for_idle(cx()).await.unwrap();
    // The second compaction's summary landed, and it is the update of the
    // first (the parsed previous summary drives the update prompt; the
    // head battery in `head` covers the parse itself).
    let text = newest_summary_text(&session).await.expect("second summary");
    assert!(text.contains("updated summary"), "newest summary: {text}");
    session.close(cx()).await.unwrap();
}
