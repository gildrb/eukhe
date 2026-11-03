//! `eukhe.compaction` on a durable Harness: the eukhe summary (wrapper,
//! update mode, live delta sink) and the manual-compaction flow. The model
//! is the faux provider, so everything is deterministic.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_ai::models::{create_models, CreateModelsOptions, Models};
use eukhe_ai::providers::faux::{
    faux_assistant_message, faux_provider, faux_text, FauxAssistantMessageOptions,
    FauxProviderHandle, FauxResponseStep, RegisterFauxProviderOptions,
};
use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_durable::entries::{CompactionData, CompactionSummary, COMPACTION_ENTRY};
use eukhe_durable::harness::types::CompactionReason;
use eukhe_durable::harness::types::{InputSubmissionDraft, ModelRef};
use eukhe_durable::harness::{ConversationEntryQuery, SubmissionHandle, COMPACTION_TASK};
use eukhe_durable::types::{
    CommitChange, CommitPublication, EntryHead, SubmissionStatus, TaskStatus, TypedEntryDraft,
};
use eukhe_types::pi_ai::{AssistantMessage, Message, StopReason, UserContent, UserMessage};
use tempfile::TempDir;
use tokio::sync::Notify;

use super::head;
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
        self.faux.append_responses(vec![stop_message(text).into()]);
    }

    /// Submit one user prompt without waiting for its run.
    async fn submit(&self, session: &EukheSession, prompt: &str) -> SubmissionHandle {
        session
            .root()
            .submit(
                InputSubmissionDraft {
                    request_id: None,
                    content: UserContent::Text(prompt.to_owned()),
                    when_busy: None,
                    origin: eukhe_types::input_origin::InputOrigin::User,
                    entry: None,
                },
                cx(),
            )
            .await
            .unwrap()
    }

    /// One user turn answered by `text`, settled.
    async fn turn(&self, session: &EukheSession, prompt: &str, reply_text: &str) {
        self.reply(reply_text);
        self.submit(session, prompt).await;
        session.root().wait_for_idle(cx()).await.unwrap();
    }
}

/// A `stop` assistant reply carrying `text`.
fn stop_message(text: &str) -> AssistantMessage {
    faux_assistant_message(
        vec![faux_text(text)],
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::Stop),
            ..FauxAssistantMessageOptions::default()
        },
    )
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
    // first.
    let text = newest_summary_text(&session).await.expect("second summary");
    assert!(text.contains("updated summary"), "newest summary: {text}");
    session.close(cx()).await.unwrap();
}

/// A set `auxiliaryModel` that the compaction cannot use falls back to the
/// session model, and the session shows why in a display row, once for
/// that cause (before, a stderr line of the worker was all).
#[tokio::test]
async fn an_unused_auxiliary_model_shows_a_notice_once() {
    let fixture = Fixture::new();
    std::fs::write(
        fixture.dir.path().join("agent").join("settings.json"),
        r#"{"compaction":{"keepRecentTokens":1},"auxiliaryModel":"faux/missing"}"#,
    )
    .expect("settings file");
    let session = fixture.open().await;
    for round in ["one", "two"] {
        fixture.turn(&session, round, "an answer").await;
        fixture.reply("a summary");
        session.root().compact(None, cx()).await.unwrap();
        session.root().wait_for_idle(cx()).await.unwrap();
    }
    let mut notices: Vec<crate::durable::entries::CustomEntryData> = Vec::new();
    let mut cursor = None;
    loop {
        let page = session
            .root()
            .entries(ConversationEntryQuery::default(), 64, cursor, cx())
            .await
            .unwrap();
        notices.extend(
            page.items
                .into_iter()
                .filter_map(|entry| {
                    crate::durable::entries::CUSTOM_ENTRY
                        .narrow(entry)
                        .expect("custom data")
                })
                .map(|entry| entry.data().clone())
                .filter(|data| {
                    data.custom_type == super::auxiliary_model::AUXILIARY_MODEL_NOTICE_CUSTOM_TYPE
                }),
        );
        match page.next {
            Some(next) => cursor = Some(next),
            None => break,
        }
    }
    assert_eq!(
        notices,
        vec![crate::durable::entries::CustomEntryData {
            custom_type: super::auxiliary_model::AUXILIARY_MODEL_NOTICE_CUSTOM_TYPE.to_owned(),
            content: Some(UserContent::Text(
                "The auxiliaryModel setting \"faux/missing\" was not used for the compaction summary: no model with a configured key has this name. The session model faux/faux-1 ran it."
                    .to_owned()
            )),
            display: true,
            details: None,
            input: false,
            origin: None,
        }]
    );
    session.close(cx()).await.unwrap();
}

/// The observer keeps no per-task dedup state (it once kept every serviced
/// task id for the life of the session): it relies on the Session
/// publishing each task's terminal record exactly once. Two compactions
/// publish one terminal `pi.compaction` record each.
#[tokio::test]
async fn each_compaction_publishes_its_terminal_record_once() {
    let fixture = Fixture::new();
    let session = fixture.open().await;
    let terminal: Arc<Mutex<Vec<u64>>> = Arc::default();
    let seen = Arc::clone(&terminal);
    let subscription = session
        .harness()
        .subscribe_commits(Arc::new(
            move |publication: &CommitPublication, _cx: &eukhe_chord::context::Context| {
                for change in &publication.changes {
                    if let CommitChange::Task(record) = change {
                        if record.kind == COMPACTION_TASK.definition().name()
                            && record.state.status() == TaskStatus::Terminal
                        {
                            seen.lock()
                                .unwrap_or_else(PoisonError::into_inner)
                                .push(record.id.get());
                        }
                    }
                }
            },
        ))
        .unwrap();
    let root = session.root().clone();
    fixture.turn(&session, "one", "answer one").await;
    fixture.turn(&session, "two", "answer two").await;
    fixture.reply("first summary");
    let first = root.compact(None, cx()).await.unwrap();
    session.harness().wait_for_task(first, cx()).await.unwrap();
    fixture.turn(&session, "three", "answer three").await;
    fixture.reply("updated summary");
    let second = root.compact(None, cx()).await.unwrap();
    session.harness().wait_for_task(second, cx()).await.unwrap();
    // A waiter woken by a publication may run before the listeners saw it;
    // one session line read passes them.
    session
        .harness()
        .conversation(root.id(), cx())
        .await
        .unwrap();
    drop(subscription);

    assert_eq!(
        *terminal.lock().unwrap_or_else(PoisonError::into_inner),
        [first.get(), second.get()]
    );
    session.close(cx()).await.unwrap();
}

/// Regression: update mode continues from the head's typed summary, so the
/// previous summary's file lists carry into the next summary and the
/// summarizer gets the previous summary text without its rendering.
#[tokio::test]
async fn update_mode_carries_the_previous_typed_summary_and_its_file_lists() {
    let fixture = Fixture::new();
    let session = fixture.open().await;
    fixture.turn(&session, "one", "answer one").await;
    let previous = CompactionSummary {
        summary: "prior work".to_owned(),
        read_files: vec!["/a.rs".to_owned()],
        modified_files: vec!["/b.rs".to_owned()],
    };
    let root = session.root().clone();
    let answer = root
        .entries(ConversationEntryQuery::default(), 1, None, cx())
        .await
        .unwrap()
        .items[0]
        .id;
    let draft = COMPACTION_ENTRY
        .draft(&TypedEntryDraft {
            model: Some(vec![Message::User(UserMessage {
                content: UserContent::Text(head::rendered_summary(&previous)),
                timestamp: 1,
            })]),
            data: CompactionData {
                reason: CompactionReason::Manual,
                summary: Some(previous),
            },
            head: Some(EntryHead::Entry(answer)),
            edits: None,
        })
        .unwrap();
    let conversation_id = root.id();
    root.commit(
        move |tx| async move {
            tx.append_entry(conversation_id, draft).await?;
            Ok(())
        },
        cx(),
    )
    .await
    .unwrap();
    fixture.turn(&session, "two", "answer two").await;
    let requests: Arc<Mutex<Vec<String>>> = Arc::default();
    let recorded = Arc::clone(&requests);
    fixture
        .faux
        .append_responses(vec![FauxResponseStep::Factory(Arc::new(
            move |context, _, _, _| {
                recorded
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .push(serde_json::to_string(context.messages()).unwrap());
                Box::pin(async { Ok(stop_message("updated summary")) })
            },
        ))]);
    root.compact(None, cx()).await.unwrap();
    root.wait_for_idle(cx()).await.unwrap();

    let request = requests
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .concat();
    assert!(
        request.contains("<previous-summary>\\nprior work\\n</previous-summary>"),
        "summarizer request: {request}"
    );
    let newest = root
        .entries(ConversationEntryQuery::default(), 1, None, cx())
        .await
        .unwrap()
        .items
        .remove(0);
    let compaction = COMPACTION_ENTRY.narrow(newest).unwrap().unwrap();
    assert_eq!(
        compaction.data().summary.clone(),
        Some(CompactionSummary {
            summary: "updated summary".to_owned(),
            read_files: vec!["/a.rs".to_owned()],
            modified_files: vec!["/b.rs".to_owned()],
        })
    );
    session.close(cx()).await.unwrap();
}

/// The eukhe summary runs inside the durable compaction task, outside every
/// session lock: while the summarizer is still answering, the transcript
/// reads and a user prompt runs to completion; the summary lands once the
/// summarizer answers.
#[tokio::test(flavor = "multi_thread")]
async fn input_and_reads_proceed_while_the_summary_is_in_flight() {
    let fixture = Fixture::new();
    let session = fixture.open().await;
    fixture.turn(&session, "one", "answer one").await;
    let reached = Arc::new(Notify::new());
    let release = Arc::new(Notify::new());
    let (gate_reached, gate_release) = (Arc::clone(&reached), Arc::clone(&release));
    fixture
        .faux
        .append_responses(vec![FauxResponseStep::Factory(Arc::new(
            move |_, _, _, _| {
                let (reached, release) = (Arc::clone(&gate_reached), Arc::clone(&gate_release));
                Box::pin(async move {
                    reached.notify_one();
                    release.notified().await;
                    Ok(stop_message("gated summary"))
                })
            },
        ))]);
    session.root().compact(None, cx()).await.unwrap();
    reached.notified().await;

    let page = session
        .root()
        .entries(ConversationEntryQuery::default(), 64, None, cx())
        .await
        .unwrap();
    assert!(!page.items.is_empty());
    fixture.reply("answer two");
    let input = fixture.submit(&session, "two").await;
    assert_eq!(
        input.wait(cx()).await.unwrap().state.status(),
        SubmissionStatus::Done
    );
    assert_eq!(newest_summary_text(&session).await, None);

    release.notify_one();
    session.root().wait_for_idle(cx()).await.unwrap();
    let text = newest_summary_text(&session).await.expect("summary placed");
    assert!(text.contains("gated summary"), "summary: {text}");
    session.close(cx()).await.unwrap();
}

/// One request the faux provider answered: its context and options.
type Captured = (
    eukhe_types::pi_ai::TranscriptContext,
    eukhe_ai::types::SimpleStreamOptions,
);

/// A faux step that records its request, notifies `seen`, and answers
/// `reply`.
fn recorded(
    requests: &Arc<Mutex<Vec<Captured>>>,
    seen: &Arc<Notify>,
    reply: AssistantMessage,
) -> FauxResponseStep {
    let (requests, seen) = (Arc::clone(requests), Arc::clone(seen));
    FauxResponseStep::factory(move |context, options, _, _| {
        requests
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push((context.clone(), options.cloned().unwrap_or_default()));
        seen.notify_one();
        Ok(reply.clone())
    })
}

/// `body` without its cache marks: the provider's prompt cache keys on
/// the content, the marks only say where entries are written. A message's
/// string content is its one text block (the end mark turns the last
/// message's string into that block).
fn unmarked(mut body: serde_json::Value) -> serde_json::Value {
    fn strip(value: &mut serde_json::Value) {
        match value {
            serde_json::Value::Object(object) => {
                object.remove("cache_control");
                if let Some(serde_json::Value::String(text)) = object.get("content") {
                    let block = serde_json::json!([{ "type": "text", "text": text }]);
                    object.insert("content".to_owned(), block);
                }
                object.values_mut().for_each(strip);
            }
            serde_json::Value::Array(items) => items.iter_mut().for_each(strip),
            serde_json::Value::Null
            | serde_json::Value::Bool(_)
            | serde_json::Value::Number(_)
            | serde_json::Value::String(_) => {}
        }
    }
    strip(&mut body);
    body
}

/// The Anthropic body of `request` without marks, and its messages up to
/// the request's own end: without the trailing message that sets the
/// request's thinking effort (it ends every request).
async fn wire(request: &Captured) -> (serde_json::Value, Vec<serde_json::Value>) {
    let mut body =
        unmarked(crate::durable::open::tests::anthropic_body(&request.0, &request.1).await);
    let mut messages = body["messages"].as_array().expect("messages").clone();
    let effort = messages.pop().expect("the effort message");
    assert_eq!(effort["role"], "system");
    body.as_object_mut().expect("body").remove("messages");
    (body, messages)
}

/// The compact-trigger review continues the session's request: after an
/// overflow compaction it sends the retried turn's request (system prompt,
/// tools, thinking, messages) byte for byte, then the answer, marked as
/// the end of the shared prefix, then the review prompt. The next turn's
/// request starts with that same prefix, so it reads what the review
/// wrote. (The review was a request of its own: the review prompt as the
/// system prompt, the transcript as one user message, no tools.)
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn the_review_continues_the_sessions_request() {
    let fixture = Fixture::new();
    // The keep window leaves the seed turn before the cut.
    std::fs::write(
        fixture.dir.path().join("agent").join("settings.json"),
        r#"{"compaction":{"enabled":true,"reserveTokens":1,"keepRecentTokens":10}}"#,
    )
    .expect("settings file");
    let requests: Arc<Mutex<Vec<Captured>>> = Arc::default();
    let arrived = Arc::new(Notify::new());
    let overflow = faux_assistant_message(
        vec![faux_text("")],
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::Error),
            error_message: Some("prompt is too long: 213462 tokens > 200000 maximum".to_owned()),
            ..FauxAssistantMessageOptions::default()
        },
    );
    fixture.faux.set_responses(
        [
            stop_message("seed reply"),
            overflow,
            stop_message("the summary"),
            stop_message("recovered reply"),
            stop_message(r#"{"shouldRefine": false, "rationale": "one-off"}"#),
            stop_message("next reply"),
        ]
        .into_iter()
        .map(|reply| recorded(&requests, &arrived, reply))
        .collect(),
    );
    let session = fixture.open().await;
    let seed = format!("seed turn {}", "x".repeat(48_000));
    let probe = format!("overflow probe {}", "x".repeat(48_000));
    fixture.submit(&session, &seed).await;
    session.root().wait_for_idle(cx()).await.unwrap();
    fixture.submit(&session, &probe).await;
    session.root().wait_for_idle(cx()).await.unwrap();
    // The review starts once the conversation is idle.
    let count = || {
        requests
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .len()
    };
    while count() < 5 {
        arrived.notified().await;
    }
    fixture.submit(&session, "next prompt").await;
    session.root().wait_for_idle(cx()).await.unwrap();
    session.close(cx()).await.unwrap();

    let requests = requests
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone();
    let [_, _, _, retried, review, next] = &requests[..] else {
        panic!("six requests: {}", requests.len());
    };
    // The review's last message is the review prompt, after the answer.
    let review_messages = review.0.messages();
    let Some(Message::User(prompt)) = review_messages.last() else {
        panic!("the review prompt ends the review");
    };
    assert!(matches!(&prompt.content, UserContent::Text(text)
        if text.starts_with(crate::refinement::planner::AUTO_REFINE_REVIEW_SYSTEM_PROMPT)));
    let Some(Message::Assistant(answer)) = review_messages.iter().rev().nth(1) else {
        panic!("the answer precedes the review prompt");
    };
    assert_eq!(
        answer
            .content
            .iter()
            .map(|block| match block {
                eukhe_types::pi_ai::AssistantContentBlock::Text(text) => {
                    (text.text.as_str(), text.cache_breakpoint)
                }
                eukhe_types::pi_ai::AssistantContentBlock::Thinking(_)
                | eukhe_types::pi_ai::AssistantContentBlock::ToolCall(_) => ("", None),
            })
            .collect::<Vec<_>>(),
        vec![(
            "recovered reply",
            Some(eukhe_types::pi_ai::CacheBreakpoint::Ephemeral)
        )]
    );

    let (retried_body, retried_messages) = wire(retried).await;
    let (review_body, review_wire) = wire(review).await;
    let (next_body, next_wire) = wire(next).await;
    // Everything but the messages (system prompt, tools, thinking, ...) is
    // the session's, and the review's messages start with the retried
    // turn's; the next turn's start with the review's through the answer.
    assert_eq!(review_body, retried_body);
    assert_eq!(next_body, review_body);
    assert_eq!(review_wire[..retried_messages.len()], retried_messages[..]);
    let shared = review_wire.len() - 1;
    assert_eq!(next_wire.len(), shared + 1);
    assert_eq!(next_wire[..shared], review_wire[..shared]);
}
