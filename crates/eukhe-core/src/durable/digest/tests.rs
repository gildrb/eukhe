//! `eukhe.digest` over a full durable session: delivery at the first
//! request, freshness across a reopen, the compaction head, and the
//! only-newest-digest-in-context invariant.

use std::path::Path;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::harness::types::ModelRef;
use eukhe_durable::harness::ConversationEntryQuery;
use eukhe_durable::session::SessionResult;
use eukhe_durable::types::{EntryDraft, EntryHead, EntryRecord};
use eukhe_pi_ai::models::{create_models, CreateModelsOptions, Models};
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_provider, faux_text, FauxAssistantMessageOptions,
    FauxProviderHandle, FauxResponseStep, RegisterFauxProviderOptions,
};
use eukhe_types::pi_ai::{Message, UserContent, UserMessage};
use tempfile::TempDir;

use super::super::{HostDeps, SessionConfig, SessionStorage};
use super::{
    digest_from_frame, harness_digest_message_text, HARNESS_DIGEST_CUSTOM_TYPE,
    HARNESS_DIGEST_PREFIX,
};
use crate::durable::open_session;
use crate::durable::EukheSession;
use crate::refinement::{
    empty_harness_state, get_global_harness_state_dir, save_harness_state, HarnessEntry,
    RefinementKind,
};

fn cx() -> &'static Context {
    &BACKGROUND_CONTEXT
}

fn lock<T>(mutex: &Mutex<T>) -> std::sync::MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

/// Directories, models, and the faux provider of one session that survive a
/// reopen, like a worker host's own objects.
struct Fixture {
    dir: TempDir,
    faux: FauxProviderHandle,
    models: Models,
}

impl Fixture {
    fn new() -> Self {
        let dir = TempDir::new().expect("temp dir");
        for sub in ["agent", "work"] {
            std::fs::create_dir_all(dir.path().join(sub)).expect("fixture dir");
        }
        let faux = faux_provider(RegisterFauxProviderOptions::default());
        let models = create_models(CreateModelsOptions::default());
        models.set_provider(faux.provider.clone());
        Self { dir, faux, models }
    }

    fn agent_dir(&self) -> std::path::PathBuf {
        self.dir.path().join("agent")
    }

    fn storage(&self) -> std::path::PathBuf {
        self.dir.path().join("sessions").join("session-1")
    }

    fn config(&self) -> SessionConfig {
        let mut config = SessionConfig::new(
            self.agent_dir(),
            self.dir.path().join("work"),
            "019a0000-0000-7000-8000-000000000001",
            SessionStorage::Jsonl {
                dir: self.storage(),
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
        config
    }

    async fn open(&self) -> EukheSession {
        open_session(self.config(), cx())
            .await
            .expect("session opens")
    }
}

/// Write one memory into the global harness state.
fn write_memory(agent_dir: &Path, id: &str, content: &str) {
    let mut state = empty_harness_state();
    state
        .entries
        .get_mut(&RefinementKind::Memory)
        .unwrap()
        .insert(
            id.to_string(),
            HarnessEntry {
                id: id.to_string(),
                kind: RefinementKind::Memory,
                title: format!("Memory {id}"),
                content: content.to_string(),
                path: String::new(),
                scope: None,
                reference: serde_json::Map::default(),
                arguments: serde_json::Map::default(),
                metadata: serde_json::Map::default(),
                source: "general".to_string(),
                created_at: "2026-01-01T00:00:00.000Z".to_string(),
                updated_at: "2026-01-01T00:00:00.000Z".to_string(),
                version: 1,
            },
        );
    save_harness_state(&get_global_harness_state_dir(agent_dir), &state)
        .expect("harness state saved");
}

/// A step that records the request's messages and answers `reply`.
fn recording_step(requests: &Arc<Mutex<Vec<Vec<Message>>>>, reply: &str) -> FauxResponseStep {
    let requests = Arc::clone(requests);
    let reply = faux_assistant_message(
        vec![faux_text(reply)],
        FauxAssistantMessageOptions::default(),
    );
    FauxResponseStep::factory(move |request, _, _, _| {
        lock(&requests).push(request.messages().to_vec());
        Ok(reply.clone())
    })
}

async fn submit(session: &EukheSession, input: &str) {
    use eukhe_durable::harness::types::InputSubmissionDraft;
    use eukhe_durable::types::SubmissionStatus;
    let id = session
        .root()
        .submit(InputSubmissionDraft::new(input), cx())
        .await
        .expect("submitted")
        .id();
    let status = session
        .harness()
        .submission(id, cx())
        .await
        .expect("submission read")
        .expect("the submission exists")
        .wait(cx())
        .await
        .expect("settled")
        .state
        .status();
    assert_eq!(status, SubmissionStatus::Done);
}

async fn entries(session: &EukheSession) -> Vec<EntryRecord> {
    let page = session
        .root()
        .entries(ConversationEntryQuery::default(), 1000, None, cx())
        .await
        .expect("entries");
    page.items.into_iter().rev().collect()
}

/// The session's delivered digest entries, oldest first.
fn digest_entries(entries: &[EntryRecord]) -> Vec<&EntryRecord> {
    entries
        .iter()
        .filter(|entry| {
            entry.kind == "eukhe.custom"
                && serde_json::Value::from(
                    entry
                        .data
                        .clone()
                        .unwrap_or(eukhe_chord::json::JsonValue::Null),
                )
                .get("customType")
                .and_then(serde_json::Value::as_str)
                    == Some(HARNESS_DIGEST_CUSTOM_TYPE)
        })
        .collect()
}

/// The digest frames of one model request, in order. Wire user messages
/// deserialize as blocks when the provider sent a content array, so both
/// content shapes decode.
fn frames(messages: &[Message]) -> Vec<String> {
    messages
        .iter()
        .filter_map(|message| match message {
            Message::User(user) => match &user.content {
                UserContent::Text(text) => digest_from_frame(text).map(str::to_string),
                UserContent::Blocks(blocks) => blocks
                    .iter()
                    .filter_map(|block| match block {
                        eukhe_types::pi_ai::UserContentBlock::Text(text) => {
                            digest_from_frame(&text.text).map(str::to_string)
                        }
                        eukhe_types::pi_ai::UserContentBlock::Image(_) => None,
                    })
                    .collect::<Vec<_>>()
                    .first()
                    .cloned(),
            },
            Message::System(_) | Message::Assistant(_) | Message::ToolResult(_) => None,
        })
        .collect()
}

/// The text of the request's non-digest user messages.
fn user_texts(messages: &[Message]) -> Vec<String> {
    messages
        .iter()
        .filter_map(|message| match message {
            Message::User(user) => match &user.content {
                UserContent::Text(text) if !text.contains(HARNESS_DIGEST_PREFIX) => {
                    Some(text.clone())
                }
                UserContent::Text(_) | UserContent::Blocks(_) => None,
            },
            Message::System(_) | Message::Assistant(_) | Message::ToolResult(_) => None,
        })
        .collect()
}

/// The session's deps, for `conversation_digest`.
fn deps(session: &EukheSession) -> Arc<HostDeps> {
    Arc::clone(session.deps())
}

/// The raw digest of the newest delivered digest entry, as the compaction
/// summary's leading snapshot frame carries it.
fn delivered_digest_text(rows: &[EntryRecord]) -> Option<String> {
    let newest = digest_entries(rows).pop()?;
    let data = serde_json::Value::from(newest.data.clone().expect("digest data"));
    Some(
        data["details"]["digest"]
            .as_str()
            .expect("the digest")
            .to_string(),
    )
}

/// Append a compaction head marker whose context starts at `first_kept`.
async fn compaction_head(
    session: &EukheSession,
    first_kept: EntryHead,
    summary: &str,
) -> SessionResult<()> {
    let mut draft = EntryDraft::new("pi.compaction");
    draft.head = Some(first_kept);
    draft.model = Some(vec![Message::User(UserMessage {
        content: UserContent::Text(summary.to_string()),
        timestamp: 1,
    })]);
    let conversation = session.root().clone();
    let conversation_id = conversation.id();
    conversation
        .commit(
            move |tx| async move {
                tx.append_entry(conversation_id, draft).await?;
                Ok(())
            },
            cx(),
        )
        .await
}

#[tokio::test]
async fn delivers_the_digest_at_the_first_request_and_persists_it() {
    let fixture = Fixture::new();
    write_memory(&fixture.agent_dir(), "m1", "Prefer tabs in this repo.");
    let requests: Arc<Mutex<Vec<Vec<Message>>>> = Arc::default();
    fixture
        .faux
        .set_responses(vec![recording_step(&requests, "understood")]);
    let session = fixture.open().await;
    submit(&session, "hello").await;

    let all = lock(&requests).clone();
    assert_eq!(all.len(), 1);
    let delivered = frames(&all[0]);
    assert_eq!(delivered.len(), 1, "{:?}", all[0]);
    assert!(
        delivered[0].contains("Prefer tabs in this repo."),
        "{}",
        delivered[0]
    );
    // The digest rides ahead of the user's prompt.
    assert_eq!(user_texts(&all[0]), ["hello"]);
    let digest_at = all[0]
        .iter()
        .position(|message| frames(std::slice::from_ref(message)).len() == 1)
        .expect("the digest message");
    let prompt_at = all[0]
        .iter()
        .position(|message| user_texts(std::slice::from_ref(message)) == ["hello"])
        .expect("the prompt message");
    assert!(digest_at < prompt_at);

    // The row persists with today's display rules.
    let all = entries(&session).await;
    let rows = digest_entries(&all);
    assert_eq!(rows.len(), 1);
    let data = serde_json::Value::from(rows[0].data.clone().expect("digest data"));
    assert_eq!(data["display"], false);
    assert!(data["details"]["digest"].is_string());
    assert!(data["details"]["stateFingerprint"].is_string());
    let rendered = super::conversation_digest(&deps(&session), session.root(), cx())
        .await
        .expect("render");
    assert_eq!(
        data["details"]["digest"].as_str(),
        Some(rendered.digest.as_str())
    );
    session.close(cx()).await.expect("close");
}

#[tokio::test]
async fn a_reopen_redelivers_only_when_the_state_changed() {
    let fixture = Fixture::new();
    write_memory(&fixture.agent_dir(), "m1", "Answer in English.");
    let requests: Arc<Mutex<Vec<Vec<Message>>>> = Arc::default();
    fixture.faux.set_responses(vec![
        recording_step(&requests, "one"),
        recording_step(&requests, "two"),
        recording_step(&requests, "three"),
    ]);
    let session = fixture.open().await;
    submit(&session, "first").await;
    assert_eq!(digest_entries(&entries(&session).await).len(), 1);
    session.close(cx()).await.expect("close");

    // Reopen with the state unchanged: the digest still rides the request
    // (it is in context), but no second row is delivered.
    let session = fixture.open().await;
    submit(&session, "second").await;
    assert_eq!(digest_entries(&entries(&session).await).len(), 1);
    let seen = lock(&requests).clone();
    assert_eq!(frames(&seen[1]).len(), 1, "frames: {frames:?}", frames = frames(&seen[1]));

    // The learned state changes: the next request delivers a fresh digest,
    // and only the newest reaches the model.
    write_memory(&fixture.agent_dir(), "m2", "Run tests before replying.");
    submit(&session, "third").await;
    let all = entries(&session).await;
    let rows = digest_entries(&all);
    assert_eq!(rows.len(), 2);
    let seen = lock(&requests).clone();
    let delivered = frames(&seen[2]);
    assert_eq!(delivered.len(), 1, "{:?}", seen[2]);
    assert!(
        delivered[0].contains("Run tests before replying."),
        "{}",
        delivered[0]
    );
    // The superseded row keeps its content in the transcript.
    assert!(rows[0].model.is_some());
    session.close(cx()).await.expect("close");
}

#[tokio::test]
async fn a_compaction_head_without_a_snapshot_redelivers() {
    let fixture = Fixture::new();
    write_memory(&fixture.agent_dir(), "m1", "Keep answers short.");
    let requests: Arc<Mutex<Vec<Vec<Message>>>> = Arc::default();
    fixture.faux.set_responses(vec![
        recording_step(&requests, "one"),
        recording_step(&requests, "two"),
    ]);
    let session = fixture.open().await;
    submit(&session, "hello").await;
    assert_eq!(digest_entries(&entries(&session).await).len(), 1);

    // A compaction whose head keeps only the answer: the delivered digest
    // falls out of context.
    let all = entries(&session).await;
    let answer = all.last().expect("the answer entry");
    compaction_head(
        &session,
        EntryHead::Entry(answer.id),
        "[compaction] early work",
    )
    .await
    .expect("compaction head");
    submit(&session, "continue").await;

    let all = entries(&session).await;
    let rows = digest_entries(&all);
    assert_eq!(rows.len(), 2, "a fresh digest is delivered after the head");
    let seen = lock(&requests).clone();
    let delivered = frames(&seen[1]);
    assert_eq!(delivered.len(), 1, "{:?}", seen[1]);
    assert!(
        delivered[0].contains("Keep answers short."),
        "{}",
        delivered[0]
    );
    session.close(cx()).await.expect("close");
}

#[tokio::test]
async fn a_compaction_snapshot_of_the_current_state_suppresses_redelivery() {
    let fixture = Fixture::new();
    write_memory(&fixture.agent_dir(), "m1", "Quote file paths verbatim.");
    let requests: Arc<Mutex<Vec<Vec<Message>>>> = Arc::default();
    fixture.faux.set_responses(vec![
        recording_step(&requests, "one"),
        recording_step(&requests, "two"),
    ]);
    let session = fixture.open().await;
    submit(&session, "hello").await;
    let Some(delivered_digest) = delivered_digest_text(&entries(&session).await) else {
        panic!("the delivered digest row");
    };

    // The compaction summary carries the digest snapshot as its leading
    // frame (the old engine's `harnessDigest` on the summary).
    let all = entries(&session).await;
    let answer = all.last().expect("the answer entry");
    let summary = format!(
        "{}[compaction] early work",
        harness_digest_message_text(&delivered_digest)
    );
    compaction_head(&session, EntryHead::Entry(answer.id), &summary)
        .await
        .expect("compaction head");
    submit(&session, "continue").await;

    assert_eq!(
        digest_entries(&entries(&session).await).len(),
        1,
        "the snapshot is fresh, so nothing is re-delivered"
    );
    let seen = lock(&requests).clone();
    let delivered = frames(&seen[1]);
    assert_eq!(delivered.len(), 1, "{:?}", seen[1]);
    assert!(
        delivered[0].contains("Quote file paths verbatim."),
        "{}",
        delivered[0]
    );
    session.close(cx()).await.expect("close");
}

/// A stale snapshot is superseded: the fresh digest entry replaces the
/// summary's digest block, so the summary text alone remains and exactly
/// one digest reaches the model.
#[tokio::test]
async fn a_stale_compaction_snapshot_yields_its_digest_block() {
    let fixture = Fixture::new();
    write_memory(&fixture.agent_dir(), "m1", "Original lesson.");
    let requests: Arc<Mutex<Vec<Vec<Message>>>> = Arc::default();
    fixture.faux.set_responses(vec![
        recording_step(&requests, "one"),
        recording_step(&requests, "two"),
    ]);
    let session = fixture.open().await;
    submit(&session, "hello").await;
    let Some(delivered_digest) = delivered_digest_text(&entries(&session).await) else {
        panic!("the delivered digest row");
    };
    let all = entries(&session).await;
    let answer = all.last().expect("the answer entry");
    let summary = format!(
        "{}[compaction] early work",
        harness_digest_message_text(&delivered_digest)
    );
    compaction_head(&session, EntryHead::Entry(answer.id), &summary)
        .await
        .expect("compaction head");

    // The state moves on: the snapshot is stale, so a fresh digest entry is
    // delivered and the summary loses its digest block.
    write_memory(&fixture.agent_dir(), "m2", "Updated lesson.");
    submit(&session, "continue").await;

    let all = entries(&session).await;
    let rows = digest_entries(&all);
    assert_eq!(rows.len(), 2);
    let seen = lock(&requests).clone();
    let request = &seen[1];
    let delivered = frames(request);
    assert_eq!(delivered.len(), 1, "{request:?}");
    assert!(delivered[0].contains("Updated lesson."), "{}", delivered[0]);
    // The summary survives, stripped of the superseded snapshot block.
    assert!(
        user_texts(request)
            .iter()
            .any(|text| text == "[compaction] early work"),
        "{:?}",
        user_texts(request)
    );
    session.close(cx()).await.expect("close");
}
