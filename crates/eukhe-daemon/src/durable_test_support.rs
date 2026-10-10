//! In-process fixtures for the durable worker features: an eukhe session on
//! a temp agent dir with a faux model, JSONL storage, and helpers to drive a
//! turn and read the transcript.

use std::path::PathBuf;

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_core::durable::{open_session, EukheSession, SessionConfig, SessionStorage};
use eukhe_durable::harness::types::{InputSubmissionDraft, ModelRef};
use eukhe_durable::harness::{Conversation, ConversationEntryQuery};
use eukhe_durable::types::EntryRecord;
use eukhe_pi_ai::models::{create_models, CreateModelsOptions, Models};
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_provider, FauxAssistantMessageOptions, FauxProviderHandle,
    FauxResponseStep, RegisterFauxProviderOptions,
};

pub(crate) const SESSION_ID: &str = "0192a000-0000-7000-8000-0000000000f1";

pub(crate) fn cx() -> &'static Context {
    &BACKGROUND_CONTEXT
}

/// One faux text answer.
pub(crate) fn answer(text: &str) -> FauxResponseStep {
    faux_assistant_message(text, FauxAssistantMessageOptions::default()).into()
}

/// A temp agent dir, project cwd, and a faux provider shared by every
/// session the fixture opens.
pub(crate) struct Fixture {
    pub(crate) dir: tempfile::TempDir,
    pub(crate) agent_dir: PathBuf,
    pub(crate) cwd: PathBuf,
    pub(crate) sessions: PathBuf,
    pub(crate) faux: FauxProviderHandle,
    pub(crate) models: Models,
}

impl Fixture {
    pub(crate) fn new() -> Self {
        let dir = tempfile::tempdir().expect("tempdir");
        let agent_dir = dir.path().join("agent");
        let cwd = dir.path().join("project");
        let sessions = agent_dir.join("sessions");
        std::fs::create_dir_all(&sessions).expect("sessions dir");
        std::fs::create_dir_all(&cwd).expect("cwd");
        let faux = faux_provider(RegisterFauxProviderOptions::default());
        let models = create_models(CreateModelsOptions::default());
        models.set_provider(faux.provider.clone());
        Self {
            dir,
            agent_dir,
            cwd,
            sessions,
            faux,
            models,
        }
    }

    /// Write the agent's global `settings.json`.
    pub(crate) fn settings(&self, settings: &serde_json::Value) {
        std::fs::write(
            self.agent_dir.join("settings.json"),
            serde_json::to_string(settings).expect("settings json"),
        )
        .expect("settings");
    }

    pub(crate) fn model(&self) -> ModelRef {
        let model = self.faux.get_model();
        ModelRef {
            provider: model.provider,
            model_id: model.id,
        }
    }

    pub(crate) fn storage_dir(&self, session_id: &str) -> PathBuf {
        self.sessions.join(session_id)
    }

    pub(crate) fn config(&self, session_id: &str) -> SessionConfig {
        let mut config = SessionConfig::new(
            &self.agent_dir,
            &self.cwd,
            session_id,
            SessionStorage::Jsonl {
                dir: self.storage_dir(session_id),
                fsync: true,
            },
        );
        config.models = Some(self.models.clone());
        config.model = Some(self.model().into());
        config
    }

    /// Open (or reopen) the session `session_id`.
    pub(crate) async fn open(&self, session_id: &str) -> EukheSession {
        open_session(self.config(session_id), cx())
            .await
            .expect("open session")
    }
}

/// Open `SESSION_ID` the way the worker hosts it (lease, open, resume).
pub(crate) async fn hosted(fixture: &Fixture) -> std::sync::Arc<crate::worker::HostedSession> {
    let request = crate::worker::durable_host::HostRequest {
        config: fixture.config(SESSION_ID),
        scripted: None,
        // Test fixtures install no telemetry (an opted-out create).
        telemetry_disabled: Some(true),
        execution_mode: None,
    };
    std::sync::Arc::new(
        crate::worker::HostedSession::open(request, &fixture.agent_dir, cx())
            .await
            .expect("open hosted session"),
    )
}

/// Run one turn on `conversation` answered by `reply`.
pub(crate) async fn ask(fixture: &Fixture, conversation: &Conversation, text: &str, reply: &str) {
    fixture.faux.append_responses(vec![answer(reply)]);
    conversation
        .submit(InputSubmissionDraft::new(text), cx())
        .await
        .expect("submit")
        .wait(cx())
        .await
        .expect("answered");
}

/// The conversation's entries, oldest first.
pub(crate) async fn entries(conversation: &Conversation) -> Vec<EntryRecord> {
    let page = conversation
        .entries(ConversationEntryQuery::default(), 10_000, None, cx())
        .await
        .expect("entries");
    page.items.into_iter().rev().collect()
}

/// The entry kinds of the conversation, oldest first.
pub(crate) async fn kinds(conversation: &Conversation) -> Vec<String> {
    entries(conversation)
        .await
        .into_iter()
        .map(|entry| entry.kind)
        .collect()
}

/// A worker `create`d on a fresh durable session (temp agent dir, `work/`
/// cwd) whose faux script answers `responses` (the script's `responses`
/// array) in order. The temp dir lives
/// as long as the returned guard.
pub(crate) async fn created_worker(
    active_session_id: &str,
    responses: serde_json::Value,
) -> (tempfile::TempDir, std::sync::Arc<crate::worker::Worker>) {
    created_worker_with(active_session_id, responses, serde_json::json!({})).await
}

/// [`created_worker`] with extra `create` payload fields (`noSession`, ...).
pub(crate) async fn created_worker_with(
    active_session_id: &str,
    responses: serde_json::Value,
    create: serde_json::Value,
) -> (tempfile::TempDir, std::sync::Arc<crate::worker::Worker>) {
    let dir = tempfile::tempdir().expect("tempdir");
    let cwd = dir.path().join("work");
    std::fs::create_dir_all(&cwd).expect("cwd");
    let config = crate::worker::WorkerConfig {
        socket_path: dir.path().join("worker.sock"),
        supervisor_socket_path: PathBuf::new(),
        token: "token".to_owned(),
        worker_instance_id: String::new(),
        active_session_id: active_session_id.to_owned(),
        agent_dir: dir.path().join("agent"),
        recovery_journal_path: dir.path().join("recovery.jsonl"),
        telemetry_disabled: None,
        script: Some(serde_json::json!({ "responses": responses })),
    };
    let worker = std::sync::Arc::new(crate::worker::Worker::new(config, None));
    let mut payload =
        serde_json::json!({ "cwd": cwd.to_string_lossy(), "name": active_session_id });
    if let (Some(payload), Some(extra)) = (payload.as_object_mut(), create.as_object()) {
        payload.extend(extra.clone());
    }
    let created = worker.dispatch("create", &payload).await;
    assert!(created.success, "create failed: {created:?}");
    (dir, worker)
}

/// The hosted session's main-conversation entries, oldest first.
pub(crate) async fn worker_entries(worker: &crate::worker::Worker) -> Vec<EntryRecord> {
    let hosted = worker.session.get().expect("a hosted session");
    entries(&hosted.main().expect("main conversation")).await
}

/// The wire messages (`entry_wire_message`) of the main-conversation
/// entries of `kind`, oldest first.
pub(crate) async fn worker_rows(
    worker: &crate::worker::Worker,
    kind: &str,
) -> Vec<serde_json::Value> {
    worker_entries(worker)
        .await
        .iter()
        .filter(|entry| entry.kind == kind)
        .filter_map(crate::worker::durable_host::wire_messages::entry_wire_message)
        .collect()
}

/// Poll until the worker's shown conversation reads `busy` (a run started or
/// ended on the event bridge).
pub(crate) async fn wait_busy(worker: &crate::worker::Worker, busy: bool) {
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(10);
    loop {
        let now = worker
            .core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .is_busy();
        if now == busy {
            return;
        }
        assert!(
            std::time::Instant::now() < deadline,
            "the session never became busy={busy}"
        );
        tokio::time::sleep(std::time::Duration::from_millis(10)).await;
    }
}

/// The main conversation's queued inbox items as `(mode, preview)` pairs
/// (`write` rows preview empty), in inbox order.
pub(crate) async fn worker_inbox(worker: &crate::worker::Worker) -> Vec<(String, String)> {
    use eukhe_durable::harness::{InboxItem, InboxState, INBOX_DOC};
    let hosted = worker.session.get().expect("a hosted session");
    let main = hosted.main().expect("main conversation");
    let Some(value) = hosted
        .harness()
        .snapshot(&INBOX_DOC, main.id(), cx())
        .await
        .expect("inbox")
    else {
        return Vec::new();
    };
    let inbox: InboxState =
        eukhe_chord::json::from_json(&eukhe_chord::json::JsonValue::Object(value))
            .expect("inbox state");
    inbox
        .items
        .into_iter()
        .map(|item| match item {
            InboxItem::Steer { content, .. } => (
                "steer".to_owned(),
                crate::worker::durable_host::bridge::content_preview(&content),
            ),
            InboxItem::FollowUp { content, .. } => (
                "followUp".to_owned(),
                crate::worker::durable_host::bridge::content_preview(&content),
            ),
            InboxItem::Write { .. } => ("write".to_owned(), String::new()),
        })
        .collect()
}
