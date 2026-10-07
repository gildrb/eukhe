//! Listing, recency, and selector resolution over durable storages and
//! legacy files. Also the session fixtures of the fork tests.

use std::path::{Path, PathBuf};
use std::time::{Duration, SystemTime};

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::harness::types::{InputSubmissionDraft, ModelRef};
use eukhe_durable::harness::{Conversation, ConversationEntryQuery};
use eukhe_durable::types::EntryRecord;
use eukhe_pi_ai::models::Models;
use eukhe_pi_ai::providers::faux_script::{create_faux_script_models, parse_faux_script};
use eukhe_types::pi_ai::{AssistantContentBlock, Message, UserContent, UserContentBlock};
use serde_json::json;

use super::*;
use crate::durable::{open_session, EukheSession, SessionConfig, SessionStorage};
use crate::session::discovery::SessionSelectorError;

pub(crate) fn cx() -> &'static Context {
    &BACKGROUND_CONTEXT
}

/// A sessions directory, an agent directory, and faux models answering
/// `answer 1`, `answer 2`, ...
pub(crate) struct Fixture {
    dir: tempfile::TempDir,
    pub(crate) agent_dir: PathBuf,
    pub(crate) sessions: PathBuf,
    models: Models,
}

pub(crate) fn fixture() -> Fixture {
    let dir = tempfile::tempdir().expect("tempdir");
    let agent_dir = dir.path().join("agent");
    let sessions = agent_dir.join("sessions");
    std::fs::create_dir_all(&sessions).expect("sessions dir");
    let responses: Vec<String> = (1..=20).map(|index| format!("answer {index}")).collect();
    let script = parse_faux_script(&json!({ "responses": responses }).to_string()).expect("script");
    let (models, _provider) = create_faux_script_models(script);
    Fixture {
        dir,
        agent_dir,
        sessions,
        models,
    }
}

impl Fixture {
    /// A project directory `name` (created).
    pub(crate) fn project(&self, name: &str) -> PathBuf {
        let path = self.dir.path().join(name);
        std::fs::create_dir_all(&path).expect("project");
        path
    }

    pub(crate) fn config(&self, id: &str, dir: &Path, cwd: &Path) -> SessionConfig {
        let mut config = SessionConfig::new(
            &self.agent_dir,
            cwd,
            id,
            SessionStorage::Jsonl {
                dir: dir.to_owned(),
                fsync: true,
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

    /// Open the session `id` in its storage directory.
    pub(crate) async fn open(&self, id: &str, cwd: &Path) -> EukheSession {
        let dir = self.sessions.join(id);
        open_session(self.config(id, &dir, cwd), cx())
            .await
            .expect("open")
    }

    /// A durable session `id` at `cwd` that was asked `prompts`; returns its
    /// main conversation's entries, oldest first.
    pub(crate) async fn durable(&self, id: &str, cwd: &Path, prompts: &[&str]) -> Vec<EntryRecord> {
        let session = self.open(id, cwd).await;
        for prompt in prompts {
            session
                .main()
                .submit(InputSubmissionDraft::new(*prompt), cx())
                .await
                .expect("submit")
                .wait(cx())
                .await
                .expect("wait");
        }
        let entries = entries(&session.main()).await;
        session.close(cx()).await.expect("close");
        entries
    }

    /// A legacy `<id>.jsonl` at `cwd` holding one question and its answer.
    pub(crate) fn legacy(&self, id: &str, cwd: &Path) -> PathBuf {
        let path = self.sessions.join(format!("{id}.jsonl"));
        let rows = [
            json!({"type": "session", "version": 3, "id": id,
                "timestamp": "2024-01-01T00:00:00.000Z", "cwd": cwd}),
            json!({"type": "model_change", "id": "m1", "parentId": null,
                "timestamp": "2024-01-01T00:00:00.500Z", "provider": "faux", "modelId": "faux-1"}),
            json!({"type": "message", "id": "u1", "parentId": "m1",
                "timestamp": "2024-01-01T00:00:01.000Z",
                "message": {"role": "user", "content": [{"type": "text", "text": "legacy question"}],
                    "timestamp": 1000}}),
            json!({"type": "message", "id": "a1", "parentId": "u1",
                "timestamp": "2024-01-01T00:00:02.000Z",
                "message": {"role": "assistant",
                    "content": [{"type": "text", "text": "legacy answer"}],
                    "api": "faux", "provider": "faux", "model": "faux-1",
                    "usage": {"input": 1, "output": 1, "cacheRead": 0, "cacheWrite": 0,
                        "totalTokens": 2,
                        "cost": {"input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0,
                            "total": 0}},
                    "stopReason": "stop", "timestamp": 2000}}),
        ];
        let mut content = String::new();
        for row in &rows {
            content.push_str(&row.to_string());
            content.push('\n');
        }
        std::fs::write(&path, content).expect("legacy file");
        path
    }
}

/// A conversation's entries, oldest first.
pub(crate) async fn entries(conversation: &Conversation) -> Vec<EntryRecord> {
    let page = conversation
        .entries(ConversationEntryQuery::default(), 1000, None, cx())
        .await
        .expect("entries");
    page.items.into_iter().rev().collect()
}

fn text_of(message: &Message) -> Option<String> {
    match message {
        Message::User(message) => match &message.content {
            UserContent::Text(text) => Some(text.clone()),
            UserContent::Blocks(blocks) => blocks.iter().find_map(|block| match block {
                UserContentBlock::Text(text) => Some(text.text.clone()),
                UserContentBlock::Image(_) => None,
            }),
        },
        Message::Assistant(message) => message.content.iter().find_map(|block| match block {
            AssistantContentBlock::Text(text) => Some(text.text.clone()),
            AssistantContentBlock::Thinking(_) | AssistantContentBlock::ToolCall(_) => None,
        }),
        Message::System(_) | Message::ToolResult(_) => None,
    }
}

/// The user and assistant texts of `entries`, in order.
pub(crate) fn texts(entries: &[EntryRecord]) -> Vec<String> {
    entries
        .iter()
        .filter(|entry| entry.kind == "pi.user" || entry.kind == "pi.assistant")
        .filter_map(|entry| entry.model.as_ref()?.first().and_then(text_of))
        .collect()
}

/// `1_700_000_000 + seconds` after the epoch.
fn at(seconds: u64) -> SystemTime {
    SystemTime::UNIX_EPOCH + Duration::from_secs(1_700_000_000 + seconds)
}

/// Set the mtime of `path` (a file, or every file of a directory).
fn touch(path: &Path, modified: SystemTime) {
    let files: Vec<PathBuf> = if path.is_dir() {
        std::fs::read_dir(path)
            .expect("read dir")
            .map(|entry| entry.expect("entry").path())
            .filter(|path| path.is_file())
            .collect()
    } else {
        vec![path.to_owned()]
    };
    for file in files {
        std::fs::File::options()
            .append(true)
            .open(&file)
            .expect("open")
            .set_modified(modified)
            .expect("set mtime");
    }
}

fn cwd_string(path: &Path) -> String {
    path.to_string_lossy().into_owned()
}

#[tokio::test]
async fn lists_durable_and_legacy_sessions_newest_first() {
    let fixture = fixture();
    let alpha = fixture.project("alpha");
    let beta = fixture.project("beta");
    fixture.durable("durable-1", &alpha, &["hello"]).await;
    let legacy = fixture.legacy("legacy-1", &beta);
    // Not sessions: a hidden staging dir, a dir without a commit log, a
    // header-less file.
    std::fs::create_dir_all(fixture.sessions.join(".x.import-1")).expect("staging");
    std::fs::create_dir_all(fixture.sessions.join("artifacts")).expect("other dir");
    std::fs::write(fixture.sessions.join("broken.jsonl"), "not json\n").expect("broken");
    let durable_dir = fixture.sessions.join("durable-1");
    touch(&durable_dir, at(20));
    touch(&legacy, at(10));

    assert_eq!(
        list_sessions(&fixture.sessions, cx()).await,
        vec![
            SessionListing {
                id: "durable-1".to_owned(),
                location: SessionLocation::Durable(durable_dir.clone()),
                cwd: cwd_string(&alpha),
                modified: at(20),
            },
            SessionListing {
                id: "legacy-1".to_owned(),
                location: SessionLocation::Legacy(legacy.clone()),
                cwd: cwd_string(&beta),
                modified: at(10),
            },
        ]
    );
}

#[tokio::test]
async fn a_legacy_file_is_listed_as_its_storage_once_imported() {
    let fixture = fixture();
    let beta = fixture.project("beta");
    let legacy = fixture.legacy("legacy-1", &beta);
    let listed = list_sessions(&fixture.sessions, cx()).await;
    assert_eq!(listed.len(), 1);
    assert_eq!(
        listed[0].storage_dir(&fixture.sessions),
        fixture.sessions.join("legacy-1")
    );

    // Opening imports it into `<id>/`; the file stays and is hidden.
    let other = fixture.project("other");
    let session = fixture.open("legacy-1", &other).await;
    session.close(cx()).await.expect("close");
    assert!(legacy.is_file());
    let storage = fixture.sessions.join("legacy-1");
    touch(&storage, at(30));
    let imported = SessionListing {
        id: "legacy-1".to_owned(),
        location: SessionLocation::Durable(storage.clone()),
        cwd: cwd_string(&beta),
        modified: at(30),
    };
    assert_eq!(
        list_sessions(&fixture.sessions, cx()).await,
        vec![imported.clone()]
    );
    // The legacy location reads the imported storage's cwd.
    assert_eq!(
        read_session_cwd(&SessionLocation::Legacy(legacy), cx()).await,
        Some(cwd_string(&beta))
    );
    assert_eq!(
        read_session_cwd(&SessionLocation::Durable(storage), cx()).await,
        Some(cwd_string(&beta))
    );
}

#[tokio::test]
async fn listing_reads_without_writing_the_storage() {
    let fixture = fixture();
    let alpha = fixture.project("alpha");
    fixture.durable("durable-1", &alpha, &["hello"]).await;
    let dir = fixture.sessions.join("durable-1");
    // A torn sidecar tail, as a writer mid-commit leaves it.
    let sidecar = std::fs::read_dir(&dir)
        .expect("read dir")
        .map(|entry| entry.expect("entry").path())
        .find(|path| {
            path.file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| name.starts_with("doc-"))
        })
        .expect("a document sidecar");
    let mut torn = std::fs::read(&sidecar).expect("sidecar");
    torn.extend_from_slice(b"{\"format\":1,\"type\":\"record\",\"seq\":99999");
    std::fs::write(&sidecar, &torn).expect("torn tail");
    let before: Vec<(PathBuf, Vec<u8>)> = snapshot_files(&dir);

    let listed = list_sessions(&fixture.sessions, cx()).await;
    assert_eq!(listed.len(), 1);
    assert_eq!(listed[0].cwd, cwd_string(&alpha));
    assert_eq!(snapshot_files(&dir), before);
}

/// `(path, bytes)` of every file of `dir`, sorted.
pub(crate) fn snapshot_files(dir: &Path) -> Vec<(PathBuf, Vec<u8>)> {
    let mut files: Vec<(PathBuf, Vec<u8>)> = std::fs::read_dir(dir)
        .expect("read dir")
        .map(|entry| entry.expect("entry").path())
        .filter(|path| path.is_file())
        .map(|path| {
            let bytes = std::fs::read(&path).expect("read");
            (path, bytes)
        })
        .collect();
    files.sort();
    files
}

#[tokio::test]
async fn reads_the_main_transcript_read_only() {
    let fixture = fixture();
    let alpha = fixture.project("alpha");
    let expected = fixture.durable("durable-1", &alpha, &["hello"]).await;
    let dir = fixture.sessions.join("durable-1");
    let before = snapshot_files(&dir);
    let transcript = read_main_transcript(&SessionLocation::Durable(dir.clone()), cx())
        .await
        .expect("transcript");
    assert_eq!(snapshot_files(&dir), before);
    assert_eq!(transcript.main, ROOT_CONVERSATION_ID);
    assert_eq!(transcript.entries, expected);
    assert_eq!(texts(&transcript.entries), ["hello", "answer 1"]);
    assert_eq!(
        transcript.agent.model,
        Some(ModelRef {
            provider: "faux".to_owned(),
            model_id: "faux-1".to_owned(),
        })
    );
    assert_eq!(transcript.agent.cwd, Some(cwd_string(&alpha)));

    let legacy = fixture.legacy("legacy-1", &alpha);
    let error = read_main_transcript(&SessionLocation::Legacy(legacy), cx())
        .await
        .expect_err("a legacy file not imported");
    assert_eq!(
        error.to_string(),
        format!(
            "no durable session storage at {}",
            fixture.sessions.join("legacy-1").display()
        )
    );
}

#[tokio::test]
async fn most_recent_session_for_cwd_prefers_the_newest_of_that_cwd() {
    let fixture = fixture();
    let alpha = fixture.project("alpha");
    let beta = fixture.project("beta");
    fixture.durable("older", &alpha, &[]).await;
    fixture.durable("newer", &alpha, &[]).await;
    fixture.durable("elsewhere", &beta, &[]).await;
    let legacy = fixture.legacy("legacy-alpha", &alpha);
    touch(&fixture.sessions.join("older"), at(10));
    touch(&fixture.sessions.join("newer"), at(30));
    touch(&fixture.sessions.join("elsewhere"), at(50));
    touch(&legacy, at(20));

    let newest = most_recent_session_for_cwd(&fixture.sessions, &alpha, cx())
        .await
        .expect("a session");
    assert_eq!(
        newest,
        SessionListing {
            id: "newer".to_owned(),
            location: SessionLocation::Durable(fixture.sessions.join("newer")),
            cwd: cwd_string(&alpha),
            modified: at(30),
        }
    );
    let gamma = fixture.project("gamma");
    assert_eq!(
        most_recent_session_for_cwd(&fixture.sessions, &gamma, cx()).await,
        None
    );
}

#[tokio::test]
async fn resolves_selectors_by_tier() {
    let fixture = fixture();
    let alpha = fixture.project("alpha");
    let beta = fixture.project("beta");
    let local_id = "01a0ab79-503d-768f-bfe5-19a937ded438";
    fixture.durable(local_id, &alpha, &[]).await;
    fixture.durable("aaaa0001", &beta, &[]).await;
    let legacy = fixture.legacy("aaaa0002", &beta);
    fixture.legacy("bbbb0001", &beta);
    touch(&fixture.sessions.join(local_id), at(10));
    touch(&fixture.sessions.join("aaaa0001"), at(10));
    touch(&legacy, at(10));
    touch(&fixture.sessions.join("bbbb0001.jsonl"), at(10));
    let listing = |id: &str, location: SessionLocation, cwd: &Path| SessionListing {
        id: id.to_owned(),
        location,
        cwd: cwd_string(cwd),
        modified: at(10),
    };
    let resolve = |selector: &'static str| {
        let alpha = alpha.clone();
        let sessions = fixture.sessions.clone();
        async move { resolve_session(selector, &alpha, &sessions, cx()).await }
    };

    // Exact local, by normalized id.
    assert_eq!(
        resolve("01A0AB79503D768FBFE519A937DED438").await,
        Ok(ResolvedListing::Local(listing(
            local_id,
            SessionLocation::Durable(fixture.sessions.join(local_id)),
            &alpha
        )))
    );
    // Partial local (prefix).
    assert_eq!(
        resolve("01a0ab79").await,
        Ok(ResolvedListing::Local(listing(
            local_id,
            SessionLocation::Durable(fixture.sessions.join(local_id)),
            &alpha
        )))
    );
    // Global: another project's legacy file.
    assert_eq!(
        resolve("bbbb").await,
        Ok(ResolvedListing::Global(listing(
            "bbbb0001",
            SessionLocation::Legacy(fixture.sessions.join("bbbb0001.jsonl")),
            &beta
        )))
    );
    // Exact global beats a partial match.
    assert_eq!(
        resolve("aaaa0002").await,
        Ok(ResolvedListing::Global(listing(
            "aaaa0002",
            SessionLocation::Legacy(legacy.clone()),
            &beta
        )))
    );
    // Ambiguous partial global, newest-first listing order (ties by id).
    let ambiguous = resolve("aaaa").await.unwrap_err();
    assert_eq!(
        ambiguous,
        SessionSelectorError::Ambiguous {
            selector: "aaaa".to_owned(),
            matches: vec!["aaaa0001".to_owned(), "aaaa0002".to_owned()],
        }
    );
    assert_eq!(
        ambiguous.message(),
        "Ambiguous saved session \"aaaa\": matches aaaa0001, aaaa0002"
    );
    // Not found, with a suggestion.
    let missing = resolve("01a0ab79-503d-768f-bfee5-19a937ded438")
        .await
        .unwrap_err();
    assert_eq!(
        missing,
        SessionSelectorError::NotFound {
            selector: "01a0ab79-503d-768f-bfee5-19a937ded438".to_owned(),
            suggestion: Some(local_id.to_owned()),
        }
    );
    assert_eq!(
        missing.message(),
        "No session found matching '01a0ab79-503d-768f-bfee5-19a937ded438'"
    );
}

#[tokio::test]
async fn path_like_selectors_name_a_location() {
    let fixture = fixture();
    let alpha = fixture.project("alpha");
    let dir = fixture.sessions.join("some-session");
    std::fs::create_dir_all(&dir).expect("dir");
    let resolve = |selector: String| {
        let alpha = alpha.clone();
        let sessions = fixture.sessions.clone();
        async move { resolve_session(&selector, &alpha, &sessions, cx()).await }
    };
    assert_eq!(
        resolve(cwd_string(&dir)).await,
        Ok(ResolvedListing::Path(SessionLocation::Durable(dir.clone())))
    );
    let file = fixture.sessions.join("old.jsonl");
    assert_eq!(
        resolve(cwd_string(&file)).await,
        Ok(ResolvedListing::Path(SessionLocation::Legacy(file.clone())))
    );
    assert_eq!(
        SessionLocation::Legacy(file).storage_dir(),
        fixture.sessions.join("old")
    );
    assert_eq!(
        resolve("new/session".to_owned()).await,
        Ok(ResolvedListing::Path(SessionLocation::Durable(
            PathBuf::from("new/session")
        )))
    );
}
