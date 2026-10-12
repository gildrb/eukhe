//! Forks of durable and legacy sources into new storages.

use std::path::Path;

use eukhe_chord::json::from_json;
use eukhe_durable::harness::types::ModelRef;
use eukhe_durable::ids::mint;
use eukhe_durable::types::{
    DocumentId, DocumentPoint, Storage, StorageWrite, ROOT_CONVERSATION_ID,
};
use serde_json::json;

use super::*;
use crate::durable::discovery::tests::{cx, entries, fixture, snapshot_files, texts, Fixture};
use crate::durable::read_session_cwd;

/// Open the forked storage `id` and return its main conversation's id and
/// texts, plus its agent cwd.
async fn opened_fork(
    fixture: &Fixture,
    id: &str,
    cwd: &Path,
) -> (ConversationId, Vec<String>, Option<String>) {
    let session = fixture.open(id, cwd).await;
    let main = session.main();
    let texts = texts(&entries(&main).await);
    let agent = main.agent(cx()).await.expect("agent");
    assert_eq!(
        agent.model,
        Some(ModelRef {
            provider: "faux".to_owned(),
            model_id: "faux-1".to_owned(),
        })
    );
    let id = main.id();
    session.close(cx()).await.expect("close");
    (id, texts, agent.cwd)
}

fn cwd_string(path: &Path) -> String {
    path.to_string_lossy().into_owned()
}

#[tokio::test]
async fn forks_a_durable_session_at_an_entry_leaving_the_source() {
    let fixture = fixture();
    let alpha = fixture.project("alpha");
    let source_entries = fixture
        .durable("source", &alpha, &["first", "second"])
        .await;
    let source_dir = fixture.sessions.join("source");
    let before = snapshot_files(&source_dir);
    let at = source_entries
        .iter()
        .find(|entry| entry.kind == "pi.assistant")
        .expect("first answer")
        .id;

    let new_dir = fixture.sessions.join("fork-1");
    let forked = fork_session(
        &SessionLocation::Durable(source_dir.clone()),
        ForkPoint::Entry(at),
        None,
        &new_dir,
        cx(),
    )
    .await
    .expect("fork");
    assert_eq!(forked.dir, new_dir);
    assert_eq!(snapshot_files(&source_dir), before);
    let leftovers: Vec<_> = std::fs::read_dir(&fixture.sessions)
        .expect("sessions")
        .map(|entry| {
            entry
                .expect("entry")
                .file_name()
                .to_string_lossy()
                .into_owned()
        })
        .filter(|name| name.starts_with('.'))
        .collect();
    assert_eq!(leftovers, Vec::<String>::new());

    let (main, texts, cwd) = opened_fork(&fixture, "fork-1", &alpha).await;
    assert_eq!(main, forked.main);
    assert_eq!(texts, ["first", "answer 1"]);
    assert_eq!(cwd, Some(cwd_string(&alpha)));

    // The source still opens with its root as main and every entry.
    let session = fixture.open("source", &alpha).await;
    assert_eq!(session.main().id(), session.root().id());
    assert_eq!(
        crate::durable::discovery::tests::texts(&entries(&session.main()).await),
        ["first", "answer 1", "second", "answer 2"]
    );
    session.close(cx()).await.expect("close");
}

#[tokio::test]
async fn forks_at_the_latest_entry_with_a_new_cwd() {
    let fixture = fixture();
    let alpha = fixture.project("alpha");
    let beta = fixture.project("beta");
    fixture.durable("source", &alpha, &["first"]).await;
    let new_dir = fixture.sessions.join("fork-1");
    let forked = fork_session(
        &SessionLocation::Durable(fixture.sessions.join("source")),
        ForkPoint::Latest,
        Some(&beta),
        &new_dir,
        cx(),
    )
    .await
    .expect("fork");
    assert_eq!(
        read_session_cwd(&SessionLocation::Durable(new_dir), cx()).await,
        Some(cwd_string(&beta))
    );
    let (main, texts, cwd) = opened_fork(&fixture, "fork-1", &beta).await;
    assert_eq!(main, forked.main);
    assert_eq!(texts, ["first", "answer 1"]);
    assert_eq!(cwd, Some(cwd_string(&beta)));
}

#[tokio::test]
async fn forks_at_the_start_with_the_source_agent() {
    let fixture = fixture();
    let alpha = fixture.project("alpha");
    fixture.durable("source", &alpha, &["first"]).await;
    let new_dir = fixture.sessions.join("fork-1");
    let forked = fork_session(
        &SessionLocation::Durable(fixture.sessions.join("source")),
        ForkPoint::Start,
        None,
        &new_dir,
        cx(),
    )
    .await
    .expect("fork");
    let (main, texts, cwd) = opened_fork(&fixture, "fork-1", &alpha).await;
    assert_eq!(main, forked.main);
    assert_eq!(texts, Vec::<String>::new());
    assert_eq!(cwd, Some(cwd_string(&alpha)));
}

#[tokio::test]
async fn forks_a_conversation_other_than_the_main_one() {
    let fixture = fixture();
    let alpha = fixture.project("alpha");
    let source_entries = fixture
        .durable("source", &alpha, &["first", "second"])
        .await;
    let at = source_entries
        .iter()
        .find(|entry| entry.kind == "pi.assistant")
        .expect("first answer")
        .id;
    // The source's main moves onto a fork at the first answer; the root
    // keeps the abandoned second turn.
    let session = fixture.open("source", &alpha).await;
    let root = session.root().id();
    fork_main_conversation(
        session.harness(),
        session.root(),
        ForkPoint::Entry(at),
        None,
        cx(),
    )
    .await
    .expect("in-place fork");
    session.close(cx()).await.expect("close");

    let new_dir = fixture.sessions.join("fork-1");
    let forked = fork_session_conversation(
        &SessionLocation::Durable(fixture.sessions.join("source")),
        root,
        ForkPoint::Latest,
        None,
        &new_dir,
        cx(),
    )
    .await
    .expect("fork");
    let (main, texts, _) = opened_fork(&fixture, "fork-1", &alpha).await;
    assert_eq!(main, forked.main);
    assert_eq!(texts, ["first", "answer 1", "second", "answer 2"]);
}

#[tokio::test]
async fn forks_a_legacy_file_without_importing_it_in_place() {
    let fixture = fixture();
    let beta = fixture.project("beta");
    let legacy = fixture.legacy("legacy-1", &beta);
    let before = std::fs::read(&legacy).expect("legacy");
    let new_dir = fixture.sessions.join("fork-1");
    let forked = fork_session(
        &SessionLocation::Legacy(legacy.clone()),
        ForkPoint::Latest,
        None,
        &new_dir,
        cx(),
    )
    .await
    .expect("fork");
    assert_eq!(std::fs::read(&legacy).expect("legacy"), before);
    assert!(!fixture.sessions.join("legacy-1").exists());
    let (main, texts, cwd) = opened_fork(&fixture, "fork-1", &beta).await;
    assert_eq!(main, forked.main);
    assert_eq!(texts, ["legacy question", "legacy answer"]);
    assert_eq!(cwd, Some(cwd_string(&beta)));
}

#[tokio::test]
async fn rejects_invalid_sources_and_existing_targets() {
    let fixture = fixture();
    let new_dir = fixture.sessions.join("fork-1");
    let empty = fixture.sessions.join("empty.jsonl");
    std::fs::write(&empty, "").expect("empty");
    let error = fork_session(
        &SessionLocation::Legacy(empty.clone()),
        ForkPoint::Latest,
        None,
        &new_dir,
        cx(),
    )
    .await
    .expect_err("an empty source");
    assert_eq!(
        error.to_string(),
        format!(
            "Cannot fork: source session file is empty or invalid: {}",
            empty.display()
        )
    );
    let missing = fixture.sessions.join("absent");
    let error = fork_session(
        &SessionLocation::Durable(missing.clone()),
        ForkPoint::Latest,
        None,
        &new_dir,
        cx(),
    )
    .await
    .expect_err("a missing source");
    assert_eq!(
        error.to_string(),
        format!(
            "Cannot fork: source session not found: {}",
            missing.display()
        )
    );
    assert_eq!(
        std::fs::read_dir(&fixture.sessions)
            .expect("sessions")
            .map(|entry| entry
                .expect("entry")
                .file_name()
                .to_string_lossy()
                .into_owned())
            .collect::<Vec<_>>(),
        ["empty.jsonl"]
    );

    let alpha = fixture.project("alpha");
    fixture.durable("source", &alpha, &[]).await;
    std::fs::create_dir_all(&new_dir).expect("target");
    let error = fork_session(
        &SessionLocation::Durable(fixture.sessions.join("source")),
        ForkPoint::Latest,
        None,
        &new_dir,
        cx(),
    )
    .await
    .expect_err("an existing target");
    assert_eq!(
        error.to_string(),
        format!("fork target {} already exists", new_dir.display())
    );
}

/// One storage write from its JSON form.
fn storage_write(value: serde_json::Value) -> StorageWrite {
    from_json(&JsonValue::from(value)).expect("storage write")
}

/// A commit published after a copy took the sidecars but before it took
/// `main.jsonl` tears the copy: its marker needs a sidecar record the copy
/// lacks. The attempt reports itself torn, and a retaken copy holds the
/// source's state.
#[tokio::test]
async fn judges_a_copy_torn_by_a_commit_published_mid_copy() {
    let dir = tempfile::tempdir().expect("tempdir");
    let source = dir.path().join("source");
    let writer = open_native_jsonl_storage(
        source.to_str().expect("utf-8"),
        cx(),
        JsonlStorageOptions::default(),
    )
    .await
    .expect("source");
    let root = json!({ "type": "conversation", "value": { "id": ROOT_CONVERSATION_ID.get() } });
    writer
        .commit(&[storage_write(root)], cx())
        .await
        .expect("root");
    let id: DocumentId = mint(&writer).await.expect("mint");
    let create = json!({
        "type": "document.create",
        "record": { "id": id.get(), "kind": "test.document", "scope": { "kind": "session" } },
        "content": { "kind": "base", "version": 1, "value": { "count": 0 } },
    });
    writer
        .commit(&[storage_write(create)], cx())
        .await
        .expect("create");

    let torn = dir.path().join("torn");
    let published = copy_without_main(&source, &torn).await.expect("copy");
    let delta = json!({
        "type": "document.change",
        "id": id.get(),
        "content": { "kind": "delta", "version": 1, "ops": [["s", ["count"], 1]] },
    });
    writer
        .commit(&[storage_write(delta)], cx())
        .await
        .expect("delta");
    assert_eq!(
        finish_copy(&source, &torn, published).await.expect("copy"),
        Snapshot::Torn
    );
    let error = open_native_jsonl_storage(
        torn.to_str().expect("utf-8"),
        cx(),
        JsonlStorageOptions::default(),
    )
    .await
    .expect_err("the torn copy lacks a confirmed record");
    assert_eq!(
        error.to_string(),
        format!("Missing confirmed sidecar record doc-{id}.jsonl at sequence 3")
    );

    let whole = dir.path().join("whole");
    copy_storage(&source, &whole).await.expect("copy");
    let copy = open_native_jsonl_storage(
        whole.to_str().expect("utf-8"),
        cx(),
        JsonlStorageOptions::default(),
    )
    .await
    .expect("the retaken copy opens");
    assert_eq!(
        copy.document(id, DocumentPoint::Current, cx())
            .await
            .expect("copy document"),
        writer
            .document(id, DocumentPoint::Current, cx())
            .await
            .expect("source document")
    );
    copy.close(cx()).await.expect("close copy");
    writer.close(cx()).await.expect("close source");
}
