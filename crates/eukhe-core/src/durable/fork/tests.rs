//! Forks of durable and legacy sources into new storages.

use std::path::Path;

use eukhe_durable::harness::types::ModelRef;

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
