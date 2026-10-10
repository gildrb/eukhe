use serde_json::json;

use super::*;
use crate::durable_test_support::{answer, ask, cx, kinds, Fixture, SESSION_ID};

fn small_keep_window(fixture: &Fixture) {
    fixture.settings(&json!({ "compaction": { "keepRecentTokens": 1 } }));
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn manual_compaction_answers_the_ts_result_and_places_the_summary() {
    let fixture = Fixture::new();
    small_keep_window(&fixture);
    let session = fixture.open(SESSION_ID).await;
    let root = session.root().clone();
    ask(&fixture, &root, "first question", "first answer").await;
    ask(&fixture, &root, "second question", "second answer").await;

    fixture
        .faux
        .append_responses(vec![answer("The user asked two questions.")]);
    let result = run_manual_compaction(
        session.harness(),
        session.deps(),
        &root,
        Some("Be terse.".to_owned()),
        cx(),
    )
    .await
    .expect("compacted");
    assert_eq!(result["summary"], "The user asked two questions.");
    assert!(result["tokensBefore"].as_u64().unwrap() > 0);
    let first_kept = result["firstKeptEntryId"].as_str().unwrap().to_owned();
    assert!(!first_kept.is_empty());
    assert_eq!(
        result.as_object().unwrap().keys().collect::<Vec<_>>(),
        ["summary", "firstKeptEntryId", "tokensBefore"]
    );
    assert_eq!(
        kinds(&root).await.last().map(String::as_str),
        Some("pi.compaction")
    );

    // The context now starts at the summary: a second run skips.
    let skipped = run_manual_compaction(session.harness(), session.deps(), &root, None, cx()).await;
    assert_eq!(
        skipped,
        Err(ManualCompactionError::Skipped(ALREADY_COMPACTED))
    );
    session.close(cx()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_short_session_skips_with_the_ts_message() {
    let fixture = Fixture::new();
    let session = fixture.open(SESSION_ID).await;
    let root = session.root().clone();
    ask(&fixture, &root, "hi", "hello").await;
    let skipped = run_manual_compaction(session.harness(), session.deps(), &root, None, cx()).await;
    assert_eq!(
        skipped,
        Err(ManualCompactionError::Skipped(TOO_SHORT_TO_COMPACT))
    );
    assert_eq!(
        skipped.unwrap_err().to_string(),
        "Session is too short to compact -- try again once it grows"
    );
    assert!(!kinds(&root)
        .await
        .iter()
        .any(|kind| kind == "pi.compaction"));
    session.close(cx()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn abort_with_no_live_compaction_is_a_no_op() {
    let fixture = Fixture::new();
    let session = fixture.open(SESSION_ID).await;
    let root = session.root().clone();
    let aborted = abort_compactions(session.harness(), &root, cx())
        .await
        .unwrap();
    assert_eq!(aborted, 0);
    session.close(cx()).await.unwrap();
}
