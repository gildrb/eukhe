use serde_json::Value;

use super::*;
use crate::durable_test_support::{ask, cx, Fixture, SESSION_ID};

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn export_jsonl_chains_the_history_linearly() {
    let fixture = Fixture::new();
    let session = fixture.open(SESSION_ID).await;
    let root = session.root().clone();
    ask(&fixture, &root, "hi", "hello").await;

    let path = export_jsonl(session.deps(), &root, Some("out/export.jsonl"), cx())
        .await
        .expect("export");
    assert_eq!(PathBuf::from(&path), fixture.cwd.join("out/export.jsonl"));
    let body = std::fs::read_to_string(&path).expect("read export");
    let lines: Vec<Value> = body
        .lines()
        .map(|line| serde_json::from_str(line).expect("json line"))
        .collect();
    assert_eq!(lines[0]["type"], "session");
    assert_eq!(lines[0]["id"], SESSION_ID);
    // One linear chain: each line's parent is the line before it.
    let parents: Vec<&Value> = lines[1..].iter().map(|line| &line["parentId"]).collect();
    let mut expected = vec![&Value::Null];
    expected.extend(lines[1..lines.len() - 1].iter().map(|line| &line["id"]));
    assert_eq!(parents, expected);
    let shape: Vec<(&str, &str)> = lines[1..]
        .iter()
        .map(|line| {
            (
                line["type"].as_str().unwrap_or_default(),
                line["message"]["role"]
                    .as_str()
                    .or_else(|| line["customType"].as_str())
                    .unwrap_or_default(),
            )
        })
        .collect();
    assert_eq!(
        shape,
        [
            ("message", "user"),
            ("custom_message", "harness_digest"),
            ("message", "assistant")
        ]
    );
    assert_eq!(
        lines[1]
            .as_object()
            .unwrap()
            .keys()
            .take(4)
            .collect::<Vec<_>>(),
        ["type", "id", "parentId", "timestamp"]
    );
    session.close(cx()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn export_html_writes_the_session_data() {
    let fixture = Fixture::new();
    let session = fixture.open(SESSION_ID).await;
    let root = session.root().clone();
    ask(&fixture, &root, "hi", "hello").await;
    let out = fixture.dir.path().join("export.html");
    let path = export_html(session.deps(), &root, Some(&out.to_string_lossy()), cx())
        .await
        .expect("export");
    assert_eq!(path, out.to_string_lossy());
    let html = std::fs::read_to_string(&out).expect("read export");
    assert!(html.contains("Session Export"));
    session.close(cx()).await.unwrap();
}
