use serde_json::json;

use super::*;

fn registry(dir: &std::path::Path) -> HostRequestRegistry {
    let registry = HostRequestRegistry::default();
    register(
        &registry,
        &Arc::new(Documents::new(dir.join("locks"), None)),
    );
    registry
}

async fn call(registry: &HostRequestRegistry, request_type: &str, data: Value) -> Value {
    let handler = registry.get(request_type).unwrap();
    handler(HostCall {
        data,
        cell_source_code: None,
        call: None,
    })
    .await
    .unwrap()
}

#[tokio::test]
async fn write_then_read_share_one_store() {
    let dir = tempfile::tempdir().unwrap();
    let registry = registry(dir.path());
    let cwd = dir.path().to_str().unwrap();
    let tag = eukhe_docs::file_hash("a\nb\n");
    let written = call(
        &registry,
        "fs.write",
        json!({"type": "fs.write", "cwd": cwd, "path": "x.txt", "content": "a\nb\n"}),
    )
    .await;
    assert_eq!(
        written,
        json!({
            "outcome": "done",
            "version": "write@1",
            "path": "x.txt",
            "absolute": dir.path().join("x.txt"),
            "created": true,
            "bytes": 4,
            "tag": tag,
            "made_executable": false,
            "rendered": format!("[x.txt#{tag}]\nSuccessfully wrote 4 bytes to x.txt"),
        })
    );
    let read = call(
        &registry,
        "fs.read",
        json!({"type": "fs.read", "cwd": cwd, "path": "x.txt:2-2"}),
    )
    .await;
    assert_eq!(
        read,
        json!({
            "outcome": "done",
            "version": "read@1",
            "path": "x.txt",
            "absolute": dir.path().join("x.txt"),
            "rendered": format!("[x.txt#{tag}]\n1:a\n2:b"),
            "diags": [],
            "kind": "file",
            "tag": tag,
            "text": "a\nb\n",
            "total_lines": 2,
            "shown": [[1, 2]],
        })
    );
}

#[tokio::test]
async fn read_rejection_carries_reason_and_message() {
    let dir = tempfile::tempdir().unwrap();
    let registry = registry(dir.path());
    let reply = call(
        &registry,
        "fs.read",
        json!({"cwd": dir.path(), "path": "nope.rs"}),
    )
    .await;
    assert_eq!(
        reply,
        json!({
            "outcome": "rejected",
            "version": "read@1",
            "reason": "not_found",
            "message": "Path 'nope.rs' not found",
        })
    );
}
