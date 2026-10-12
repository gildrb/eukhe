use serde_json::json;

use super::*;

fn registry(dir: &std::path::Path) -> HostRequestRegistry {
    let registry = HostRequestRegistry::default();
    let host = DocumentsHost {
        documents: eukhe_docs::Documents::new(dir.join("locks"), None),
        kernel_cwds: std::sync::Mutex::default(),
    };
    register(&registry, &Arc::new(host));
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

#[tokio::test]
async fn edit_grep_and_glob_share_the_read_anchors() {
    let dir = tempfile::tempdir().unwrap();
    std::fs::write(dir.path().join("a.rs"), "fn one() {}\nfn two() {}\n").unwrap();
    let registry = registry(dir.path());
    let cwd = dir.path().to_str().unwrap();
    let grep = call(
        &registry,
        "fs.grep",
        json!({"cwd": cwd, "pattern": "two", "path": "a.rs", "glob": null,
               "ignore_case": false, "context": 0, "skip": 0, "limit": null}),
    )
    .await;
    let tag = eukhe_docs::file_hash("fn one() {}\nfn two() {}\n");
    assert_eq!(
        (
            &grep["version"],
            &grep["files"][0]["matches"],
            &grep["files"][0]["tag"]
        ),
        (&json!("grep@1"), &json!([[2, "fn two() {}"]]), &json!(tag))
    );
    let unseen = call(
        &registry,
        "fs.edit",
        json!({"cwd": cwd, "input": format!("[a.rs#{tag}]\nPUT 1.=1:\n+x")}),
    )
    .await;
    assert_eq!(
        (&unseen["outcome"], &unseen["version"]),
        (&json!("rejected"), &json!("edit@hl.1"))
    );
    let edited = call(
        &registry,
        "fs.edit",
        json!({"cwd": cwd, "input": format!("[a.rs#{tag}]\nPUT 2.=2:\n+fn three() {{}}")}),
    )
    .await;
    assert_eq!(
        (
            &edited["outcome"],
            &edited["version"],
            &edited["files"][0]["change"]
        ),
        (&json!("done"), &json!("edit@hl.1"), &json!("updated"))
    );
    assert_eq!(
        std::fs::read_to_string(dir.path().join("a.rs")).unwrap(),
        "fn one() {}\nfn three() {}\n"
    );
    let globbed = call(
        &registry,
        "fs.glob",
        json!({"cwd": cwd, "path": "*.rs", "hidden": false, "limit": null}),
    )
    .await;
    assert_eq!(
        (&globbed["version"], &globbed["paths"]),
        (&json!("glob@1"), &json!(["a.rs"]))
    );
}
