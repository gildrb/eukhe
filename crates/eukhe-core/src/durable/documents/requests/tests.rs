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

async fn call(
    registry: &HostRequestRegistry,
    request_type: &str,
    cwd: &Path,
    args: Value,
) -> Value {
    let handler = registry.get(request_type).unwrap();
    handler(HostCall {
        data: json!({"type": request_type, "cwd": cwd, "args": args}),
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
    let tag = eukhe_docs::file_hash("a\nb\n");
    let written = call(
        &registry,
        "fs.write",
        dir.path(),
        json!({"path": "x.txt", "content": "a\nb\n"}),
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
            "warnings": [],
        })
    );
    let read = call(
        &registry,
        "fs.read",
        dir.path(),
        json!({"path": "x.txt:2-2"}),
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
            "warnings": [],
        })
    );
}

#[tokio::test]
async fn read_rejection_carries_reason_and_message() {
    let dir = tempfile::tempdir().unwrap();
    let registry = registry(dir.path());
    let reply = call(&registry, "fs.read", dir.path(), json!({"path": "nope.rs"})).await;
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
async fn kernel_arguments_repair_by_the_wire_contract() {
    let dir = tempfile::tempdir().unwrap();
    std::fs::write(dir.path().join("a.rs"), "fn one() {}\n").unwrap();
    let registry = registry(dir.path());
    let repaired = call(
        &registry,
        "fs.grep",
        dir.path(),
        json!({"regex": "ONE", "file_path": "a.rs", "case": "false"}),
    )
    .await;
    assert_eq!(
        (
            &repaired["outcome"],
            &repaired["files"][0]["matches"],
            &repaired["warnings"]
        ),
        (
            &json!("done"),
            &json!([[1, "fn one() {}"]]),
            &json!([
                "Repaired argument: regex read as pattern",
                "Repaired argument: file_path read as path",
                "Repaired argument: case=\"false\" read as false",
            ])
        )
    );
    let unknown = call(
        &registry,
        "fs.read",
        dir.path(),
        json!({"path": "a.rs", "offset": 3}),
    )
    .await;
    assert_eq!(
        unknown,
        json!({
            "outcome": "rejected",
            "version": "read@1",
            "reason": "arguments",
            "message": "read has no argument `offset`. Valid arguments: i, path.",
        })
    );
    let refused = call(
        &registry,
        "fs.edit",
        dir.path(),
        json!({"old_string": "one", "new_string": "two"}),
    )
    .await;
    assert_eq!(
        (&refused["reason"], &refused["message"]),
        (
            &json!("arguments"),
            &json!("edit does not take `old_string`: edit takes a hashline patch, not old/new strings. read or grep the file, then send '[path#TAG]\\nPUT 12.=14:\\n+new line' with the header and line numbers they printed.")
        )
    );
}

#[tokio::test]
async fn edit_grep_and_glob_share_the_read_anchors() {
    let dir = tempfile::tempdir().unwrap();
    std::fs::write(dir.path().join("a.rs"), "fn one() {}\nfn two() {}\n").unwrap();
    let registry = registry(dir.path());
    let grep = call(
        &registry,
        "fs.grep",
        dir.path(),
        json!({"pattern": "two", "path": "a.rs"}),
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
    let edited = call(
        &registry,
        "fs.edit",
        dir.path(),
        json!({"input": format!("[a.rs#{tag}]\nPUT 2.=2:\n+fn three() {{}}")}),
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
    let globbed = call(&registry, "fs.glob", dir.path(), json!({"path": "*.rs"})).await;
    assert_eq!(
        (&globbed["version"], &globbed["paths"]),
        (&json!("glob@1"), &json!(["a.rs"]))
    );
}
