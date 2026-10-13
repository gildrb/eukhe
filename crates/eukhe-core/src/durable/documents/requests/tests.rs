use std::future::Future;
use std::sync::Mutex;

use eukhe_lsp::{LspHandle, LspHost};
use eukhe_types::lsp::{
    DiagnosticsReport, LspDiagnostic, LspError, LspOp, LspPoint, LspRequest, LspResponse,
    LspSeverity, LspSpan,
};
use serde_json::json;

use super::*;
use crate::durable::HarnessCell;

/// Language servers that answer every committed write with `report` and
/// record the written paths.
struct Servers {
    report: DiagnosticsReport,
    synced: Mutex<Vec<PathBuf>>,
}

impl LspHost for Servers {
    fn call(
        &self,
        request: LspRequest,
    ) -> impl Future<Output = Result<LspResponse, LspError>> + Send {
        let report = match request.op {
            LspOp::Sync { path, .. } => {
                self.synced.lock().unwrap().push(path);
                self.report.clone()
            }
            LspOp::AwaitDiagnostics { .. } => self.report.clone(),
            other => panic!("unscripted {other:?}"),
        };
        std::future::ready(Ok(LspResponse::Diagnostics(report)))
    }
}

fn registry_with(dir: &Path, report: DiagnosticsReport) -> (HostRequestRegistry, Arc<Servers>) {
    let registry = HostRequestRegistry::default();
    let servers = Arc::new(Servers {
        report,
        synced: Mutex::default(),
    });
    let documents = eukhe_docs::Documents::new(dir.join("locks"), None);
    let host = DocumentsHost {
        lsp: Arc::new(SessionLsp::new(
            Some(LspHandle::new(Arc::clone(&servers))),
            dir.to_owned(),
            HarnessCell::default(),
            documents.clone(),
        )),
        documents,
    };
    register(&registry, &Arc::new(host));
    (registry, servers)
}

fn registry(dir: &Path) -> HostRequestRegistry {
    let clean = DiagnosticsReport {
        diagnostics: Vec::new(),
        pending: Vec::new(),
    };
    registry_with(dir, clean).0
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
            "diagnostics": [],
            "diagnostics_complete": true,
            "diagnostics_error": null,
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

/// A committed write reaches the language servers, and the result (and its
/// text) carries what they said in the inline window, including that some
/// are still pending.
#[tokio::test]
async fn committed_writes_carry_the_servers_diagnostics() {
    let dir = tempfile::tempdir().unwrap();
    let file = dir.path().join("a.rs");
    std::fs::write(&file, "fn one() {}\n").unwrap();
    let error = LspDiagnostic {
        path: file.clone(),
        span: LspSpan {
            start: LspPoint { line: 1, column: 4 },
            end: LspPoint { line: 1, column: 7 },
        },
        severity: LspSeverity::Error,
        message: "boom".to_owned(),
        source: Some("fake".to_owned()),
        code: None,
        server: "fake".to_owned(),
    };
    let (registry, servers) = registry_with(
        dir.path(),
        DiagnosticsReport {
            diagnostics: vec![error.clone()],
            pending: vec!["slow".to_owned()],
        },
    );
    let tag = eukhe_docs::file_hash("fn one() {}\n");
    let edited = call(
        &registry,
        "fs.edit",
        dir.path(),
        json!({"input": format!("[a.rs#{tag}]\nPUT 1.=1:\n+fn two() {{}}")}),
    )
    .await;
    assert_eq!(
        (
            &edited["files"][0]["diagnostics"],
            &edited["files"][0]["diagnostics_complete"],
            &edited["files"][0]["diagnostics_error"],
        ),
        (&json!([error]), &json!(false), &Value::Null)
    );
    let rendered = edited["rendered"].as_str().unwrap();
    assert!(
        rendered.ends_with(
            "\nLSP diagnostics of a.rs: 1 error(s)\n\
             1:4 error [fake] boom\n\
             LSP diagnostics of a.rs are still pending; late ones arrive as a [late-diagnostics] message."
        ),
        "{rendered}"
    );
    assert_eq!(*servers.synced.lock().unwrap(), vec![file]);
}

/// A real server, when installed: the kernel's `write()` of a temp crate's
/// file reaches rust-analyzer; once it runs, a write introducing an error
/// comes back with it inline, and the fixing write comes back clean.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn rust_analyzer_diagnoses_committed_writes() {
    let installed = std::process::Command::new("rust-analyzer")
        .arg("--version")
        .output()
        .is_ok_and(|output| output.status.success());
    if !installed {
        eprintln!("skipped: rust-analyzer is not installed on PATH");
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path().canonicalize().unwrap();
    std::fs::write(
        root.join("Cargo.toml"),
        "[package]\nname = \"probe\"\nversion = \"0.1.0\"\nedition = \"2021\"\n",
    )
    .unwrap();
    std::fs::create_dir(root.join("src")).unwrap();
    let registry = HostRequestRegistry::default();
    let documents = eukhe_docs::Documents::new(root.join("target/locks"), None);
    let host = DocumentsHost {
        lsp: Arc::new(SessionLsp::new(
            None,
            root.clone(),
            HarnessCell::default(),
            documents.clone(),
        )),
        documents,
    };
    register(&registry, &Arc::new(host));
    let write = |content: &'static str| {
        call(
            &registry,
            "fs.write",
            &root,
            json!({"path": "src/main.rs", "content": content}),
        )
    };
    let clean = "fn helper() -> u8 { 1 }\n\nfn main() {\n    helper();\n}\n";
    let broken = "fn helper() -> u8 { 1 }\n\nfn main() {\n    helper(1);\n}\n";
    let reports_the_error = |reply: &Value| {
        reply["diagnostics_complete"] == json!(true)
            && reply["diagnostics"]
                .as_array()
                .unwrap()
                .iter()
                .any(|diagnostic| {
                    diagnostic["code"] == json!("E0061") && diagnostic["severity"] == json!("error")
                })
    };
    // The first write starts the server in the background, and while it
    // loads the project its diagnostics miss the inline window (they would
    // arrive as a late message); once it runs, they come back inline.
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(90);
    let mut writes = 0;
    let broken_reply = loop {
        writes += 1;
        let reply = write(broken).await;
        if reports_the_error(&reply) {
            break reply;
        }
        assert!(
            std::time::Instant::now() < deadline,
            "rust-analyzer never reported the error inline: {reply}"
        );
        write(clean).await;
        tokio::time::sleep(std::time::Duration::from_millis(500)).await;
    };
    eprintln!(
        "broken write #{writes}:\n{}",
        broken_reply["rendered"].as_str().unwrap()
    );
    let fixed = write(clean).await;
    eprintln!("fixing write:\n{}", fixed["rendered"].as_str().unwrap());
    assert_eq!(
        (&fixed["diagnostics"], &fixed["diagnostics_complete"]),
        (&json!([]), &json!(true)),
        "{fixed}"
    );
}
