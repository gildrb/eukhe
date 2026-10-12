use std::sync::Mutex;

use eukhe_durable::types::ROOT_CONVERSATION_ID;
use eukhe_lsp::LspHost;
use eukhe_types::lsp::{LspFileEdit, LspPoint, LspSeverity, LspSpan, LspTextEdit};
use serde_json::json;

use super::*;

/// Answers every request from a script and records what it was asked.
struct ScriptedHost {
    requests: Mutex<Vec<LspRequest>>,
    edit: LspWorkspaceEdit,
}

impl LspHost for ScriptedHost {
    fn call(
        &self,
        request: LspRequest,
    ) -> impl std::future::Future<Output = Result<LspResponse, LspError>> + Send {
        let response = match &request.op {
            LspOp::Navigate { .. } => LspResponse::Locations(Vec::new()),
            LspOp::Rename { .. } => LspResponse::Edit(self.edit.clone()),
            LspOp::Sync { .. } => LspResponse::Diagnostics(DiagnosticsReport {
                diagnostics: Vec::new(),
                pending: Vec::new(),
            }),
            other => panic!("unscripted {other:?}"),
        };
        self.requests.lock().unwrap().push(request);
        std::future::ready(Ok(response))
    }
}

fn point(line: u32, column: u32) -> LspPoint {
    LspPoint { line, column }
}

fn session(root: &Path, edit: LspWorkspaceEdit) -> (Arc<ScriptedHost>, Arc<SessionLsp>) {
    let host = Arc::new(ScriptedHost {
        requests: Mutex::default(),
        edit,
    });
    let lsp = Arc::new(SessionLsp::new(
        Some(LspHandle::new(Arc::clone(&host))),
        root.to_owned(),
        HarnessCell::default(),
    ));
    (host, lsp)
}

fn host_call(data: Value) -> HostCall {
    HostCall {
        data,
        cell_source_code: None,
        call: None,
    }
}

#[tokio::test]
async fn host_requests_resolve_paths_against_the_kernel_cwd() {
    let dir = tempfile::tempdir().unwrap();
    let (host, lsp) = session(dir.path(), LspWorkspaceEdit::default());
    let request = host_call(json!({
        "type": "lsp.references",
        "cwd": dir.path().join("src"),
        "path": "main.rs",
        "line": 3,
        "symbol": "run#2",
    }));
    let answer = handle(
        &lsp,
        HostLspRequest::Navigate(LspNavigation::References),
        request,
    )
    .await
    .unwrap();
    assert_eq!(answer, json!([]));
    assert_eq!(
        *host.requests.lock().unwrap(),
        vec![LspRequest {
            root: dir.path().to_owned(),
            op: LspOp::Navigate {
                navigation: LspNavigation::References,
                target: LspTarget {
                    path: dir.path().join("src/main.rs"),
                    line: 3,
                    symbol: "run#2".to_owned(),
                },
            },
        }]
    );
    let missing_line = handle(
        &lsp,
        HostLspRequest::Hover,
        host_call(json!({ "path": "main.rs", "symbol": "run" })),
    )
    .await;
    assert_eq!(
        missing_line.unwrap_err().to_string(),
        "lsp.hover requires a 1-based line"
    );
}

#[tokio::test]
async fn applied_edits_are_written_and_synced() {
    let dir = tempfile::tempdir().unwrap();
    let file = dir.path().join("lib.rs");
    std::fs::write(&file, "fn old() {}\nfn main() { old(); }\n").unwrap();
    let edit = LspWorkspaceEdit {
        files: vec![LspFileEdit {
            path: file.clone(),
            edits: vec![
                LspTextEdit {
                    span: LspSpan {
                        start: point(1, 4),
                        end: point(1, 7),
                    },
                    new_text: "new".to_owned(),
                },
                LspTextEdit {
                    span: LspSpan {
                        start: point(2, 13),
                        end: point(2, 16),
                    },
                    new_text: "new".to_owned(),
                },
            ],
        }],
    };
    let (host, lsp) = session(dir.path(), edit.clone());
    let written = lsp.apply(&edit, ROOT_CONVERSATION_ID).await.unwrap();
    let text = "fn new() {}\nfn main() { new(); }\n";
    assert_eq!(std::fs::read_to_string(&file).unwrap(), text);
    assert_eq!(
        written,
        vec![WrittenFile {
            path: file.clone(),
            edits: 2,
            diagnostics: WriteDiagnostics::Report(DiagnosticsReport {
                diagnostics: Vec::new(),
                pending: Vec::new(),
            }),
        }]
    );
    assert_eq!(
        *host.requests.lock().unwrap(),
        vec![LspRequest {
            root: dir.path().to_owned(),
            op: LspOp::Sync {
                path: file,
                text: text.to_owned(),
            },
        }]
    );
}

#[cfg(unix)]
#[test]
fn atomic_writes_keep_permissions_and_leave_no_temp_file() {
    use std::os::unix::fs::PermissionsExt as _;
    let dir = tempfile::tempdir().unwrap();
    let file = dir.path().join("run.sh");
    std::fs::write(&file, "old").unwrap();
    std::fs::set_permissions(&file, std::fs::Permissions::from_mode(0o750)).unwrap();
    write_atomically(&file, "new").unwrap();
    assert_eq!(std::fs::read_to_string(&file).unwrap(), "new");
    assert_eq!(
        std::fs::metadata(&file).unwrap().permissions().mode() & 0o777,
        0o750
    );
    assert_eq!(std::fs::read_dir(dir.path()).unwrap().count(), 1);
}

#[test]
fn late_diagnostics_render_relative_to_the_root() {
    let diagnostic = |line, severity, code: Option<&str>| LspDiagnostic {
        path: PathBuf::from("/work/src/a.rs"),
        span: LspSpan {
            start: point(line, 9),
            end: point(line, 12),
        },
        severity,
        message: "cannot find function `new`".to_owned(),
        source: Some("rustc".to_owned()),
        code: code.map(str::to_owned),
        server: "rust-analyzer".to_owned(),
    };
    let diagnostics = [
        diagnostic(41, LspSeverity::Error, Some("E0425")),
        diagnostic(42, LspSeverity::Warning, None),
    ];
    assert_eq!(
        Report::LateDiagnostics.render(&late_diagnostics_text(
            Path::new("/work/src/a.rs"),
            &diagnostics,
            Path::new("/work")
        )),
        "[late-diagnostics]\n\n\
         src/a.rs\n\
         Late LSP diagnostics arrived after the write returned: 1 error(s), 1 warning(s)\n\
         41:9 error [rustc] cannot find function `new` (E0425)\n\
         42:9 warning [rustc] cannot find function `new`"
    );
}
