//! The service against the fake language server (`tests/support`), plus
//! one check against a real rust-analyzer when it is installed.

use std::path::{Path, PathBuf};
use std::time::Duration;

use eukhe_lsp::{apply_text_edits, LspService, ServerTable};
use eukhe_types::lsp::{
    CodeActionSelector, DiagnosticsReport, LspDiagnostic, LspError, LspLocation, LspNavigation,
    LspOp, LspPoint, LspRequest, LspResponse, LspScope, LspServerState, LspServerStatus,
    LspSeverity, LspSpan, LspTarget,
};
use serde_json::json;

const SOURCE: &str =
    "fn helper() {}\nstruct Shape\n    fn area() {}\nfn main() { helper(); ERROR }\n";

struct Project {
    _dir: tempfile::TempDir,
    root: PathBuf,
    file: PathBuf,
    service: LspService,
}

fn project(args: &[&str]) -> Project {
    project_with_backoff(args, Duration::from_mins(3))
}

fn project_with_backoff(args: &[&str], backoff: Duration) -> Project {
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path().canonicalize().unwrap();
    std::fs::write(root.join("fake.toml"), "").unwrap();
    let file = root.join("main.fake");
    std::fs::write(&file, SOURCE).unwrap();
    let table = json!({
        "fake": {
            "command": env!("CARGO_BIN_EXE_eukhe-lsp-fake-server"),
            "args": args,
            "fileTypes": [".fake"],
            "rootMarkers": ["fake.toml"],
            "settings": { "fake": { "greeting": "hello from settings" } },
        },
        "ghost": {
            "command": "eukhe-lsp-no-such-server",
            "fileTypes": [".fake"],
            "rootMarkers": ["fake.toml"],
        },
    });
    let service =
        LspService::with_backoff(ServerTable::from_json(&table.to_string()).unwrap(), backoff);
    Project {
        _dir: dir,
        root,
        file,
        service,
    }
}

impl Project {
    async fn call(&self, op: LspOp) -> Result<LspResponse, LspError> {
        self.service
            .call(LspRequest {
                root: self.root.clone(),
                op,
            })
            .await
    }

    fn target(&self, line: u32, symbol: &str) -> LspTarget {
        LspTarget {
            path: self.file.clone(),
            line,
            symbol: symbol.to_owned(),
        }
    }

    async fn navigate(
        &self,
        navigation: LspNavigation,
        line: u32,
        symbol: &str,
    ) -> Vec<LspLocation> {
        match self
            .call(LspOp::Navigate {
                navigation,
                target: self.target(line, symbol),
            })
            .await
        {
            Ok(LspResponse::Locations(locations)) => locations,
            other => panic!("unexpected {other:?}"),
        }
    }

    async fn diagnostics(&self, op: LspOp) -> DiagnosticsReport {
        match self.call(op).await {
            Ok(LspResponse::Diagnostics(report)) => report,
            other => panic!("unexpected {other:?}"),
        }
    }

    fn status(&self) -> Vec<LspServerStatus> {
        let runtime = tokio::runtime::Handle::current();
        match tokio::task::block_in_place(|| runtime.block_on(self.call(LspOp::Status))) {
            Ok(LspResponse::Status(rows)) => rows,
            other => panic!("unexpected {other:?}"),
        }
    }
}

fn span(line: u32, start: u32, end: u32) -> LspSpan {
    LspSpan {
        start: LspPoint {
            line,
            column: start,
        },
        end: LspPoint { line, column: end },
    }
}

fn location(path: &Path, line: u32, start: u32, end: u32, text: &str) -> LspLocation {
    LspLocation {
        path: path.to_owned(),
        span: span(line, start, end),
        line_text: text.to_owned(),
    }
}

fn error_diagnostic(path: &Path, line: u32, start: u32) -> LspDiagnostic {
    LspDiagnostic {
        path: path.to_owned(),
        span: span(line, start, start + 5),
        severity: LspSeverity::Error,
        message: "ERROR is not allowed".to_owned(),
        source: Some("fake".to_owned()),
        code: Some("E1".to_owned()),
        server: "fake".to_owned(),
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn navigation_hover_and_symbols() {
    let project = project(&[]);
    let file = &project.file;
    let definition = location(file, 1, 4, 10, "fn helper() {}");
    for navigation in [
        LspNavigation::Definition,
        LspNavigation::TypeDefinition,
        LspNavigation::Implementation,
    ] {
        assert_eq!(
            project.navigate(navigation, 4, "helper").await,
            vec![definition.clone()]
        );
    }
    assert_eq!(
        project
            .navigate(LspNavigation::References, 4, "helper")
            .await,
        vec![
            definition,
            location(file, 4, 13, 19, "fn main() { helper(); ERROR }")
        ]
    );
    let hover = project
        .call(LspOp::Hover {
            target: project.target(1, "helper"),
        })
        .await;
    assert_eq!(
        hover,
        Ok(LspResponse::Hover(Some(
            "```fake\nfn helper\n```\n\"hello from settings\"".to_owned()
        )))
    );
    let LspResponse::Symbols(symbols) = project
        .call(LspOp::Symbols {
            scope: LspScope::File(file.clone()),
            query: None,
        })
        .await
        .unwrap()
    else {
        panic!("symbols");
    };
    let named: Vec<_> = symbols
        .iter()
        .map(|symbol| {
            (
                symbol.name.as_str(),
                symbol.kind.as_str(),
                symbol.container.as_deref(),
            )
        })
        .collect();
    assert_eq!(
        named,
        vec![
            ("helper", "function", None),
            ("Shape", "struct", None),
            ("area", "method", Some("Shape")),
            ("main", "function", None),
        ]
    );
    let LspResponse::Symbols(symbols) = project
        .call(LspOp::Symbols {
            scope: LspScope::Workspace,
            query: Some("hel".to_owned()),
        })
        .await
        .unwrap()
    else {
        panic!("workspace symbols");
    };
    assert_eq!(
        symbols
            .into_iter()
            .map(|symbol| symbol.location)
            .collect::<Vec<_>>(),
        vec![location(file, 1, 4, 10, "fn helper() {}")]
    );
    assert_eq!(
        project.status(),
        vec![
            LspServerStatus {
                name: "fake".to_owned(),
                state: LspServerState::Ready,
                file_types: vec![".fake".to_owned()],
                detail: None,
            },
            LspServerStatus {
                name: "ghost".to_owned(),
                state: LspServerState::Missing,
                file_types: vec![".fake".to_owned()],
                detail: Some("eukhe-lsp-no-such-server is not installed (looked in node_modules/.bin and PATH)".to_owned()),
            },
        ]
    );
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn position_and_routing_errors_are_typed() {
    let project = project(&[]);
    let notes = project.root.join("notes.txt");
    std::fs::write(&notes, "text").unwrap();
    assert_eq!(
        project
            .call(LspOp::Hover {
                target: LspTarget {
                    path: notes.clone(),
                    line: 1,
                    symbol: "text".to_owned(),
                },
            })
            .await,
        Err(LspError::NoServer {
            root: project.root.clone(),
            path: notes,
        })
    );
    assert_eq!(
        project
            .call(LspOp::Hover {
                target: project.target(1, "absent")
            })
            .await,
        Err(LspError::SymbolNotFound {
            symbol: "absent".to_owned(),
            line: 1,
        })
    );
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn writes_sync_and_report_inline_then_late_diagnostics() {
    let project = project(&[]);
    let file = project.file.clone();
    assert_eq!(project.status()[0].state, LspServerState::Available);
    // The server is not running: the write starts it in the background.
    let first = project
        .diagnostics(LspOp::Sync {
            path: file.clone(),
            text: SOURCE.to_owned(),
        })
        .await;
    assert_eq!(first.pending, vec!["fake".to_owned()]);
    let late = project
        .diagnostics(LspOp::AwaitDiagnostics { path: file.clone() })
        .await;
    assert_eq!(
        late,
        DiagnosticsReport {
            diagnostics: vec![error_diagnostic(&file, 4, 23)],
            pending: Vec::new(),
        }
    );
    let fixed = SOURCE.replace("ERROR", "OK");
    std::fs::write(&file, &fixed).unwrap();
    let inline = project
        .diagnostics(LspOp::Sync {
            path: file.clone(),
            text: fixed,
        })
        .await;
    assert_eq!(
        inline,
        DiagnosticsReport {
            diagnostics: Vec::new(),
            pending: Vec::new(),
        }
    );
    // An edit outside eukhe reaches the server on the next request.
    std::fs::write(&file, "fn x() { WARN }\n").unwrap();
    let explicit = project
        .diagnostics(LspOp::Diagnostics {
            scope: LspScope::File(file.clone()),
        })
        .await;
    assert_eq!(
        explicit
            .diagnostics
            .iter()
            .map(|diagnostic| diagnostic.severity)
            .collect::<Vec<_>>(),
        vec![LspSeverity::Warning]
    );
    let workspace = project
        .diagnostics(LspOp::Diagnostics {
            scope: LspScope::Workspace,
        })
        .await;
    assert_eq!(workspace.diagnostics, explicit.diagnostics);
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn slow_servers_deliver_after_the_inline_window() {
    let project = project(&["--delay-ms", "1500"]);
    let file = project.file.clone();
    project
        .diagnostics(LspOp::AwaitDiagnostics { path: file.clone() })
        .await;
    let edited = SOURCE.replace("helper(); ERROR", "ERROR; helper();");
    let inline = project
        .diagnostics(LspOp::Sync {
            path: file.clone(),
            text: edited.clone(),
        })
        .await;
    assert_eq!(inline.pending, vec!["fake".to_owned()]);
    std::fs::write(&file, &edited).unwrap();
    let late = project
        .diagnostics(LspOp::AwaitDiagnostics { path: file.clone() })
        .await;
    assert_eq!(late.diagnostics, vec![error_diagnostic(&file, 4, 13)]);
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn pull_servers_are_asked() {
    let project = project(&["--pull"]);
    let report = project
        .diagnostics(LspOp::Diagnostics {
            scope: LspScope::File(project.file.clone()),
        })
        .await;
    assert_eq!(
        report,
        DiagnosticsReport {
            diagnostics: vec![error_diagnostic(&project.file, 4, 23)],
            pending: Vec::new(),
        }
    );
}

/// A server that answers pulls and also publishes after a save
/// (rust-analyzer: its own diagnostics by pull, `cargo check`'s by publish)
/// reports both for a committed write.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn dual_mode_servers_report_pulled_and_published_diagnostics() {
    let project = project(&["--pull", "--check-on-save"]);
    let file = project.file.clone();
    let opened = project
        .diagnostics(LspOp::Diagnostics {
            scope: LspScope::File(file.clone()),
        })
        .await;
    assert_eq!(
        opened,
        DiagnosticsReport {
            diagnostics: vec![error_diagnostic(&file, 4, 23)],
            pending: Vec::new(),
        }
    );
    let edited = SOURCE.replace("ERROR", "ERROR WARN");
    std::fs::write(&file, &edited).unwrap();
    let written = project
        .diagnostics(LspOp::Sync {
            path: file.clone(),
            text: edited,
        })
        .await;
    assert!(written.pending.is_empty(), "{written:?}");
    assert_eq!(
        written
            .diagnostics
            .iter()
            .map(|diagnostic| (diagnostic.severity, diagnostic.span.start))
            .collect::<Vec<_>>(),
        vec![
            (
                LspSeverity::Error,
                LspPoint {
                    line: 4,
                    column: 23
                }
            ),
            (
                LspSeverity::Warning,
                LspPoint {
                    line: 4,
                    column: 29
                }
            ),
        ]
    );
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn rename_and_code_actions_return_edits() {
    let project = project(&[]);
    let LspResponse::Edit(edit) = project
        .call(LspOp::Rename {
            target: project.target(1, "helper"),
            new_name: "assist".to_owned(),
        })
        .await
        .unwrap()
    else {
        panic!("rename");
    };
    assert_eq!(edit.files.len(), 1);
    assert_eq!(edit.files[0].base, SOURCE);
    assert_eq!(
        apply_text_edits(SOURCE, &edit.files[0].edits),
        Ok(SOURCE.replace("helper", "assist"))
    );

    let actions = |apply| LspOp::CodeActions {
        target: project.target(4, "ERROR"),
        apply,
    };
    let LspResponse::CodeActions(listed) = project.call(actions(None)).await.unwrap() else {
        panic!("code actions");
    };
    assert_eq!(
        listed
            .actions
            .iter()
            .map(|action| action.title.as_str())
            .collect::<Vec<_>>(),
        vec!["Replace ERROR with OK", "Uppercase line", "Append marker"]
    );
    assert!(listed.applied.is_none());
    for (selector, expected) in [
        (CodeActionSelector::Index(0), SOURCE.replace("ERROR", "OK")),
        (
            CodeActionSelector::Title("uppercase".to_owned()),
            SOURCE.replace(
                "fn main() { helper(); ERROR }",
                "FN MAIN() { HELPER(); ERROR }",
            ),
        ),
        (
            CodeActionSelector::Title("marker".to_owned()),
            SOURCE.replace("ERROR }", "ERROR } // marker"),
        ),
    ] {
        let LspResponse::CodeActions(report) = project.call(actions(Some(selector))).await.unwrap()
        else {
            panic!("apply");
        };
        let applied = report.applied.expect("applied action");
        assert_eq!(applied.edit.files.len(), 1);
        assert_eq!(
            apply_text_edits(SOURCE, &applied.edit.files[0].edits),
            Ok(expected)
        );
    }
    assert_eq!(
        project
            .call(actions(Some(CodeActionSelector::Index(9))))
            .await,
        Err(LspError::NoCodeAction {
            selector: CodeActionSelector::Index(9),
        })
    );
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn crashing_servers_back_off() {
    let project = project(&["--crash"]);
    let hover = || {
        project.call(LspOp::Hover {
            target: project.target(1, "helper"),
        })
    };
    assert!(matches!(
        hover().await,
        Err(LspError::ServerUnavailable { server, .. }) if server == "fake"
    ));
    assert!(matches!(
        hover().await,
        Err(LspError::Backoff { server, .. }) if server == "fake"
    ));
    assert_eq!(project.status()[0].state, LspServerState::Failed);

    let project = project_with_backoff(&["--crash"], Duration::ZERO);
    for _ in 0..2 {
        assert!(matches!(
            project
                .call(LspOp::Hover {
                    target: project.target(1, "helper")
                })
                .await,
            Err(LspError::ServerUnavailable { .. })
        ));
    }
}

/// A real server, when installed: rust-analyzer finds a definition in a
/// fresh crate, then reports an error a committed write introduced (inline
/// or in the late window) and clears it when the next write fixes it. The
/// error is one rust-analyzer finds itself: the server table turns
/// `cargo check` on save off, as omp does.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn rust_analyzer_navigates_and_diagnoses_writes() {
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
    let main = root.join("src/main.rs");
    let clean = "fn helper() -> u8 { 1 }\n\nfn main() {\n    helper();\n}\n";
    std::fs::write(&main, clean).unwrap();
    let service = LspService::new(ServerTable::builtin());
    let call = |op| {
        service.call(LspRequest {
            root: root.clone(),
            op,
        })
    };
    let definition = call(LspOp::Navigate {
        navigation: LspNavigation::Definition,
        target: LspTarget {
            path: main.clone(),
            line: 4,
            symbol: "helper".to_owned(),
        },
    })
    .await;
    eprintln!("definition: {definition:?}");

    // A committed write: the inline window, then the late window when the
    // server had not answered yet (what a session's late message waits on).
    let broken = "fn helper() -> u8 { 1 }\n\nfn main() {\n    helper(1);\n}\n";
    std::fs::write(&main, broken).unwrap();
    let written = |text: &str| LspOp::Sync {
        path: main.clone(),
        text: text.to_owned(),
    };
    let late = || LspOp::AwaitDiagnostics { path: main.clone() };
    let inline = call(written(broken)).await;
    eprintln!("inline after the broken write: {inline:?}");
    let mut report = match inline {
        Ok(LspResponse::Diagnostics(report)) => report,
        other => panic!("unexpected {other:?}"),
    };
    if !report.pending.is_empty() {
        report = match call(late()).await {
            Ok(LspResponse::Diagnostics(report)) => report,
            other => panic!("unexpected {other:?}"),
        };
        eprintln!("late after the broken write: {report:?}");
    }

    std::fs::write(&main, clean).unwrap();
    let fixed = call(written(clean)).await;
    eprintln!("inline after the fixing write: {fixed:?}");
    let mut fixed = match fixed {
        Ok(LspResponse::Diagnostics(report)) => report,
        other => panic!("unexpected {other:?}"),
    };
    if !fixed.pending.is_empty() {
        fixed = match call(late()).await {
            Ok(LspResponse::Diagnostics(report)) => report,
            other => panic!("unexpected {other:?}"),
        };
        eprintln!("late after the fixing write: {fixed:?}");
    }
    service.shutdown().await;

    assert_eq!(
        definition,
        Ok(LspResponse::Locations(vec![location(
            &main,
            1,
            4,
            10,
            "fn helper() -> u8 { 1 }"
        )]))
    );
    assert!(
        report.pending.is_empty(),
        "rust-analyzer never answered: {report:?}"
    );
    assert!(
        report
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.span.start.line == 4
                && diagnostic.severity == LspSeverity::Error
                && diagnostic.code.as_deref() == Some("E0061")),
        "no error for the extra argument: {report:?}"
    );
    assert!(
        fixed.pending.is_empty() && fixed.diagnostics.is_empty(),
        "the fixing write left diagnostics: {fixed:?}"
    );
}
