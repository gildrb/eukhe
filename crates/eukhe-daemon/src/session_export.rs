//! Session export commands: the worker-side handlers for `export_html` and
//! `export_jsonl` (the daemon-mode cases over `session.exportToHtml` /
//! `exportToJsonl`) over the main conversation ([`durable`]). The HTML file
//! is built by eukhe-core's exporter (the embedded template plus the session
//! data); the JSONL export is the history re-chained into a linear file.

use eukhe_chord::context::BACKGROUND_CONTEXT;
use serde_json::{json, Value};

use crate::protocol::{response_failure, response_success, DaemonResponse};
use crate::worker::SessionSlot;

/// The `export_*` command set over the hosted session's main conversation.
pub(crate) struct ExportCommands {
    session: SessionSlot,
}

/// Which file an export writes.
#[derive(Clone, Copy)]
enum ExportFormat {
    Html,
    Jsonl,
}

impl ExportFormat {
    fn command(self) -> &'static str {
        match self {
            ExportFormat::Html => "export_html",
            ExportFormat::Jsonl => "export_jsonl",
        }
    }
}

impl ExportCommands {
    pub(crate) fn new(session: SessionSlot) -> Self {
        ExportCommands { session }
    }

    /// `export_html`: render the session to a standalone HTML file; the
    /// response carries the written path (TS `{ path }`).
    pub(crate) async fn export_html(&self, payload: &Value) -> DaemonResponse {
        self.export(ExportFormat::Html, payload).await
    }

    /// `export_jsonl`: the main conversation's history re-chained linearly
    /// into a JSONL file; the response carries the resolved path (TS
    /// `{ path }`).
    pub(crate) async fn export_jsonl(&self, payload: &Value) -> DaemonResponse {
        self.export(ExportFormat::Jsonl, payload).await
    }

    async fn export(&self, format: ExportFormat, payload: &Value) -> DaemonResponse {
        let command = format.command();
        let Some(hosted) = self.session.get() else {
            return response_failure(None, command, "Session is still initializing", None);
        };
        let output_path = payload.get("outputPath").and_then(Value::as_str);
        let written = async {
            let main = hosted.main()?;
            let cx = &BACKGROUND_CONTEXT;
            match format {
                ExportFormat::Html => {
                    durable::export_html(hosted.deps(), &main, output_path, cx).await
                }
                ExportFormat::Jsonl => {
                    durable::export_jsonl(hosted.deps(), &main, output_path, cx).await
                }
            }
        }
        .await;
        match written {
            Ok(path) => response_success(None, command, Some(json!({ "path": path }))),
            Err(error) => response_failure(None, command, &format!("{error:#}"), None),
        }
    }
}

/// The export's custom-tool renderer (the TS `createToolHtmlRenderer`
/// seam): resolves a tool by name against the session's live registry at
/// render time. The Rust tool surface carries no render functions — the
/// built-in `ipython` has none in either product — so a resolved tool
/// reports no renderable representation and the export falls back to the
/// template's generic tool rendering, exactly like the TS renderer for a
/// tool without `renderCall`. The seam stays wired at the registry so a
/// future line-oriented renderer slots in without touching the exporter.
pub(crate) struct ExportToolRenderer<'a> {
    /// The session's live tool registry (TS `getToolDefinition` source).
    pub tools: &'a [std::sync::Arc<dyn eukhe_agent::types::AgentTool>],
}

impl eukhe_core::export_html::ToolHtmlRenderer for ExportToolRenderer<'_> {
    fn render_call(&self, _tool_call_id: &str, tool_name: &str, _args: &Value) -> Option<String> {
        // Registry lookup first (TS `getToolDefinition`): an unregistered
        // tool never renders; a registered one has no render function.
        self.tools.iter().find(|tool| tool.name() == tool_name)?;
        None
    }

    fn render_result(
        &self,
        _tool_call_id: &str,
        tool_name: &str,
        _result: &[Value],
        _details: &Value,
        _is_error: bool,
    ) -> Option<eukhe_core::export_html::RenderedToolResult> {
        self.tools.iter().find(|tool| tool.name() == tool_name)?;
        None
    }
}

pub(crate) mod durable;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::durable_test_support::{ask, cx, hosted, Fixture};

    fn written_path(response: &DaemonResponse) -> String {
        assert!(response.success, "export failed: {:?}", response.error);
        response
            .data
            .as_ref()
            .and_then(|data| data.get("path"))
            .and_then(Value::as_str)
            .expect("path in response")
            .to_string()
    }

    async fn exports_with_turn(fixture: &Fixture) -> (ExportCommands, SessionSlot) {
        let slot = SessionSlot::default();
        let session = hosted(fixture).await;
        slot.replace(std::sync::Arc::clone(&session));
        ask(fixture, &session.main().expect("main"), "hi", "hello").await;
        (ExportCommands::new(slot.clone()), slot)
    }

    async fn close(slot: &SessionSlot) {
        if let Some(session) = slot.take() {
            session.close(cx()).await.expect("close");
        }
    }

    /// The HTML export writes the given path and renders the template.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn export_html_writes_the_session_data() {
        let fixture = Fixture::new();
        let (exports, slot) = exports_with_turn(&fixture).await;
        let out = fixture.cwd.join("export.html");
        let response = exports
            .export_html(&json!({ "outputPath": out.display().to_string() }))
            .await;
        assert_eq!(written_path(&response), out.display().to_string());
        let html = std::fs::read_to_string(&out).expect("read export");
        assert!(html.contains("Session Export"));
        assert!(html.contains("--accent:"));
        close(&slot).await;
    }

    /// The JSONL export re-chains the transcript linearly under a fresh
    /// header, and resolves relative paths against the session cwd.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn export_jsonl_rechains_the_transcript() {
        let fixture = Fixture::new();
        let (exports, slot) = exports_with_turn(&fixture).await;
        let response = exports
            .export_jsonl(&json!({ "outputPath": "out/session.jsonl" }))
            .await;
        let path = written_path(&response);
        assert_eq!(
            path,
            fixture.cwd.join("out/session.jsonl").display().to_string()
        );
        let body = std::fs::read_to_string(&path).expect("read export");
        let lines: Vec<Value> = body
            .lines()
            .map(|line| serde_json::from_str(line).expect("json line"))
            .collect();
        assert_eq!(lines[0]["type"], "session");
        assert_eq!(lines[0]["cwd"], fixture.cwd.display().to_string());
        let messages: Vec<&Value> = lines[1..]
            .iter()
            .filter(|line| line["type"] == "message")
            .collect();
        assert_eq!(messages.len(), 2, "{lines:?}");
        assert_eq!(messages[0]["message"]["role"], "user");
        assert_eq!(messages[1]["message"]["role"], "assistant");
        // One linear chain: each line's parent is the line before it (the
        // digest row sits between the user message and the answer).
        for pair in lines[1..].windows(2) {
            assert_eq!(pair[1]["parentId"], pair[0]["id"], "{lines:?}");
        }
        close(&slot).await;
    }

    /// Before `create` there is nothing to export: the TS initializing error.
    #[tokio::test]
    async fn export_requires_the_session() {
        let exports = ExportCommands::new(SessionSlot::default());
        let response = exports.export_html(&json!({})).await;
        assert!(!response.success);
        assert_eq!(
            response.error.as_deref(),
            Some("Session is still initializing")
        );
    }
}
