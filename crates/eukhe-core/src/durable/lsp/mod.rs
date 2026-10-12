//! The session side of LSP: the `lsp.*` kernel host requests, the
//! committed-write notice every file writer calls, applying workspace
//! edits, and late diagnostics delivered as a typed harness message.
//!
//! Requests go to the session's [`LspHandle`]: the daemon worker's handle
//! asks the supervisor's shared service; a session without a daemon runs a
//! private [`LspService`] (no server starts until a request needs one).

use std::collections::HashMap;
use std::fmt::Write as _;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_durable::harness::types::{InputSubmissionDraft, WhenBusy};
use eukhe_durable::types::ConversationId;
use eukhe_lsp::{apply_text_edits, DiagnosticsLedger, LspHandle, LspService, ServerTable};
use eukhe_types::input_origin::{InputOrigin, Report};
use eukhe_types::lsp::{
    CodeActionSelector, CodeActionsReport, DiagnosticsReport, LspDiagnostic, LspError, LspLocation,
    LspNavigation, LspOp, LspRequest, LspResponse, LspScope, LspServerStatus, LspSymbol, LspTarget,
    LspWorkspaceEdit,
};
use eukhe_types::pi_ai::UserContent;
use futures::FutureExt as _;
use serde::{Deserialize, Serialize};
use serde_json::Value;

use super::deps::{HarnessCell, HostCall, HostDeps, ServiceStop};

/// Late diagnostics list at most this many entries (omp
/// `DIAGNOSTIC_MESSAGE_LIMIT`).
const LATE_DIAGNOSTIC_LIMIT: usize = 50;

/// The LSP state of one session.
pub struct SessionLsp {
    handle: LspHandle,
    /// The in-process service when the session has no daemon.
    private: Option<LspService>,
    /// Workspace root handed to the servers: the session's cwd.
    root: PathBuf,
    harness: HarnessCell,
    ledger: Mutex<DiagnosticsLedger>,
    /// Committed writes per path; a late report for an older write is stale.
    writes: Mutex<HashMap<PathBuf, u64>>,
}

/// One file a workspace edit wrote, with what the servers said about it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct WrittenFile {
    pub path: PathBuf,
    pub edits: usize,
    pub diagnostics: WriteDiagnostics,
}

/// The servers' answer to a committed write.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", content = "value", rename_all = "snake_case")]
pub enum WriteDiagnostics {
    Report(DiagnosticsReport),
    /// The file is written; the LSP authority could not be told (the
    /// [`LspError`] message).
    Failed(String),
}

/// Why a workspace edit was not applied.
#[derive(Debug, thiserror::Error)]
pub enum ApplyError {
    #[error("cannot read {path:?}: {source}")]
    Read {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },
    #[error("cannot apply the edits to {path:?}: {source}")]
    Edit {
        path: PathBuf,
        #[source]
        source: eukhe_lsp::EditError,
    },
    #[error("cannot write {path:?}: {source}")]
    Write {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },
}

impl SessionLsp {
    /// The LSP state of a session rooted at `root`: `handle` when the
    /// embedding supplies one, else a private service.
    pub(crate) fn new(handle: Option<LspHandle>, root: PathBuf, harness: HarnessCell) -> Self {
        let (handle, private) = if let Some(handle) = handle {
            (handle, None)
        } else {
            let service = LspService::new(ServerTable::builtin());
            (LspHandle::new(Arc::new(service.clone())), Some(service))
        };
        Self {
            handle,
            private,
            root,
            harness,
            ledger: Mutex::default(),
            writes: Mutex::default(),
        }
    }

    async fn call(&self, op: LspOp) -> Result<LspResponse, LspError> {
        self.handle
            .call(LspRequest {
                root: self.root.clone(),
                op,
            })
            .await
    }

    /// A file writer committed `text` to `path` (absolute): the servers
    /// get the new text and the diagnostics of the inline window come
    /// back. Servers still pending report later, as a late-diagnostics
    /// message to `conversation`, unless `path` is written again first.
    ///
    /// # Errors
    ///
    /// The LSP authority is unreachable.
    pub async fn committed_write(
        self: &Arc<Self>,
        path: &Path,
        text: &str,
        conversation: ConversationId,
    ) -> Result<DiagnosticsReport, LspError> {
        let write = {
            let mut writes = self.writes.lock().unwrap_or_else(PoisonError::into_inner);
            let count = writes.entry(path.to_owned()).or_default();
            *count += 1;
            *count
        };
        let response = self
            .call(LspOp::Sync {
                path: path.to_owned(),
                text: text.to_owned(),
            })
            .await?;
        let report = expect_diagnostics(response)?;
        self.ledger().reduce(path, report.diagnostics.clone());
        if !report.pending.is_empty() {
            let lsp = Arc::clone(self);
            let path = path.to_owned();
            tokio::spawn(async move {
                if let Err(error) = lsp.late_diagnostics(&path, write, conversation).await {
                    tracing::warn!(path = %path.display(), %error, "late LSP diagnostics failed");
                }
            });
        }
        Ok(report)
    }

    fn ledger(&self) -> std::sync::MutexGuard<'_, DiagnosticsLedger> {
        self.ledger.lock().unwrap_or_else(PoisonError::into_inner)
    }

    fn current_write(&self, path: &Path) -> u64 {
        self.writes
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .get(path)
            .copied()
            .unwrap_or_default()
    }

    async fn late_diagnostics(
        &self,
        path: &Path,
        write: u64,
        conversation: ConversationId,
    ) -> anyhow::Result<()> {
        let response = self
            .call(LspOp::AwaitDiagnostics {
                path: path.to_owned(),
            })
            .await?;
        let report = expect_diagnostics(response)?;
        if self.current_write(path) != write {
            return Ok(());
        }
        let fresh = self.ledger().reduce(path, report.diagnostics);
        if fresh.is_empty() {
            return Ok(());
        }
        let cx = BACKGROUND_CONTEXT.clone();
        let harness = self.harness.require()?;
        let Some(conversation) = harness.conversation(conversation, &cx).await? else {
            return Ok(());
        };
        let report = Report::LateDiagnostics;
        conversation
            .submit(
                InputSubmissionDraft {
                    request_id: Some(format!("late-diagnostics:{}", uuid::Uuid::new_v4())),
                    content: UserContent::Text(
                        report.render(&late_diagnostics_text(path, &fresh, &self.root)),
                    ),
                    when_busy: Some(WhenBusy::Steer),
                    origin: InputOrigin::Report { report },
                },
                &cx,
            )
            .await?;
        Ok(())
    }

    /// Write every file of `edit` atomically, then tell the servers.
    ///
    /// # Errors
    ///
    /// A file cannot be read, the edits do not apply, or a write fails;
    /// files written before the failure stay written.
    pub async fn apply(
        self: &Arc<Self>,
        edit: &LspWorkspaceEdit,
        conversation: ConversationId,
    ) -> Result<Vec<WrittenFile>, ApplyError> {
        let mut written = Vec::new();
        for file in &edit.files {
            let path = &file.path;
            let text =
                tokio::fs::read_to_string(path)
                    .await
                    .map_err(|source| ApplyError::Read {
                        path: path.clone(),
                        source,
                    })?;
            let next = apply_text_edits(&text, &file.edits).map_err(|source| ApplyError::Edit {
                path: path.clone(),
                source,
            })?;
            write_atomically(path, &next).map_err(|source| ApplyError::Write {
                path: path.clone(),
                source,
            })?;
            let diagnostics = match self.committed_write(path, &next, conversation).await {
                Ok(report) => WriteDiagnostics::Report(report),
                Err(error) => WriteDiagnostics::Failed(error.to_string()),
            };
            written.push(WrittenFile {
                path: path.clone(),
                edits: file.edits.len(),
                diagnostics,
            });
        }
        Ok(written)
    }
}

/// Register the `lsp.*` host requests, and the private service's shutdown
/// when the session runs one.
pub(crate) fn install(deps: &Arc<HostDeps>) {
    let lsp = Arc::clone(&deps.lsp);
    for request in [
        HostLspRequest::Diagnostics,
        HostLspRequest::Navigate(LspNavigation::Definition),
        HostLspRequest::Navigate(LspNavigation::TypeDefinition),
        HostLspRequest::Navigate(LspNavigation::Implementation),
        HostLspRequest::Navigate(LspNavigation::References),
        HostLspRequest::Hover,
        HostLspRequest::Symbols,
        HostLspRequest::Rename,
        HostLspRequest::CodeActions,
        HostLspRequest::Status,
    ] {
        let lsp = Arc::clone(&lsp);
        deps.host_requests.register(
            request.request_type(),
            Arc::new(move |call: HostCall| {
                let lsp = Arc::clone(&lsp);
                async move { handle(&lsp, request, call).await }.boxed()
            }),
        );
    }
    if let Some(service) = deps.lsp.private.clone() {
        deps.add_service(Box::new(move |_| {
            async move {
                let stop: ServiceStop =
                    Box::new(move || async move { service.shutdown().await }.boxed());
                Ok(Some(stop))
            }
            .boxed()
        }));
    }
}

#[derive(Clone, Copy)]
enum HostLspRequest {
    Diagnostics,
    Navigate(LspNavigation),
    Hover,
    Symbols,
    Rename,
    CodeActions,
    Status,
}

impl HostLspRequest {
    fn request_type(self) -> &'static str {
        match self {
            Self::Diagnostics => "lsp.diagnostics",
            Self::Navigate(LspNavigation::Definition) => "lsp.definition",
            Self::Navigate(LspNavigation::TypeDefinition) => "lsp.type_definition",
            Self::Navigate(LspNavigation::Implementation) => "lsp.implementation",
            Self::Navigate(LspNavigation::References) => "lsp.references",
            Self::Hover => "lsp.hover",
            Self::Symbols => "lsp.symbols",
            Self::Rename => "lsp.rename",
            Self::CodeActions => "lsp.code_actions",
            Self::Status => "lsp.status",
        }
    }
}

/// The payload fields the Python surface sends; `cwd` resolves relative
/// paths (the kernel's `os.getcwd()`). `path` `"*"` is the workspace.
#[derive(Debug, Deserialize)]
struct Payload {
    cwd: Option<PathBuf>,
    path: Option<String>,
    line: Option<u32>,
    symbol: Option<String>,
    query: Option<String>,
    new_name: Option<String>,
    apply: Option<Value>,
}

impl Payload {
    fn path(&self, request: &str, root: &Path) -> anyhow::Result<PathBuf> {
        let path = self
            .path
            .as_deref()
            .ok_or_else(|| anyhow::anyhow!("{request} requires path"))?;
        let base = self.cwd.as_deref().unwrap_or(root);
        Ok(base.join(path))
    }

    fn scope(&self, request: &str, root: &Path) -> anyhow::Result<LspScope> {
        match self.path.as_deref() {
            None | Some("*") => Ok(LspScope::Workspace),
            Some(_) => Ok(LspScope::File(self.path(request, root)?)),
        }
    }

    fn target(&self, request: &str, root: &Path) -> anyhow::Result<LspTarget> {
        let line = self
            .line
            .filter(|line| *line >= 1)
            .ok_or_else(|| anyhow::anyhow!("{request} requires a 1-based line"))?;
        let symbol = self
            .symbol
            .clone()
            .filter(|symbol| !symbol.is_empty())
            .ok_or_else(|| anyhow::anyhow!("{request} requires symbol (name or name#N)"))?;
        Ok(LspTarget {
            path: self.path(request, root)?,
            line,
            symbol,
        })
    }
}

/// The conversation a host call belongs to: its tool call's, else the root.
fn call_conversation(lsp: &SessionLsp, call: &HostCall) -> anyhow::Result<ConversationId> {
    match &call.call {
        Some(api) => Ok(api.conversation_id()),
        None => lsp
            .harness
            .root()
            .map(|root| root.id())
            .ok_or_else(|| anyhow::anyhow!("Harness is closed")),
    }
}

/// What `lsp.rename` returns.
#[derive(Serialize)]
struct RenameResult {
    edit: LspWorkspaceEdit,
    applied: Option<Vec<WrittenFile>>,
}

/// What `lsp.code_actions` returns.
#[derive(Serialize)]
struct CodeActionsResult {
    #[serde(flatten)]
    report: CodeActionsReport,
    written: Option<Vec<WrittenFile>>,
}

async fn handle(
    lsp: &Arc<SessionLsp>,
    request: HostLspRequest,
    call: HostCall,
) -> anyhow::Result<Value> {
    let name = request.request_type();
    let payload: Payload = serde_json::from_value(call.data.clone())
        .map_err(|error| anyhow::anyhow!("invalid {name} payload: {error}"))?;
    let root = lsp.root.as_path();
    let value = match request {
        HostLspRequest::Diagnostics => {
            let response = lsp
                .call(LspOp::Diagnostics {
                    scope: payload.scope(name, root)?,
                })
                .await?;
            serde_json::to_value(expect_diagnostics(response)?)?
        }
        HostLspRequest::Navigate(navigation) => {
            let response = lsp
                .call(LspOp::Navigate {
                    navigation,
                    target: payload.target(name, root)?,
                })
                .await?;
            serde_json::to_value::<Vec<LspLocation>>(match response {
                LspResponse::Locations(locations) => locations,
                other => return Err(unexpected(name, &other)),
            })?
        }
        HostLspRequest::Hover => {
            let response = lsp
                .call(LspOp::Hover {
                    target: payload.target(name, root)?,
                })
                .await?;
            serde_json::to_value::<Option<String>>(match response {
                LspResponse::Hover(text) => text,
                other => return Err(unexpected(name, &other)),
            })?
        }
        HostLspRequest::Symbols => {
            let response = lsp
                .call(LspOp::Symbols {
                    scope: payload.scope(name, root)?,
                    query: payload.query.clone(),
                })
                .await?;
            serde_json::to_value::<Vec<LspSymbol>>(match response {
                LspResponse::Symbols(symbols) => symbols,
                other => return Err(unexpected(name, &other)),
            })?
        }
        HostLspRequest::Rename => {
            let new_name = payload
                .new_name
                .clone()
                .filter(|name| !name.is_empty())
                .ok_or_else(|| anyhow::anyhow!("{name} requires new_name"))?;
            let apply = match &payload.apply {
                None | Some(Value::Bool(true)) => true,
                Some(Value::Bool(false)) => false,
                Some(other) => anyhow::bail!("{name} apply must be a bool, got {other}"),
            };
            let response = lsp
                .call(LspOp::Rename {
                    target: payload.target(name, root)?,
                    new_name,
                })
                .await?;
            let edit = match response {
                LspResponse::Edit(edit) => edit,
                other => return Err(unexpected(name, &other)),
            };
            let applied = if apply {
                Some(lsp.apply(&edit, call_conversation(lsp, &call)?).await?)
            } else {
                None
            };
            serde_json::to_value(RenameResult { edit, applied })?
        }
        HostLspRequest::CodeActions => {
            let apply = match &payload.apply {
                None | Some(Value::Null) => None,
                Some(Value::Number(index)) => Some(CodeActionSelector::Index(
                    index
                        .as_u64()
                        .and_then(|index| usize::try_from(index).ok())
                        .ok_or_else(|| {
                            anyhow::anyhow!("{name} apply index must be a non-negative integer")
                        })?,
                )),
                Some(Value::String(title)) => Some(CodeActionSelector::Title(title.clone())),
                Some(other) => {
                    anyhow::bail!("{name} apply must be an index or a title, got {other}")
                }
            };
            let response = lsp
                .call(LspOp::CodeActions {
                    target: payload.target(name, root)?,
                    apply,
                })
                .await?;
            let report = match response {
                LspResponse::CodeActions(report) => report,
                other => return Err(unexpected(name, &other)),
            };
            let written = match &report.applied {
                Some(applied) => Some(
                    lsp.apply(&applied.edit, call_conversation(lsp, &call)?)
                        .await?,
                ),
                None => None,
            };
            serde_json::to_value(CodeActionsResult { report, written })?
        }
        HostLspRequest::Status => {
            let response = lsp.call(LspOp::Status).await?;
            serde_json::to_value::<Vec<LspServerStatus>>(match response {
                LspResponse::Status(rows) => rows,
                other => return Err(unexpected(name, &other)),
            })?
        }
    };
    Ok(value)
}

fn expect_diagnostics(response: LspResponse) -> Result<DiagnosticsReport, LspError> {
    match response {
        LspResponse::Diagnostics(report) => Ok(report),
        other => Err(LspError::Unreachable {
            reason: format!("the LSP host answered a diagnostics request with {other:?}"),
        }),
    }
}

fn unexpected(request: &str, response: &LspResponse) -> anyhow::Error {
    anyhow::anyhow!("the LSP host answered {request} with {response:?}")
}

/// The body of a late-diagnostics report (omp `lsp-late-diagnostic.md`),
/// `path` relative to `root`.
pub(crate) fn late_diagnostics_text(
    path: &Path,
    diagnostics: &[LspDiagnostic],
    root: &Path,
) -> String {
    let shown = path.strip_prefix(root).unwrap_or(path).display();
    let mut text = format!(
        "{shown}\nLate LSP diagnostics arrived after the write returned: {}",
        summary(diagnostics)
    );
    for diagnostic in diagnostics.iter().take(LATE_DIAGNOSTIC_LIMIT) {
        text.push('\n');
        text.push_str(&diagnostic_line(diagnostic));
    }
    if diagnostics.len() > LATE_DIAGNOSTIC_LIMIT {
        let more = diagnostics.len() - LATE_DIAGNOSTIC_LIMIT;
        // Writing to a `String` cannot fail.
        let _ = write!(text, "\n({more} more)");
    }
    text
}

/// `LINE:COL severity [source] message (code)`.
fn diagnostic_line(diagnostic: &LspDiagnostic) -> String {
    let severity = match diagnostic.severity {
        eukhe_types::lsp::LspSeverity::Error => "error",
        eukhe_types::lsp::LspSeverity::Warning => "warning",
        eukhe_types::lsp::LspSeverity::Information => "info",
        eukhe_types::lsp::LspSeverity::Hint => "hint",
    };
    let source = diagnostic.source.as_deref().unwrap_or(&diagnostic.server);
    let code = diagnostic
        .code
        .as_deref()
        .map(|code| format!(" ({code})"))
        .unwrap_or_default();
    format!(
        "{}:{} {severity} [{source}] {}{code}",
        diagnostic.span.start.line, diagnostic.span.start.column, diagnostic.message
    )
}

/// `2 error(s), 1 warning(s)` (omp `formatDiagnosticsSummary`).
fn summary(diagnostics: &[LspDiagnostic]) -> String {
    use eukhe_types::lsp::LspSeverity;
    let parts: Vec<String> = [
        (LspSeverity::Error, "error"),
        (LspSeverity::Warning, "warning"),
        (LspSeverity::Information, "info"),
        (LspSeverity::Hint, "hint"),
    ]
    .into_iter()
    .filter_map(|(severity, label)| {
        let count = diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.severity == severity)
            .count();
        (count > 0).then(|| format!("{count} {label}(s)"))
    })
    .collect();
    parts.join(", ")
}

/// Replace `path` with `text` atomically (temp file in the same directory,
/// fsync, rename, directory fsync), keeping the file's permissions.
fn write_atomically(path: &Path, text: &str) -> std::io::Result<()> {
    let parent = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));
    let name = path
        .file_name()
        .ok_or_else(|| std::io::Error::other("the path names no file"))?
        .to_string_lossy();
    let temp = parent.join(format!(".{name}.eukhe-{}.tmp", uuid::Uuid::new_v4()));
    let written = (|| {
        let mut file = std::fs::File::create_new(&temp)?;
        file.write_all(text.as_bytes())?;
        if let Ok(metadata) = std::fs::metadata(path) {
            file.set_permissions(metadata.permissions())?;
        }
        file.sync_all()?;
        std::fs::rename(&temp, path)
    })();
    if written.is_err() {
        // The temp file is ours; the write error is the one to report.
        let _ = std::fs::remove_file(&temp);
    }
    written?;
    crate::platform::fs::sync_directory(parent)
}

#[cfg(test)]
mod tests;
