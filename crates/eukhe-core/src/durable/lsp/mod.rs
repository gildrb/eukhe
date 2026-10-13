//! The session side of LSP: the `lsp.*` kernel host requests, the
//! committed-write notice every file writer calls, applying workspace
//! edits, and late diagnostics delivered as a typed harness message.
//!
//! Requests go to the session's [`LspHandle`]: the daemon worker's handle
//! asks the supervisor's shared service; a session without a daemon runs a
//! private [`LspService`] (no server starts until a request needs one).

use std::collections::HashMap;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_docs::{Documents, WriteError};
use eukhe_durable::harness::types::{InputSubmissionDraft, WhenBusy};
use eukhe_durable::types::ConversationId;
use eukhe_lsp::{
    apply_text_edits, read_text, DiagnosticsLedger, LspHandle, LspService, ServerTable,
};
use eukhe_types::input_origin::{InputOrigin, Report};
use eukhe_types::lsp::{
    CodeActionSelector, DiagnosticsReport, LspCodeAction, LspDiagnostic, LspError, LspLocation,
    LspNavigation, LspOp, LspRequest, LspResponse, LspScope, LspServerStatus, LspSymbol, LspTarget,
    LspWorkspaceEdit,
};
use eukhe_types::pi_ai::UserContent;
use futures::FutureExt as _;
use serde::{Deserialize, Serialize};
use serde_json::Value;

use super::deps::{HarnessCell, HostCall, HostDeps, ServiceStop};

/// Diagnostics listings show at most this many entries (omp
/// `DIAGNOSTIC_MESSAGE_LIMIT`).
const DIAGNOSTIC_LIMIT: usize = 50;

/// The LSP state of one session.
pub struct SessionLsp {
    handle: LspHandle,
    /// The in-process service when the session has no daemon.
    private: Option<LspService>,
    /// Workspace root handed to the servers: the session's cwd.
    root: PathBuf,
    harness: HarnessCell,
    /// The session's documents; workspace edits write through them.
    documents: Documents,
    ledger: Mutex<DiagnosticsLedger>,
    /// Committed writes per path; a late report for an older write is stale.
    writes: Mutex<HashMap<PathBuf, u64>>,
}

/// What the language servers said about one committed write.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct WriteDiagnostics {
    /// The diagnostics that arrived in the inline window.
    pub diagnostics: Vec<LspDiagnostic>,
    /// Every server handling the file answered in the inline window; when
    /// not, the rest arrive later as a `[late-diagnostics]` message.
    pub diagnostics_complete: bool,
    /// The file is written; the LSP authority could not be told. The model
    /// gets its message.
    #[serde(serialize_with = "error_message")]
    pub diagnostics_error: Option<LspError>,
}

#[allow(clippy::ref_option)] // serde's `serialize_with` signature
fn error_message<S: serde::Serializer>(
    error: &Option<LspError>,
    serializer: S,
) -> Result<S::Ok, S::Error> {
    match error {
        Some(error) => serializer.collect_str(error),
        None => serializer.serialize_none(),
    }
}

impl From<Result<DiagnosticsReport, LspError>> for WriteDiagnostics {
    fn from(report: Result<DiagnosticsReport, LspError>) -> Self {
        match report {
            Ok(report) => Self {
                diagnostics_complete: report.pending.is_empty(),
                diagnostics: report.diagnostics,
                diagnostics_error: None,
            },
            Err(error) => Self {
                diagnostics: Vec::new(),
                diagnostics_complete: false,
                diagnostics_error: Some(error),
            },
        }
    }
}

impl WriteDiagnostics {
    /// The model text that follows the write of `display`; `None` when the
    /// servers all answered and found nothing.
    pub(crate) fn render(&self, display: &str) -> Option<String> {
        if let Some(error) = &self.diagnostics_error {
            return Some(format!("LSP diagnostics of {display} unavailable: {error}"));
        }
        let found = (!self.diagnostics.is_empty()).then(|| {
            format!(
                "LSP diagnostics of {display}: {}",
                listing(&self.diagnostics)
            )
        });
        let pending = (!self.diagnostics_complete).then(|| {
            format!(
                "LSP diagnostics of {display} are still pending; late ones arrive as a {} message.",
                Report::LateDiagnostics.header()
            )
        });
        match (found, pending) {
            (None, None) => None,
            (Some(text), None) | (None, Some(text)) => Some(text),
            (Some(found), Some(pending)) => Some(format!("{found}\n{pending}")),
        }
    }
}

/// One file a workspace edit wrote, with what the servers said about it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct WrittenFile {
    pub path: PathBuf,
    pub edits: usize,
    #[serde(flatten)]
    pub diagnostics: WriteDiagnostics,
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
    #[error("{path:?} changed after the language server computed the edit")]
    Stale { path: PathBuf },
    #[error("cannot apply the edits to {path:?}: {source}")]
    Edit {
        path: PathBuf,
        #[source]
        source: eukhe_lsp::EditError,
    },
    #[error("{path:?} is not a UTF-8 path")]
    NotUtf8 { path: PathBuf },
    #[error(transparent)]
    Write(WriteError),
    #[error("the write of {path:?} did not finish: {source}")]
    Interrupted {
        path: PathBuf,
        #[source]
        source: tokio::task::JoinError,
    },
}

impl SessionLsp {
    /// The LSP state of a session rooted at `root`: `handle` when the
    /// embedding supplies one, else a private service. Workspace edits
    /// write through `documents`.
    pub(crate) fn new(
        handle: Option<LspHandle>,
        root: PathBuf,
        harness: HarnessCell,
        documents: Documents,
    ) -> Self {
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
            documents,
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

    /// A file writer committed `path` (absolute): the servers get its text
    /// on disk and the diagnostics of the inline window come back. Servers
    /// still pending report later, as a late-diagnostics message to
    /// `conversation` (the root conversation when `None`), unless `path` is
    /// written again first.
    pub async fn committed_write(
        self: &Arc<Self>,
        path: &Path,
        conversation: Option<ConversationId>,
    ) -> WriteDiagnostics {
        let write = {
            let mut writes = self.writes.lock().unwrap_or_else(PoisonError::into_inner);
            let count = writes.entry(path.to_owned()).or_default();
            *count += 1;
            *count
        };
        let report = match read_text(path).await {
            Ok(text) => self
                .call(LspOp::Sync {
                    path: path.to_owned(),
                    text,
                })
                .await
                .and_then(expect_diagnostics),
            Err(error) => Err(error),
        };
        if let Ok(report) = &report {
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
        }
        WriteDiagnostics::from(report)
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
        conversation: Option<ConversationId>,
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
        let conversation = match conversation {
            Some(conversation) => conversation,
            None => self
                .harness
                .root()
                .map(|root| root.id())
                .ok_or_else(|| anyhow::anyhow!("Harness is closed"))?,
        };
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

    /// Write every file of `edit` through the session's documents (path
    /// lock, compare-and-swap against the text the server edited, BOM, line
    /// endings, and mode kept), then tell the servers. Every file must
    /// still hold that text before any is written.
    ///
    /// # Errors
    ///
    /// A file cannot be read or changed since the server saw it, the edits
    /// do not apply, or a write fails; files written before a failing
    /// write stay written.
    pub async fn apply(
        self: &Arc<Self>,
        edit: &LspWorkspaceEdit,
        conversation: Option<ConversationId>,
    ) -> Result<Vec<WrittenFile>, ApplyError> {
        let mut staged = Vec::with_capacity(edit.files.len());
        for file in &edit.files {
            let path = &file.path;
            let current = tokio::fs::read(path)
                .await
                .map_err(|source| ApplyError::Read {
                    path: path.clone(),
                    source,
                })?;
            if current != file.base.as_bytes() {
                return Err(ApplyError::Stale { path: path.clone() });
            }
            let next =
                apply_text_edits(&file.base, &file.edits).map_err(|source| ApplyError::Edit {
                    path: path.clone(),
                    source,
                })?;
            let target = path
                .to_str()
                .ok_or_else(|| ApplyError::NotUtf8 { path: path.clone() })?
                .to_owned();
            staged.push((file, target, next));
        }
        let mut written = Vec::with_capacity(staged.len());
        for (file, target, next) in staged {
            let documents = self.documents.clone();
            let root = self.root.clone();
            let base = file.base.clone();
            let replaced = tokio::task::spawn_blocking(move || {
                // The writer keeps the file's BOM: it takes the text after it.
                let content = next.strip_prefix('\u{feff}').unwrap_or(&next);
                documents.replace_if(&root, &target, base.as_bytes(), content)
            })
            .await
            .map_err(|source| ApplyError::Interrupted {
                path: file.path.clone(),
                source,
            })?;
            match replaced {
                Ok(_) => {}
                Err(WriteError::Changed { .. }) => {
                    return Err(ApplyError::Stale {
                        path: file.path.clone(),
                    })
                }
                Err(error @ (WriteError::IsDirectory { .. } | WriteError::Io { .. })) => {
                    return Err(ApplyError::Write(error))
                }
            }
            written.push(WrittenFile {
                path: file.path.clone(),
                edits: file.edits.len(),
                diagnostics: self.committed_write(&file.path, conversation).await,
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

/// One file of a workspace edit as the REPL sees it: its edit count and,
/// once written, what the servers said.
#[derive(Serialize)]
struct FileChange {
    path: PathBuf,
    edits: usize,
    #[serde(flatten)]
    diagnostics: Option<WriteDiagnostics>,
}

impl From<WrittenFile> for FileChange {
    fn from(written: WrittenFile) -> Self {
        Self {
            path: written.path,
            edits: written.edits,
            diagnostics: Some(written.diagnostics),
        }
    }
}

/// What `lsp.rename` returns.
#[derive(Serialize)]
struct RenameResult {
    files: Vec<FileChange>,
    applied: bool,
}

/// What `lsp.code_actions` returns.
#[derive(Serialize)]
struct CodeActionsResult {
    actions: Vec<LspCodeAction>,
    applied: Option<LspCodeAction>,
    files: Vec<FileChange>,
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
            let files = if apply {
                lsp.apply(&edit, call.conversation_id())
                    .await?
                    .into_iter()
                    .map(FileChange::from)
                    .collect()
            } else {
                edit.files
                    .iter()
                    .map(|file| FileChange {
                        path: file.path.clone(),
                        edits: file.edits.len(),
                        diagnostics: None,
                    })
                    .collect()
            };
            serde_json::to_value(RenameResult {
                files,
                applied: apply,
            })?
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
            let (applied, files) = match report.applied {
                Some(applied) => {
                    let written = lsp.apply(&applied.edit, call.conversation_id()).await?;
                    (
                        Some(applied.action),
                        written.into_iter().map(FileChange::from).collect(),
                    )
                }
                None => (None, Vec::new()),
            };
            serde_json::to_value(CodeActionsResult {
                actions: report.actions,
                applied,
                files,
            })?
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
    format!(
        "{shown}\nLate LSP diagnostics arrived after the write returned: {}",
        listing(diagnostics)
    )
}

/// The summary, then one line per diagnostic (at most
/// [`DIAGNOSTIC_LIMIT`]).
fn listing(diagnostics: &[LspDiagnostic]) -> String {
    let mut text = summary(diagnostics);
    for diagnostic in diagnostics.iter().take(DIAGNOSTIC_LIMIT) {
        text.push('\n');
        text.push_str(&diagnostic_line(diagnostic));
    }
    if diagnostics.len() > DIAGNOSTIC_LIMIT {
        let more = diagnostics.len() - DIAGNOSTIC_LIMIT;
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

#[cfg(test)]
mod tests;
