//! LSP wire vocabulary: what a session asks the language servers of its
//! project and what comes back. Positions the model names are 1-based
//! lines plus a symbol on that line (`name`, or `name#N` for the Nth
//! match); positions that come back are 1-based lines and 1-based columns
//! counted in Unicode scalar values.

use std::path::PathBuf;

use serde::{Deserialize, Serialize};

/// One LSP request of a session: the project root whose language servers
/// answer it, and the operation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LspRequest {
    /// Workspace root handed to the servers (the session's working
    /// directory); servers are admitted when their root markers match it.
    pub root: PathBuf,
    pub op: LspOp,
}

/// A position the model names: an absolute file path, a 1-based line, and
/// a symbol on that line (`name` or `name#N`, N 1-based).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LspTarget {
    pub path: PathBuf,
    pub line: u32,
    pub symbol: String,
}

/// The files a diagnostics or symbols request covers.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum LspScope {
    /// One absolute file path.
    File(PathBuf),
    /// Every file the root's running servers know.
    Workspace,
}

/// The location lookups of [`LspOp::Navigate`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum LspNavigation {
    Definition,
    TypeDefinition,
    Implementation,
    References,
}

/// Which listed code action to apply.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum CodeActionSelector {
    /// The action's `index` in the listing.
    Index(usize),
    /// The first action whose title contains this text (case-insensitive).
    Title(String),
}

/// One LSP operation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum LspOp {
    /// Current diagnostics; a file is synchronized from disk first.
    Diagnostics {
        scope: LspScope,
    },
    Navigate {
        navigation: LspNavigation,
        target: LspTarget,
    },
    Hover {
        target: LspTarget,
    },
    /// Document symbols of a file, or workspace symbols matching `query`.
    Symbols {
        scope: LspScope,
        query: Option<String>,
    },
    /// The edit a rename produces; applying it is the caller's.
    #[serde(rename_all = "camelCase")]
    Rename {
        target: LspTarget,
        new_name: String,
    },
    /// The code actions at a position; with `apply`, the selected one's edit
    /// is returned (its command, when it has one, runs on the server).
    CodeActions {
        target: LspTarget,
        apply: Option<CodeActionSelector>,
    },
    Status,
    /// A committed write of `text` to `path`: the servers receive the new
    /// text and the diagnostics that arrive within the inline window come
    /// back.
    Sync {
        path: PathBuf,
        text: String,
    },
    /// Wait (the late window) for fresh diagnostics of `path` after a
    /// [`LspOp::Sync`] that returned pending servers.
    AwaitDiagnostics {
        path: PathBuf,
    },
}

/// The answer to one [`LspOp`].
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind", content = "value", rename_all = "snake_case")]
pub enum LspResponse {
    /// [`LspOp::Diagnostics`], [`LspOp::Sync`], [`LspOp::AwaitDiagnostics`].
    Diagnostics(DiagnosticsReport),
    /// [`LspOp::Navigate`].
    Locations(Vec<LspLocation>),
    /// [`LspOp::Hover`]; `None` when the server has nothing to show.
    Hover(Option<String>),
    /// [`LspOp::Symbols`].
    Symbols(Vec<LspSymbol>),
    /// [`LspOp::Rename`].
    Edit(LspWorkspaceEdit),
    /// [`LspOp::CodeActions`].
    CodeActions(CodeActionsReport),
    /// [`LspOp::Status`].
    Status(Vec<LspServerStatus>),
}

/// A 1-based line and a 1-based column in Unicode scalar values.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct LspPoint {
    pub line: u32,
    pub column: u32,
}

/// A half-open span between two points.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct LspSpan {
    pub start: LspPoint,
    pub end: LspPoint,
}

/// A location in a file, with the text of the line it starts on.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LspLocation {
    pub path: PathBuf,
    pub span: LspSpan,
    pub line_text: String,
}

/// LSP `DiagnosticSeverity`; a diagnostic without one is an error.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum LspSeverity {
    Error,
    Warning,
    Information,
    Hint,
}

/// One diagnostic of one server.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LspDiagnostic {
    pub path: PathBuf,
    pub span: LspSpan,
    pub severity: LspSeverity,
    pub message: String,
    pub source: Option<String>,
    pub code: Option<String>,
    /// The server that reported it.
    pub server: String,
}

/// Diagnostics, and the servers whose fresh diagnostics had not arrived
/// when the wait ended (empty: complete).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct DiagnosticsReport {
    pub diagnostics: Vec<LspDiagnostic>,
    pub pending: Vec<String>,
}

/// One symbol: a document symbol (with its container's name) or a
/// workspace symbol.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LspSymbol {
    pub name: String,
    /// LSP `SymbolKind` name in `snake_case` (`function`, `struct`, ...).
    pub kind: String,
    pub container: Option<String>,
    pub location: LspLocation,
}

/// One text replacement; `span` addresses the file's text as the server
/// saw it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LspTextEdit {
    pub span: LspSpan,
    pub new_text: String,
}

/// The edits of one file, in server order, and the text they address: the
/// edit applies only while the file still holds `base`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LspFileEdit {
    pub path: PathBuf,
    pub edits: Vec<LspTextEdit>,
    pub base: String,
}

/// A workspace edit: text edits grouped by file, files in server order.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct LspWorkspaceEdit {
    pub files: Vec<LspFileEdit>,
}

/// One listed code action.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LspCodeAction {
    pub index: usize,
    pub title: String,
    pub kind: Option<String>,
    pub preferred: bool,
    pub server: String,
}

/// The code actions at a position and, when one was selected, what applying
/// it takes.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CodeActionsReport {
    pub actions: Vec<LspCodeAction>,
    pub applied: Option<AppliedCodeAction>,
}

/// The selected code action: its edit (its own plus every edit its command
/// asked the client to apply) for the caller to write.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AppliedCodeAction {
    pub action: LspCodeAction,
    pub edit: LspWorkspaceEdit,
}

/// Lifecycle stage of one server declaration for a root.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum LspServerState {
    /// Root markers match but the executable is not on PATH or in the
    /// project's `node_modules/.bin`.
    Missing,
    /// Runnable; not started (servers start on first use).
    Available,
    /// Spawn and initialize are in flight.
    Starting,
    Ready,
    /// Startup failed or the server exited; retried after the crash
    /// backoff.
    Failed,
}

/// One status row.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LspServerStatus {
    pub name: String,
    pub state: LspServerState,
    pub file_types: Vec<String>,
    /// Failure or missing-binary detail.
    pub detail: Option<String>,
}

/// Why an LSP request failed.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, thiserror::Error)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum LspError {
    #[error("no language server handles {path:?} in {root:?}")]
    NoServer { root: PathBuf, path: PathBuf },
    #[error("file not found: {path:?}")]
    FileNotFound { path: PathBuf },
    #[error("cannot read {path:?}: {reason}")]
    Read { path: PathBuf, reason: String },
    #[error("line {line} is out of range in {path:?} ({lines} lines)")]
    LineOutOfRange {
        path: PathBuf,
        line: u32,
        lines: usize,
    },
    #[error("symbol {symbol:?} not found on line {line}")]
    SymbolNotFound { symbol: String, line: u32 },
    #[error(
        "symbol {symbol:?} occurrence {occurrence} is out of bounds on line {line} (found {found})"
    )]
    OccurrenceOutOfRange {
        symbol: String,
        line: u32,
        occurrence: usize,
        found: usize,
    },
    #[error("language server {server} is unavailable: {reason}")]
    ServerUnavailable { server: String, reason: String },
    #[error("language server {server} is in crash backoff for {retry_after_ms} ms: {reason}")]
    Backoff {
        server: String,
        retry_after_ms: u64,
        reason: String,
    },
    #[error("language server {server} does not support {method}")]
    NotSupported { server: String, method: String },
    #[error("{method} failed on {server}: {message} (code {code})")]
    Request {
        server: String,
        method: String,
        code: i64,
        message: String,
    },
    #[error("{method} on {server} timed out after {timeout_ms} ms")]
    Timeout {
        server: String,
        method: String,
        timeout_ms: u64,
    },
    #[error("{server} answered {method} with an invalid result: {reason}")]
    InvalidResult {
        server: String,
        method: String,
        reason: String,
    },
    #[error("no code action matches {selector:?}")]
    NoCodeAction { selector: CodeActionSelector },
    #[error("the LSP host is unreachable: {reason}")]
    Unreachable { reason: String },
}
