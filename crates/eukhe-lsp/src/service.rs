//! The LSP service: per-root rosters, the pool of started servers, and
//! the operations sessions ask for. One service serves every session of a
//! process (the daemon supervisor's, or a headless session's private one);
//! servers start lazily on first use and never at construction.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Duration;

use parking_lot::Mutex;
use serde_json::{json, Value};
use url::Url;

use eukhe_types::lsp::{
    AppliedCodeAction, CodeActionSelector, CodeActionsReport, DiagnosticsReport, LspCodeAction,
    LspDiagnostic, LspError, LspFileEdit, LspLocation, LspNavigation, LspOp, LspRequest,
    LspResponse, LspScope, LspServerState, LspServerStatus, LspSymbol, LspTarget, LspTextEdit,
    LspWorkspaceEdit,
};

use crate::client::{file_uri, LspClient};
use crate::pool::{Pool, PoolKey, Refused, SlotState, CRASH_BACKOFF};
use crate::position::{self, PositionEncoding};
use crate::protocol::{
    symbol_kind_name, CodeAction, CodeActionEntry, DocumentSymbol, DocumentSymbolResponse, Hover,
    Location, LocationResponse, SymbolInformation, WorkspaceEdit,
};
use crate::servers::{RosterEntry, ServerTable};

/// How long a committed write waits inline for fresh diagnostics (omp
/// `INLINE_DIAGNOSTICS_WAIT_TIMEOUT_MS`).
pub const INLINE_DIAGNOSTICS_WAIT: Duration = Duration::from_millis(500);
/// How long late diagnostics are awaited after the inline window (omp
/// `DEFERRED_DIAGNOSTICS_WAIT_TIMEOUT_MS`).
pub const LATE_DIAGNOSTICS_WAIT: Duration = Duration::from_secs(12);
/// How long an explicit diagnostics request waits (omp
/// `SINGLE_DIAGNOSTICS_WAIT_TIMEOUT_MS`).
const DIAGNOSTICS_WAIT: Duration = Duration::from_secs(3);
/// Workspace symbol cap (omp `WORKSPACE_SYMBOL_LIMIT`).
const WORKSPACE_SYMBOL_LIMIT: usize = 200;

struct Inner {
    table: ServerTable,
    pool: Pool<LspClient>,
    rosters: Mutex<HashMap<PathBuf, Arc<[RosterEntry]>>>,
}

/// The LSP service. Cheap to clone; clones share servers.
#[derive(Clone)]
pub struct LspService {
    inner: Arc<Inner>,
}

/// One code action as listed, with what applying it needs.
struct Listed {
    client: Arc<LspClient>,
    raw: Value,
    entry: CodeActionEntry,
    info: LspCodeAction,
}

impl LspService {
    /// A service over `table`; no server starts until a request needs it.
    #[must_use]
    pub fn new(table: ServerTable) -> Self {
        Self::with_backoff(table, CRASH_BACKOFF)
    }

    /// [`Self::new`] with an explicit crash backoff.
    #[must_use]
    pub fn with_backoff(table: ServerTable, backoff: Duration) -> Self {
        Self {
            inner: Arc::new(Inner {
                table,
                pool: Pool::new(backoff),
                rosters: Mutex::default(),
            }),
        }
    }

    /// Answer one request.
    ///
    /// # Errors
    ///
    /// The typed failure of the operation.
    #[tracing::instrument(level = "debug", skip_all, fields(root = %request.root.display()))]
    pub async fn call(&self, request: LspRequest) -> Result<LspResponse, LspError> {
        let LspRequest { root, op } = request;
        match op {
            LspOp::Diagnostics { scope } => self
                .diagnostics(&root, scope)
                .await
                .map(LspResponse::Diagnostics),
            LspOp::Navigate { navigation, target } => self
                .navigate(&root, navigation, &target)
                .await
                .map(LspResponse::Locations),
            LspOp::Hover { target } => self.hover(&root, &target).await.map(LspResponse::Hover),
            LspOp::Symbols { scope, query } => self
                .symbols(&root, scope, query.as_deref())
                .await
                .map(LspResponse::Symbols),
            LspOp::Rename { target, new_name } => self
                .rename(&root, &target, &new_name)
                .await
                .map(LspResponse::Edit),
            LspOp::CodeActions { target, apply } => self
                .code_actions(&root, &target, apply.as_ref())
                .await
                .map(LspResponse::CodeActions),
            LspOp::Status => Ok(LspResponse::Status(self.status(&root))),
            LspOp::Sync { path, text } => Ok(LspResponse::Diagnostics(
                self.sync(&root, &path, &text).await,
            )),
            LspOp::AwaitDiagnostics { path } => Ok(LspResponse::Diagnostics(
                self.await_diagnostics(&root, &path).await,
            )),
        }
    }

    /// Shut every started server down.
    pub async fn shutdown(&self) {
        for client in self.inner.pool.drain() {
            client.shutdown().await;
        }
    }

    fn roster(&self, root: &Path) -> Arc<[RosterEntry]> {
        let mut rosters = self.inner.rosters.lock();
        Arc::clone(
            rosters
                .entry(root.to_owned())
                .or_insert_with(|| self.inner.table.roster(root).into()),
        )
    }

    /// The roster entries handling `path`.
    fn handlers(&self, root: &Path, path: &Path) -> Vec<RosterEntry> {
        self.roster(root)
            .iter()
            .filter(|entry| entry.handles(path))
            .cloned()
            .collect()
    }

    fn key(entry: &RosterEntry, root: &Path) -> Option<PoolKey> {
        let launch = entry.launch(root).ok()?;
        Some(PoolKey {
            server: entry.name.clone(),
            root: root.to_owned(),
            fingerprint: entry.fingerprint(&launch),
        })
    }

    /// The started client of `entry`, starting it when needed.
    async fn client(&self, root: &Path, entry: &RosterEntry) -> Result<Arc<LspClient>, LspError> {
        let launch = entry
            .launch(root)
            .map_err(|missing| LspError::ServerUnavailable {
                server: entry.name.clone(),
                reason: missing.to_string(),
            })?;
        let key = PoolKey {
            server: entry.name.clone(),
            root: root.to_owned(),
            fingerprint: entry.fingerprint(&launch),
        };
        self.inner
            .pool
            .get_or_start(&key, LspClient::exited, || async {
                LspClient::start(entry, &launch, root)
                    .await
                    .map_err(|error| error.to_string())
            })
            .await
            .map_err(|refused| match refused {
                Refused::Startup(reason) => LspError::ServerUnavailable {
                    server: entry.name.clone(),
                    reason,
                },
                Refused::Backoff {
                    retry_after,
                    reason,
                } => LspError::Backoff {
                    server: entry.name.clone(),
                    retry_after_ms: u64::try_from(retry_after.as_millis()).unwrap_or(u64::MAX),
                    reason,
                },
            })
    }

    /// [`Self::client`] in its own task, so a caller that stops waiting
    /// does not cancel the start.
    fn start_detached(
        &self,
        root: &Path,
        entry: &RosterEntry,
    ) -> tokio::task::JoinHandle<Result<Arc<LspClient>, LspError>> {
        let service = self.clone();
        let root = root.to_owned();
        let entry = entry.clone();
        tokio::spawn(async move { service.client(&root, &entry).await })
    }

    /// The first server handling `path` that starts and serves `method`.
    async fn first_client(
        &self,
        root: &Path,
        path: &Path,
        method: &str,
    ) -> Result<Arc<LspClient>, LspError> {
        let mut failure = None;
        for entry in self.handlers(root, path) {
            match self.client(root, &entry).await {
                Ok(client) if client.supports(method) => return Ok(client),
                Ok(client) => {
                    failure.get_or_insert(LspError::NotSupported {
                        server: client.name.clone(),
                        method: method.to_owned(),
                    });
                }
                Err(error) => {
                    failure.get_or_insert(error);
                }
            }
        }
        Err(failure.unwrap_or_else(|| LspError::NoServer {
            root: root.to_owned(),
            path: path.to_owned(),
        }))
    }

    /// Give `client` the disk text of `path`; returns the text.
    async fn open(client: &LspClient, path: &Path) -> Result<String, LspError> {
        let text = read_text(path).await?;
        client.sync(path, text.clone()).await?;
        Ok(text)
    }

    fn position(client: &LspClient, target: &LspTarget, text: &str) -> Result<Value, LspError> {
        let lines = position::lines(text);
        let (column, _) =
            position::symbol_column(&target.path, &lines, target.line, &target.symbol)?;
        let line_index = target.line - 1;
        let line_text = lines.get(line_index as usize).copied().unwrap_or_default();
        Ok(json!({
            "textDocument": { "uri": file_uri(&target.path)? },
            "position": position::to_lsp(line_text, line_index, column, client.encoding),
        }))
    }

    async fn navigate(
        &self,
        root: &Path,
        navigation: LspNavigation,
        target: &LspTarget,
    ) -> Result<Vec<LspLocation>, LspError> {
        let method = match navigation {
            LspNavigation::Definition => "textDocument/definition",
            LspNavigation::TypeDefinition => "textDocument/typeDefinition",
            LspNavigation::Implementation => "textDocument/implementation",
            LspNavigation::References => "textDocument/references",
        };
        let client = self.first_client(root, &target.path, method).await?;
        let text = Self::open(&client, &target.path).await?;
        client.project_loaded().await;
        let mut params = Self::position(&client, target, &text)?;
        if navigation == LspNavigation::References {
            params["context"] = json!({ "includeDeclaration": true });
        }
        let response: Option<LocationResponse> = client.request(method, params).await?;
        let locations = response
            .map(LocationResponse::into_locations)
            .unwrap_or_default();
        Ok(locations_of(&client, locations).await)
    }

    async fn hover(&self, root: &Path, target: &LspTarget) -> Result<Option<String>, LspError> {
        let method = "textDocument/hover";
        let client = self.first_client(root, &target.path, method).await?;
        let text = Self::open(&client, &target.path).await?;
        client.project_loaded().await;
        let params = Self::position(&client, target, &text)?;
        let hover: Option<Hover> = client.request(method, params).await?;
        Ok(hover
            .map(|hover| hover.contents.into_text())
            .filter(|text| !text.trim().is_empty()))
    }

    async fn symbols(
        &self,
        root: &Path,
        scope: LspScope,
        query: Option<&str>,
    ) -> Result<Vec<LspSymbol>, LspError> {
        let matches = |name: &str| {
            query.is_none_or(|query| name.to_lowercase().contains(&query.to_lowercase()))
        };
        match scope {
            LspScope::File(path) => {
                let method = "textDocument/documentSymbol";
                let client = self.first_client(root, &path, method).await?;
                let text = Self::open(&client, &path).await?;
                let response: Option<DocumentSymbolResponse> = client
                    .request(
                        method,
                        json!({ "textDocument": { "uri": file_uri(&path)? } }),
                    )
                    .await?;
                let lines = position::lines(&text);
                let mut symbols = Vec::new();
                match response {
                    Some(DocumentSymbolResponse::Nested(nested)) => {
                        flatten(&path, &lines, client.encoding, &nested, None, &mut symbols);
                    }
                    Some(DocumentSymbolResponse::Flat(flat)) => {
                        symbols.extend(symbols_of(&client, flat).await);
                    }
                    None => {}
                }
                symbols.retain(|symbol| matches(&symbol.name));
                Ok(symbols)
            }
            LspScope::Workspace => {
                let method = "workspace/symbol";
                let mut failure = None;
                let mut answered = false;
                let mut symbols = Vec::new();
                for entry in self.roster(root).iter() {
                    let client = match self.client(root, entry).await {
                        Ok(client) => client,
                        Err(error) => {
                            failure.get_or_insert(error);
                            continue;
                        }
                    };
                    if !client.supports(method) {
                        continue;
                    }
                    client.project_loaded().await;
                    let found: Option<Vec<Value>> = match client
                        .request(method, json!({ "query": query.unwrap_or_default() }))
                        .await
                    {
                        Ok(found) => found,
                        Err(error) => {
                            failure.get_or_insert(error);
                            continue;
                        }
                    };
                    answered = true;
                    // Symbols without a resolved range (`location: {uri}`)
                    // are not reported.
                    let located = found
                        .into_iter()
                        .flatten()
                        .filter_map(|value| serde_json::from_value::<SymbolInformation>(value).ok())
                        .collect();
                    symbols.extend(symbols_of(&client, located).await);
                }
                if !answered {
                    return Err(failure.unwrap_or_else(|| LspError::NoServer {
                        root: root.to_owned(),
                        path: root.to_owned(),
                    }));
                }
                symbols.retain(|symbol| matches(&symbol.name));
                symbols.truncate(WORKSPACE_SYMBOL_LIMIT);
                Ok(symbols)
            }
        }
    }

    async fn rename(
        &self,
        root: &Path,
        target: &LspTarget,
        new_name: &str,
    ) -> Result<LspWorkspaceEdit, LspError> {
        let method = "textDocument/rename";
        let client = self.first_client(root, &target.path, method).await?;
        let text = Self::open(&client, &target.path).await?;
        client.project_loaded().await;
        let mut params = Self::position(&client, target, &text)?;
        params["newName"] = json!(new_name);
        let edit: Option<WorkspaceEdit> = client.request(method, params).await?;
        workspace_edit(&client, vec![edit.unwrap_or_default()]).await
    }

    #[allow(clippy::too_many_lines)] // one pass: list per server, then apply the selection
    async fn code_actions(
        &self,
        root: &Path,
        target: &LspTarget,
        apply: Option<&CodeActionSelector>,
    ) -> Result<CodeActionsReport, LspError> {
        let method = "textDocument/codeAction";
        let mut failure = None;
        let mut listed: Vec<Listed> = Vec::new();
        let mut answered = false;
        for entry in self.handlers(root, &target.path) {
            let client = match self.client(root, &entry).await {
                Ok(client) if client.supports(method) => client,
                Ok(_) => continue,
                Err(error) => {
                    failure.get_or_insert(error);
                    continue;
                }
            };
            let text = Self::open(&client, &target.path).await?;
            let lines = position::lines(&text);
            let (column, length) =
                position::symbol_column(&target.path, &lines, target.line, &target.symbol)?;
            let line_index = target.line - 1;
            let line_text = lines.get(line_index as usize).copied().unwrap_or_default();
            let start = position::to_lsp(line_text, line_index, column, client.encoding);
            let end = position::to_lsp(line_text, line_index, column + length, client.encoding);
            let diagnostics = client.line_diagnostics(&target.path, line_index).await;
            let found: Option<Vec<Value>> = match client
                .request(
                    method,
                    json!({
                        "textDocument": { "uri": file_uri(&target.path)? },
                        "range": { "start": start, "end": end },
                        "context": { "diagnostics": diagnostics, "triggerKind": 1 },
                    }),
                )
                .await
            {
                Ok(found) => found,
                Err(error) => {
                    failure.get_or_insert(error);
                    continue;
                }
            };
            answered = true;
            for raw in found.into_iter().flatten() {
                let entry: CodeActionEntry =
                    serde_json::from_value(raw.clone()).map_err(|error| {
                        LspError::InvalidResult {
                            server: client.name.clone(),
                            method: method.to_owned(),
                            reason: error.to_string(),
                        }
                    })?;
                let (title, kind, preferred) = match &entry {
                    CodeActionEntry::Action(action) => (
                        action.title.clone(),
                        action.kind.clone(),
                        action.is_preferred,
                    ),
                    CodeActionEntry::Command(command) => (command.title.clone(), None, false),
                };
                let info = LspCodeAction {
                    index: listed.len(),
                    title,
                    kind,
                    preferred,
                    server: client.name.clone(),
                };
                listed.push(Listed {
                    client: Arc::clone(&client),
                    raw,
                    entry,
                    info,
                });
            }
        }
        if !answered {
            return Err(failure.unwrap_or_else(|| LspError::NoServer {
                root: root.to_owned(),
                path: target.path.clone(),
            }));
        }
        let applied = match apply {
            None => None,
            Some(selector) => {
                let chosen = listed
                    .iter()
                    .find(|listed| match selector {
                        CodeActionSelector::Index(index) => listed.info.index == *index,
                        CodeActionSelector::Title(title) => listed
                            .info
                            .title
                            .to_lowercase()
                            .contains(&title.to_lowercase()),
                    })
                    .ok_or_else(|| LspError::NoCodeAction {
                        selector: selector.clone(),
                    })?;
                Some(apply_action(chosen).await?)
            }
        };
        Ok(CodeActionsReport {
            actions: listed.into_iter().map(|listed| listed.info).collect(),
            applied,
        })
    }

    fn status(&self, root: &Path) -> Vec<LspServerStatus> {
        self.roster(root)
            .iter()
            .map(|entry| {
                let (state, detail) = match entry.launch(root) {
                    Err(missing) => (LspServerState::Missing, Some(missing.to_string())),
                    Ok(launch) => {
                        let key = PoolKey {
                            server: entry.name.clone(),
                            root: root.to_owned(),
                            fingerprint: entry.fingerprint(&launch),
                        };
                        match self.inner.pool.state(&key) {
                            SlotState::Empty => (LspServerState::Available, None),
                            SlotState::Starting => (LspServerState::Starting, None),
                            SlotState::Failed { reason } => (LspServerState::Failed, Some(reason)),
                            SlotState::Ready => match self
                                .inner
                                .pool
                                .ready(&key)
                                .and_then(|client| client.exited())
                            {
                                Some(reason) => (LspServerState::Failed, Some(reason)),
                                None => (LspServerState::Ready, None),
                            },
                        }
                    }
                };
                LspServerStatus {
                    name: entry.name.clone(),
                    state,
                    file_types: entry.spec.file_types.clone(),
                    detail,
                }
            })
            .collect()
    }

    /// A committed write: ready servers get the text and are waited on
    /// for the inline window; servers not started yet start in the
    /// background and are reported pending.
    async fn sync(&self, root: &Path, path: &Path, text: &str) -> DiagnosticsReport {
        let deadline = tokio::time::Instant::now() + INLINE_DIAGNOSTICS_WAIT;
        let mut report = DiagnosticsReport {
            diagnostics: Vec::new(),
            pending: Vec::new(),
        };
        for entry in self.handlers(root, path) {
            let Some(key) = Self::key(&entry, root) else {
                continue;
            };
            match self.inner.pool.state(&key) {
                SlotState::Failed { .. } => {}
                SlotState::Empty | SlotState::Starting => {
                    report.pending.push(entry.name.clone());
                    // The start goes on without this write; its failure is
                    // cached in the pool and reported by the next request.
                    drop(self.start_detached(root, &entry));
                }
                SlotState::Ready => {
                    let Some(client) = self
                        .inner
                        .pool
                        .ready(&key)
                        .filter(|client| client.exited().is_none())
                    else {
                        continue;
                    };
                    let fresh = match client.sync(path, text.to_owned()).await {
                        Ok(()) => client.fresh_diagnostics(path, deadline).await,
                        Err(error) => {
                            tracing::debug!(server = %client.name, %error, "LSP sync failed");
                            continue;
                        }
                    };
                    match fresh {
                        Some(diagnostics) => report.diagnostics.extend(diagnostics),
                        None => report.pending.push(client.name.clone()),
                    }
                }
            }
        }
        report
    }

    /// The late window after a [`Self::sync`] with pending servers: wait
    /// for their start, give them the disk text, and wait for fresh
    /// diagnostics.
    async fn await_diagnostics(&self, root: &Path, path: &Path) -> DiagnosticsReport {
        self.collect_fresh(root, path, LATE_DIAGNOSTICS_WAIT)
            .await
            .0
    }

    /// Fresh diagnostics of `path` from every server handling it, started
    /// as needed, within `wait`; the first failure when no server answered.
    async fn collect_fresh(
        &self,
        root: &Path,
        path: &Path,
        wait: Duration,
    ) -> (DiagnosticsReport, Option<LspError>) {
        let deadline = tokio::time::Instant::now() + wait;
        let mut report = DiagnosticsReport {
            diagnostics: Vec::new(),
            pending: Vec::new(),
        };
        let mut failure = None;
        let mut answered = false;
        for entry in self.handlers(root, path) {
            let start = self.start_detached(root, &entry);
            let fresh = async {
                let client = start.await.map_err(|error| LspError::ServerUnavailable {
                    server: entry.name.clone(),
                    reason: error.to_string(),
                })??;
                Self::open(&client, path).await?;
                Ok::<_, LspError>(client.fresh_diagnostics(path, deadline).await)
            };
            match tokio::time::timeout_at(deadline, fresh).await {
                Ok(Ok(Some(diagnostics))) => {
                    answered = true;
                    report.diagnostics.extend(diagnostics);
                }
                Ok(Ok(None)) | Err(_) => {
                    answered = true;
                    report.pending.push(entry.name.clone());
                }
                Ok(Err(error)) => {
                    failure.get_or_insert(error);
                }
            }
        }
        let failure = if answered {
            None
        } else {
            Some(failure.unwrap_or_else(|| LspError::NoServer {
                root: root.to_owned(),
                path: path.to_owned(),
            }))
        };
        (report, failure)
    }

    async fn diagnostics(
        &self,
        root: &Path,
        scope: LspScope,
    ) -> Result<DiagnosticsReport, LspError> {
        match scope {
            LspScope::File(path) => match self.collect_fresh(root, &path, DIAGNOSTICS_WAIT).await {
                (_, Some(failure)) => Err(failure),
                (report, None) => Ok(report),
            },
            LspScope::Workspace => {
                let mut diagnostics: Vec<LspDiagnostic> = Vec::new();
                for entry in self.roster(root).iter() {
                    let Some(client) =
                        Self::key(entry, root).and_then(|key| self.inner.pool.ready(&key))
                    else {
                        continue;
                    };
                    for (path, items) in client.all_diagnostics() {
                        let text = match client.document_text(&path).await {
                            Some(text) => text,
                            None => read_text(&path).await?,
                        };
                        diagnostics.extend(client.convert(&path, &text, &items));
                    }
                }
                Ok(DiagnosticsReport {
                    diagnostics,
                    pending: Vec::new(),
                })
            }
        }
    }
}

/// The edit of a chosen code action: its own edit (resolved first when the
/// server resolves lazily) plus every edit its command asked for.
async fn apply_action(chosen: &Listed) -> Result<AppliedCodeAction, LspError> {
    let client = &chosen.client;
    let mut edits = Vec::new();
    let command = match &chosen.entry {
        CodeActionEntry::Command(command) => Some(command.clone()),
        CodeActionEntry::Action(action) => {
            let action = if action.edit.is_none()
                && action.command.is_none()
                && client.supports("codeAction/resolve")
            {
                client
                    .request::<CodeAction>("codeAction/resolve", chosen.raw.clone())
                    .await?
            } else {
                action.clone()
            };
            edits.extend(action.edit);
            action.command
        }
    };
    if let Some(command) = command {
        edits.extend(client.execute_command(&command).await?);
    }
    Ok(AppliedCodeAction {
        action: chosen.info.clone(),
        edit: workspace_edit(client, edits).await?,
    })
}

/// Typed edits of `edits`, merged per file in first-seen order; spans are
/// converted against the text the server has (or the disk text).
async fn workspace_edit(
    client: &LspClient,
    edits: Vec<WorkspaceEdit>,
) -> Result<LspWorkspaceEdit, LspError> {
    let mut files: Vec<(PathBuf, String, Vec<crate::protocol::TextEdit>)> = Vec::new();
    for (uri, text_edits) in edits.into_iter().flat_map(WorkspaceEdit::by_document) {
        let path = uri.to_file_path().map_err(|()| LspError::InvalidResult {
            server: client.name.clone(),
            method: "workspaceEdit".to_owned(),
            reason: format!("{uri} is not a file URI"),
        })?;
        if let Some((_, _, known)) = files.iter_mut().find(|(known, _, _)| *known == path) {
            known.extend(text_edits);
        } else {
            let text = match client.document_text(&path).await {
                Some(text) => text,
                None => read_text(&path).await?,
            };
            files.push((path, text, text_edits));
        }
    }
    Ok(LspWorkspaceEdit {
        files: files
            .into_iter()
            .filter(|(_, _, edits)| !edits.is_empty())
            .map(|(path, text, edits)| {
                let lines = position::lines(&text);
                LspFileEdit {
                    path,
                    edits: edits
                        .into_iter()
                        .map(|edit| LspTextEdit {
                            span: position::span_from_lsp(&lines, edit.range, client.encoding),
                            new_text: edit.new_text,
                        })
                        .collect(),
                }
            })
            .collect(),
    })
}

/// Typed locations. Locations outside `file://` or in unreadable files are
/// left out (their columns cannot be converted).
async fn locations_of(client: &LspClient, locations: Vec<Location>) -> Vec<LspLocation> {
    let mut texts: HashMap<PathBuf, Option<String>> = HashMap::new();
    let mut typed = Vec::new();
    for location in locations {
        let Some((path, text)) = located_text(client, &location.uri, &mut texts).await else {
            continue;
        };
        typed.push(location_in(
            &path,
            &position::lines(&text),
            location.range,
            client.encoding,
        ));
    }
    typed
}

async fn symbols_of(client: &LspClient, symbols: Vec<SymbolInformation>) -> Vec<LspSymbol> {
    let mut texts: HashMap<PathBuf, Option<String>> = HashMap::new();
    let mut typed = Vec::new();
    for symbol in symbols {
        let Some((path, text)) = located_text(client, &symbol.location.uri, &mut texts).await
        else {
            continue;
        };
        typed.push(LspSymbol {
            name: symbol.name,
            kind: symbol_kind_name(symbol.kind),
            container: symbol.container_name.filter(|name| !name.is_empty()),
            location: location_in(
                &path,
                &position::lines(&text),
                symbol.location.range,
                client.encoding,
            ),
        });
    }
    typed
}

async fn located_text(
    client: &LspClient,
    uri: &Url,
    texts: &mut HashMap<PathBuf, Option<String>>,
) -> Option<(PathBuf, String)> {
    let Ok(path) = uri.to_file_path() else {
        tracing::debug!(%uri, "skipping a non-file LSP location");
        return None;
    };
    if !texts.contains_key(&path) {
        let text = match client.document_text(&path).await {
            Some(text) => Some(text),
            None => match read_text(&path).await {
                Ok(text) => Some(text),
                Err(error) => {
                    tracing::debug!(%error, "skipping an LSP location in an unreadable file");
                    None
                }
            },
        };
        texts.insert(path.clone(), text);
    }
    let text = texts.get(&path).cloned().flatten()?;
    Some((path, text))
}

fn location_in(
    path: &Path,
    lines: &[&str],
    range: crate::protocol::Range,
    encoding: PositionEncoding,
) -> LspLocation {
    LspLocation {
        path: path.to_owned(),
        span: position::span_from_lsp(lines, range, encoding),
        line_text: lines
            .get(range.start.line as usize)
            .copied()
            .unwrap_or_default()
            .to_owned(),
    }
}

/// Document symbols, depth first, each with its parent's name.
fn flatten(
    path: &Path,
    lines: &[&str],
    encoding: PositionEncoding,
    symbols: &[DocumentSymbol],
    container: Option<&str>,
    out: &mut Vec<LspSymbol>,
) {
    for symbol in symbols {
        out.push(LspSymbol {
            name: symbol.name.clone(),
            kind: symbol_kind_name(symbol.kind),
            container: container.map(str::to_owned),
            location: location_in(path, lines, symbol.selection_range, encoding),
        });
        flatten(
            path,
            lines,
            encoding,
            &symbol.children,
            Some(&symbol.name),
            out,
        );
    }
}

async fn read_text(path: &Path) -> Result<String, LspError> {
    tokio::fs::read_to_string(path)
        .await
        .map_err(|error| match error.kind() {
            std::io::ErrorKind::NotFound => LspError::FileNotFound {
                path: path.to_owned(),
            },
            _ => LspError::Read {
                path: path.to_owned(),
                reason: error.to_string(),
            },
        })
}
