//! One running language server: process, initialize handshake, document
//! synchronization (`didOpen`/`didChange`/`didSave`, full text), the
//! published diagnostics, and typed requests.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::process::Stdio;
use std::sync::Arc;
use std::time::{Duration, Instant};

use parking_lot::Mutex;
use serde::de::DeserializeOwned;
use serde_json::{json, Value};
use tokio::process::{Child, Command};
use tokio::sync::watch;
use url::Url;

use eukhe_types::lsp::{LspDiagnostic, LspError, LspSeverity};

use crate::position::{self, PositionEncoding};
use crate::protocol::{
    enabled, Diagnostic, DocumentDiagnosticReport, NumberOrString, PublishDiagnosticsParams,
    ServerCapabilities, TextDocumentSync, WorkspaceEdit,
};
use crate::rpc::{Inbound, ResponseError, RpcFailure, Transport, INVALID_PARAMS, METHOD_NOT_FOUND};
use crate::servers::{language_id, Launch, RosterEntry};

/// Initialize deadline when the declaration names none (omp2).
const DEFAULT_INITIALIZE_TIMEOUT: Duration = Duration::from_secs(10);
/// Deadline of one request.
pub(crate) const REQUEST_TIMEOUT: Duration = Duration::from_secs(30);
/// How long project-aware requests wait for the first indexing progress to
/// end (omp `PROJECT_LOAD_TIMEOUT_MS`).
const PROJECT_LOAD_TIMEOUT: Duration = Duration::from_secs(15);
/// A publish without a document version counts once no newer one arrived
/// for this long (omp `DIAGNOSTICS_SETTLE_MS`).
const DIAGNOSTICS_SETTLE: Duration = Duration::from_millis(250);
/// Graceful shutdown deadline before the process is killed.
const SHUTDOWN_TIMEOUT: Duration = Duration::from_secs(3);

/// Why a server could not be started.
#[derive(Debug, Clone, thiserror::Error)]
pub(crate) enum StartError {
    #[error(transparent)]
    Missing(#[from] crate::servers::MissingExecutable),
    #[error("cannot spawn {executable:?}: {reason}")]
    Spawn { executable: PathBuf, reason: String },
    #[error("initialize failed: {0}")]
    Initialize(RpcFailure),
    #[error("initialize returned invalid capabilities: {0}")]
    Capabilities(String),
}

/// The latest `publishDiagnostics` of one document.
struct Published {
    version: Option<i32>,
    diagnostics: Vec<Diagnostic>,
    /// The publish counter value this publish took.
    sequence: u64,
    at: Instant,
}

/// One open document as the server has it.
struct OpenDocument {
    uri: Url,
    version: i32,
    text: String,
    /// The publish counter when the server last received this text.
    synced_at: u64,
}

#[derive(Default)]
struct Progress {
    tokens: HashSet<String>,
    reports_status: bool,
}

/// Server-initiated state the reader task writes.
struct Shared {
    root_uri: Url,
    root_name: String,
    settings: Value,
    diagnostics: Mutex<HashMap<Url, Published>>,
    /// Counts publishes; waiters watch it.
    publishes: watch::Sender<u64>,
    /// Methods registered with `client/registerCapability`.
    registered: Mutex<HashSet<String>>,
    /// Work-done progress tokens in flight, and whether the server reports
    /// `experimental/serverStatus` (rust-analyzer). `loaded` flips once:
    /// on the first quiescent status, else when the first progress round
    /// ended, else at the project-load timeout.
    progress: Mutex<Progress>,
    loaded: watch::Sender<bool>,
    /// Edits the server asked to apply (`workspace/applyEdit`) while a
    /// command runs; `None` when no command is running.
    captured: Mutex<Option<Vec<WorkspaceEdit>>>,
}

impl Inbound for Shared {
    fn notification(&self, method: &str, params: Value) {
        match method {
            "textDocument/publishDiagnostics" => {
                let Ok(params) = serde_json::from_value::<PublishDiagnosticsParams>(params) else {
                    tracing::warn!("dropping malformed publishDiagnostics");
                    return;
                };
                // The reader task is the only writer of the counter.
                let sequence = *self.publishes.borrow() + 1;
                self.diagnostics.lock().insert(
                    params.uri,
                    Published {
                        version: params.version,
                        diagnostics: params.diagnostics,
                        sequence,
                        at: Instant::now(),
                    },
                );
                self.publishes.send_replace(sequence);
            }
            "$/progress" => {
                let token = params
                    .get("token")
                    .map(Value::to_string)
                    .unwrap_or_default();
                let kind = params.pointer("/value/kind").and_then(Value::as_str);
                let mut progress = self.progress.lock();
                match kind {
                    Some("begin") => {
                        progress.tokens.insert(token);
                    }
                    Some("end") => {
                        progress.tokens.remove(&token);
                        if progress.tokens.is_empty() && !progress.reports_status {
                            self.loaded.send_replace(true);
                        }
                    }
                    Some(_) | None => {}
                }
            }
            "experimental/serverStatus" => {
                self.progress.lock().reports_status = true;
                if params.get("quiescent").and_then(Value::as_bool) == Some(true) {
                    self.loaded.send_replace(true);
                }
            }
            _ => {}
        }
    }

    fn request(&self, method: &str, params: Value) -> Result<Value, ResponseError> {
        match method {
            "workspace/configuration" => {
                let items = params
                    .get("items")
                    .and_then(Value::as_array)
                    .ok_or_else(|| ResponseError {
                        code: INVALID_PARAMS,
                        message: "workspace/configuration requires items".to_owned(),
                    })?;
                Ok(Value::Array(
                    items
                        .iter()
                        .map(|item| match item.get("section").and_then(Value::as_str) {
                            Some(section) => section
                                .split('.')
                                .try_fold(&self.settings, |value, key| value.get(key))
                                .cloned()
                                .unwrap_or(Value::Null),
                            None => self.settings.clone(),
                        })
                        .collect(),
                ))
            }
            "workspace/workspaceFolders" => {
                Ok(json!([{ "uri": self.root_uri, "name": self.root_name }]))
            }
            "client/registerCapability" => {
                let methods = params
                    .get("registrations")
                    .and_then(Value::as_array)
                    .into_iter()
                    .flatten()
                    .filter_map(|registration| registration.get("method").and_then(Value::as_str));
                self.registered.lock().extend(methods.map(str::to_owned));
                Ok(Value::Null)
            }
            "workspace/applyEdit" => {
                let mut captured = self.captured.lock();
                let Some(edits) = captured.as_mut() else {
                    return Ok(
                        json!({ "applied": false, "failureReason": "no command is running" }),
                    );
                };
                let edit = params
                    .get("edit")
                    .cloned()
                    .map(serde_json::from_value::<WorkspaceEdit>)
                    .transpose()
                    .map_err(|error| ResponseError {
                        code: INVALID_PARAMS,
                        message: error.to_string(),
                    })?
                    .unwrap_or_default();
                edits.push(edit);
                Ok(json!({ "applied": true }))
            }
            "client/unregisterCapability"
            | "window/workDoneProgress/create"
            | "window/showMessageRequest"
            | "workspace/semanticTokens/refresh"
            | "workspace/codeLens/refresh"
            | "workspace/inlayHint/refresh"
            | "workspace/diagnostic/refresh"
            | "workspace/inlineValue/refresh" => Ok(Value::Null),
            "window/showDocument" => Ok(json!({ "success": false })),
            _ => Err(ResponseError {
                code: METHOD_NOT_FOUND,
                message: format!("unhandled server request {method}"),
            }),
        }
    }
}

/// How the server wants document changes.
#[derive(Clone, Copy, PartialEq, Eq)]
enum SyncKind {
    None,
    /// Full or incremental: a change without a range replaces the text,
    /// which both accept.
    Changes,
}

/// A started and initialized server.
pub(crate) struct LspClient {
    pub(crate) name: String,
    transport: Transport,
    shared: Arc<Shared>,
    capabilities: ServerCapabilities,
    pub(crate) encoding: PositionEncoding,
    sync: SyncKind,
    save: bool,
    documents: tokio::sync::Mutex<HashMap<PathBuf, OpenDocument>>,
    child: Mutex<Option<Child>>,
}

impl LspClient {
    /// Spawn `launch` in `root` and run the initialize handshake.
    #[tracing::instrument(level = "debug", skip_all, fields(server = %entry.name))]
    #[allow(clippy::too_many_lines)] // one linear spawn + initialize handshake
    pub(crate) async fn start(
        entry: &RosterEntry,
        launch: &Launch,
        root: &Path,
    ) -> Result<Self, StartError> {
        let mut child = Command::new(&launch.executable)
            .args(&launch.args)
            .current_dir(root)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .kill_on_drop(true)
            .spawn()
            .map_err(|error| StartError::Spawn {
                executable: launch.executable.clone(),
                reason: error.to_string(),
            })?;
        let (Some(stdin), Some(stdout)) = (child.stdin.take(), child.stdout.take()) else {
            return Err(StartError::Spawn {
                executable: launch.executable.clone(),
                reason: "the child has no piped stdio".to_owned(),
            });
        };
        let root_uri = Url::from_directory_path(root).map_err(|()| StartError::Spawn {
            executable: launch.executable.clone(),
            reason: format!("{} is not an absolute directory", root.display()),
        })?;
        let root_name = root.file_name().map_or_else(
            || "workspace".to_owned(),
            |name| name.to_string_lossy().into_owned(),
        );
        let settings = entry.spec.settings.clone().unwrap_or(Value::Null);
        let shared = Arc::new(Shared {
            root_uri: root_uri.clone(),
            root_name: root_name.clone(),
            settings: settings.clone(),
            diagnostics: Mutex::default(),
            publishes: watch::Sender::new(0),
            registered: Mutex::default(),
            progress: Mutex::default(),
            loaded: watch::Sender::new(false),
            captured: Mutex::default(),
        });
        let transport = Transport::start(stdout, stdin, Arc::clone(&shared) as Arc<dyn Inbound>);
        let mut params = json!({
            "processId": std::process::id(),
            "clientInfo": { "name": "eukhe" },
            "rootUri": root_uri,
            "rootPath": root,
            "workspaceFolders": [{ "uri": root_uri, "name": root_name }],
            "capabilities": client_capabilities(),
        });
        if let Some(options) = &entry.spec.init_options {
            params["initializationOptions"] = options.clone();
        }
        let timeout = entry
            .spec
            .warmup_timeout_ms
            .map_or(DEFAULT_INITIALIZE_TIMEOUT, Duration::from_millis);
        let result = transport
            .request("initialize", params, timeout)
            .await
            .map_err(StartError::Initialize)?;
        let capabilities: ServerCapabilities =
            serde_json::from_value(result.get("capabilities").cloned().unwrap_or(Value::Null))
                .map_err(|error| StartError::Capabilities(error.to_string()))?;
        transport
            .notify("initialized", &json!({}))
            .map_err(StartError::Initialize)?;
        if !settings.is_null() {
            transport
                .notify(
                    "workspace/didChangeConfiguration",
                    &json!({ "settings": settings }),
                )
                .map_err(StartError::Initialize)?;
        }
        let (sync, save) = match &capabilities.text_document_sync {
            None | Some(TextDocumentSync::Kind(0)) => (SyncKind::None, false),
            Some(TextDocumentSync::Kind(_)) => (SyncKind::Changes, false),
            Some(TextDocumentSync::Options(options)) => (
                if options.change.unwrap_or(0) == 0 {
                    SyncKind::None
                } else {
                    SyncKind::Changes
                },
                enabled(options.save.as_ref()),
            ),
        };
        let loaded = shared.loaded.clone();
        tokio::spawn(async move {
            tokio::time::sleep(PROJECT_LOAD_TIMEOUT).await;
            loaded.send_replace(true);
        });
        Ok(Self {
            name: entry.name.clone(),
            transport,
            encoding: PositionEncoding::from_server(capabilities.position_encoding.as_deref()),
            capabilities,
            shared,
            sync,
            save,
            documents: tokio::sync::Mutex::default(),
            child: Mutex::new(Some(child)),
        })
    }

    /// Why the server is gone, once it is.
    pub(crate) fn exited(&self) -> Option<String> {
        self.transport.closed()
    }

    /// Whether the server serves `method` (statically or by registration).
    pub(crate) fn supports(&self, method: &str) -> bool {
        let capabilities = &self.capabilities;
        let capability = match method {
            "textDocument/definition" => capabilities.definition_provider.as_ref(),
            "textDocument/typeDefinition" => capabilities.type_definition_provider.as_ref(),
            "textDocument/implementation" => capabilities.implementation_provider.as_ref(),
            "textDocument/references" => capabilities.references_provider.as_ref(),
            "textDocument/hover" => capabilities.hover_provider.as_ref(),
            "textDocument/documentSymbol" => capabilities.document_symbol_provider.as_ref(),
            "workspace/symbol" => capabilities.workspace_symbol_provider.as_ref(),
            "textDocument/rename" => capabilities.rename_provider.as_ref(),
            "textDocument/codeAction" => capabilities.code_action_provider.as_ref(),
            "textDocument/diagnostic" => capabilities.diagnostic_provider.as_ref(),
            "codeAction/resolve" => capabilities
                .code_action_provider
                .as_ref()
                .and_then(|options| options.get("resolveProvider")),
            _ => None,
        };
        enabled(capability) || self.shared.registered.lock().contains(method)
    }

    fn require(&self, method: &str) -> Result<(), LspError> {
        if self.supports(method) {
            Ok(())
        } else {
            Err(LspError::NotSupported {
                server: self.name.clone(),
                method: method.to_owned(),
            })
        }
    }

    /// Send a request; `T` is the result type (`Option<..>` for nullable
    /// results).
    pub(crate) async fn request<T: DeserializeOwned>(
        &self,
        method: &str,
        params: Value,
    ) -> Result<T, LspError> {
        self.require(method)?;
        self.raw_request(method, params).await
    }

    async fn raw_request<T: DeserializeOwned>(
        &self,
        method: &str,
        params: Value,
    ) -> Result<T, LspError> {
        let result = self
            .transport
            .request(method, params, REQUEST_TIMEOUT)
            .await
            .map_err(|failure| self.failure(method, failure))?;
        serde_json::from_value(result).map_err(|error| LspError::InvalidResult {
            server: self.name.clone(),
            method: method.to_owned(),
            reason: error.to_string(),
        })
    }

    fn failure(&self, method: &str, failure: RpcFailure) -> LspError {
        match failure {
            RpcFailure::Closed(reason) => LspError::ServerUnavailable {
                server: self.name.clone(),
                reason,
            },
            RpcFailure::Timeout => LspError::Timeout {
                server: self.name.clone(),
                method: method.to_owned(),
                timeout_ms: u64::try_from(REQUEST_TIMEOUT.as_millis()).unwrap_or(u64::MAX),
            },
            RpcFailure::Response(error) => LspError::Request {
                server: self.name.clone(),
                method: method.to_owned(),
                code: error.code,
                message: error.message,
            },
        }
    }

    /// Wait (bounded) until the server's first indexing progress ended.
    pub(crate) async fn project_loaded(&self) {
        let mut loaded = self.shared.loaded.subscribe();
        // The sender lives in `self.shared`, so the wait cannot fail.
        let _ = loaded.wait_for(|loaded| *loaded).await;
    }

    /// Give the server `text` as the content of `path` (open it, or send a
    /// change when the text differs from what it has).
    pub(crate) async fn sync(&self, path: &Path, text: String) -> Result<(), LspError> {
        let mut documents = self.documents.lock().await;
        let published = *self.shared.publishes.borrow();
        match documents.get_mut(path) {
            Some(document) if document.text == text => Ok(()),
            Some(document) => {
                if self.sync == SyncKind::None {
                    return Ok(());
                }
                document.version += 1;
                document.text = text;
                document.synced_at = published;
                self.notify(
                    "textDocument/didChange",
                    &json!({
                        "textDocument": { "uri": document.uri, "version": document.version },
                        "contentChanges": [{ "text": document.text }],
                    }),
                )?;
                if self.save {
                    self.notify(
                        "textDocument/didSave",
                        &json!({ "textDocument": { "uri": document.uri } }),
                    )?;
                }
                Ok(())
            }
            None => {
                let uri = file_uri(path)?;
                self.notify(
                    "textDocument/didOpen",
                    &json!({
                        "textDocument": {
                            "uri": uri,
                            "languageId": language_id(path),
                            "version": 1,
                            "text": text,
                        },
                    }),
                )?;
                documents.insert(
                    path.to_owned(),
                    OpenDocument {
                        uri,
                        version: 1,
                        text,
                        synced_at: published,
                    },
                );
                Ok(())
            }
        }
    }

    /// The text the server has for `path`, when it is open.
    pub(crate) async fn document_text(&self, path: &Path) -> Option<String> {
        self.documents
            .lock()
            .await
            .get(path)
            .map(|document| document.text.clone())
    }

    fn notify(&self, method: &str, params: &Value) -> Result<(), LspError> {
        self.transport
            .notify(method, params)
            .map_err(|failure| self.failure(method, failure))
    }

    /// Fresh diagnostics of the open document `path`, waiting until
    /// `deadline`; `None` when none arrived in time. Pull-capable servers
    /// are asked (`textDocument/diagnostic`); others count when a publish
    /// for the synced version arrived after the last sync, or a publish
    /// without a version settled.
    pub(crate) async fn fresh_diagnostics(
        &self,
        path: &Path,
        deadline: tokio::time::Instant,
    ) -> Option<Vec<LspDiagnostic>> {
        let (uri, version, synced_at, text) = {
            let documents = self.documents.lock().await;
            let document = documents.get(path)?;
            (
                document.uri.clone(),
                document.version,
                document.synced_at,
                document.text.clone(),
            )
        };
        if self.supports("textDocument/diagnostic") {
            let pulled = tokio::time::timeout_at(
                deadline,
                self.raw_request::<DocumentDiagnosticReport>(
                    "textDocument/diagnostic",
                    json!({ "textDocument": { "uri": uri } }),
                ),
            )
            .await;
            return match pulled {
                Ok(Ok(DocumentDiagnosticReport::Full { items })) => {
                    Some(self.convert(path, &text, &items))
                }
                Ok(Ok(DocumentDiagnosticReport::Unchanged {})) => {
                    let items = self
                        .shared
                        .diagnostics
                        .lock()
                        .get(&uri)
                        .map(|published| published.diagnostics.clone())
                        .unwrap_or_default();
                    Some(self.convert(path, &text, &items))
                }
                Ok(Err(error)) => {
                    tracing::debug!(server = %self.name, %error, "diagnostic pull failed");
                    None
                }
                Err(_) => None,
            };
        }
        let mut publishes = self.shared.publishes.subscribe();
        loop {
            let settle_at = {
                let diagnostics = self.shared.diagnostics.lock();
                match diagnostics.get(&uri) {
                    Some(latest) if latest.sequence > synced_at => match latest.version {
                        Some(latest_version) if latest_version == version => {
                            return Some(self.convert(path, &text, &latest.diagnostics));
                        }
                        Some(_) => None,
                        None if latest.at.elapsed() >= DIAGNOSTICS_SETTLE => {
                            return Some(self.convert(path, &text, &latest.diagnostics));
                        }
                        None => Some(tokio::time::Instant::from_std(
                            latest.at + DIAGNOSTICS_SETTLE,
                        )),
                    },
                    Some(_) | None => None,
                }
            };
            let wake = settle_at.map_or(deadline, |settle| settle.min(deadline));
            tokio::select! {
                changed = publishes.changed() => {
                    if changed.is_err() {
                        return None;
                    }
                }
                () = tokio::time::sleep_until(wake) => {
                    if tokio::time::Instant::now() >= deadline {
                        return None;
                    }
                }
            }
        }
    }

    /// Every stored diagnostic of every document.
    pub(crate) fn all_diagnostics(&self) -> Vec<(PathBuf, Vec<Diagnostic>)> {
        self.shared
            .diagnostics
            .lock()
            .iter()
            .filter_map(|(uri, published)| {
                Some((uri.to_file_path().ok()?, published.diagnostics.clone()))
            })
            .collect()
    }

    /// The stored diagnostics of `path` that touch 0-based `line`.
    pub(crate) async fn line_diagnostics(&self, path: &Path, line: u32) -> Vec<Diagnostic> {
        let Some(uri) = self
            .documents
            .lock()
            .await
            .get(path)
            .map(|document| document.uri.clone())
        else {
            return Vec::new();
        };
        self.shared
            .diagnostics
            .lock()
            .get(&uri)
            .map(|published| {
                published
                    .diagnostics
                    .iter()
                    .filter(|diagnostic| {
                        diagnostic.range.start.line <= line && line <= diagnostic.range.end.line
                    })
                    .cloned()
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Typed diagnostics of `path` whose text is `text`.
    pub(crate) fn convert(
        &self,
        path: &Path,
        text: &str,
        items: &[Diagnostic],
    ) -> Vec<LspDiagnostic> {
        let text_lines = position::lines(text);
        items
            .iter()
            .map(|diagnostic| LspDiagnostic {
                path: path.to_owned(),
                span: position::span_from_lsp(&text_lines, diagnostic.range, self.encoding),
                severity: match diagnostic.severity {
                    Some(2) => LspSeverity::Warning,
                    Some(3) => LspSeverity::Information,
                    Some(4) => LspSeverity::Hint,
                    Some(_) | None => LspSeverity::Error,
                },
                message: strip_noise(&diagnostic.message),
                source: diagnostic.source.clone(),
                code: diagnostic.code.as_ref().map(|code| match code {
                    NumberOrString::Number(number) => number.to_string(),
                    NumberOrString::String(text) => text.clone(),
                }),
                server: self.name.clone(),
            })
            .collect()
    }

    /// Run `command` on the server and collect the edits it asks the client
    /// to apply meanwhile.
    pub(crate) async fn execute_command(
        &self,
        command: &crate::protocol::Command,
    ) -> Result<Vec<WorkspaceEdit>, LspError> {
        *self.shared.captured.lock() = Some(Vec::new());
        let ran = self
            .raw_request::<Value>(
                "workspace/executeCommand",
                json!({ "command": command.command, "arguments": command.arguments }),
            )
            .await;
        let captured = self.shared.captured.lock().take().unwrap_or_default();
        ran.map(|_| captured)
    }

    /// Ask the server to shut down, then kill it.
    pub(crate) async fn shutdown(&self) {
        let graceful = tokio::time::timeout(SHUTDOWN_TIMEOUT, async {
            if self
                .transport
                .request("shutdown", Value::Null, SHUTDOWN_TIMEOUT)
                .await
                .is_ok()
            {
                // The process is going away either way.
                let _ = self.transport.notify("exit", &Value::Null);
            }
        })
        .await;
        if graceful.is_err() {
            tracing::debug!(server = %self.name, "LSP shutdown timed out");
        }
        let child = self.child.lock().take();
        if let Some(mut child) = child {
            if let Err(error) = child.kill().await {
                tracing::debug!(server = %self.name, %error, "LSP kill failed");
            }
        }
    }
}

/// The `file://` URI of an absolute path.
pub(crate) fn file_uri(path: &Path) -> Result<Url, LspError> {
    Url::from_file_path(path).map_err(|()| LspError::Read {
        path: path.to_owned(),
        reason: "not an absolute path".to_owned(),
    })
}

/// Drop "for further information visit" lines and bare URLs (omp
/// `stripDiagnosticNoise`).
fn strip_noise(message: &str) -> String {
    message
        .lines()
        .filter(|line| {
            let trimmed = line.trim();
            !trimmed.starts_with("for further information visit")
                && !trimmed.starts_with("http://")
                && !trimmed.starts_with("https://")
        })
        .collect::<Vec<_>>()
        .join("\n")
        .trim()
        .to_owned()
}

fn client_capabilities() -> Value {
    json!({
        "general": { "positionEncodings": ["utf-8", "utf-16", "utf-32"] },
        "experimental": { "serverStatusNotification": true },
        "window": { "workDoneProgress": true, "showDocument": { "support": false } },
        "workspace": {
            "applyEdit": true,
            "configuration": true,
            "workspaceFolders": true,
            "symbol": {},
            "executeCommand": {},
            "didChangeConfiguration": {},
            "workspaceEdit": { "documentChanges": true, "resourceOperations": [] },
        },
        "textDocument": {
            "synchronization": { "didSave": true },
            "hover": { "contentFormat": ["markdown", "plaintext"] },
            "definition": { "linkSupport": true },
            "typeDefinition": { "linkSupport": true },
            "implementation": { "linkSupport": true },
            "references": {},
            "documentSymbol": { "hierarchicalDocumentSymbolSupport": true },
            "rename": {},
            "codeAction": {
                "codeActionLiteralSupport": {
                    "codeActionKind": {
                        "valueSet": [
                            "", "quickfix", "refactor", "refactor.extract", "refactor.inline",
                            "refactor.rewrite", "source", "source.organizeImports", "source.fixAll",
                        ],
                    },
                },
                "isPreferredSupport": true,
                "resolveSupport": { "properties": ["edit"] },
            },
            "publishDiagnostics": { "versionSupport": true },
            "diagnostic": {},
        },
    })
}
