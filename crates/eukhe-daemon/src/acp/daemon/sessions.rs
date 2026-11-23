//! The connection's sessions: `session/new`, `session/load` and
//! `session/resume` open and attach a daemon session whose durable id is
//! the ACP session id; `session/list` and `session/delete` read and remove
//! saved sessions; `authenticate` checks for a usable model. One session is
//! hosted at a time; close and EOF release it (`stop.rs`).

use std::path::{Path, PathBuf};
use std::sync::Arc;

use eukhe_types::daemon::{DaemonCommand, DaemonSessionLifecycle, DetachReason};
use serde::Deserialize;
use serde_json::{json, Map, Value};
use tokio::sync::Mutex;

use super::error::DaemonCommandError;
use super::{
    fetch_rlm_children, jsonrpc, meta, permission, producer, types, wire_events, DaemonAcpOptions,
    DaemonAcpState, DaemonLink, HostedSession, SessionStorage,
};
use crate::acp::auth::{self, TerminalLogin};
use crate::acp::meta::{EukheEventPhase, EukheSessionMeta};
use crate::acp::producer::UpdateProducer;
use crate::acp::replay;
use crate::acp::wire_config::{
    fetch_available_models, fetch_connection_state, picker_options_from_state, HostedConfig,
};
use crate::acp::wire_events::WireMappingState;

/// What every session of this connection shares.
pub(crate) struct Connection {
    pub(crate) options: DaemonAcpOptions,
    /// The owner of the MCP servers this connection installs.
    pub(crate) mcp_owner_id: String,
}

/// A saved session to open.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SavedSessionTarget {
    pub session_path: String,
    pub cwd: PathBuf,
}

/// Which request starts a session.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum StartKind {
    New,
    Load,
    Resume,
}

impl StartKind {
    pub(super) fn of_method(method: &str) -> Option<StartKind> {
        match method {
            "session/new" => Some(StartKind::New),
            "session/load" => Some(StartKind::Load),
            "session/resume" => Some(StartKind::Resume),
            _ => None,
        }
    }
}

/// The daemon session a start opens.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Target {
    /// A new saved session.
    Fresh {
        cwd: PathBuf,
    },
    /// A new session that ends with the connection (`--no-session`).
    Memory {
        cwd: PathBuf,
    },
    Saved(SavedSessionTarget),
}

impl Target {
    fn cwd(&self) -> &Path {
        match self {
            Target::Fresh { cwd } | Target::Memory { cwd } => cwd,
            Target::Saved(saved) => &saved.cwd,
        }
    }
}

/// The daemon session this connection attached.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DaemonSession {
    pub(crate) active_session_id: String,
    /// The durable id: the ACP session id.
    pub(crate) session_id: String,
    pub(crate) session_file: Option<String>,
    pub(crate) lifecycle: DaemonSessionLifecycle,
    pub(crate) cwd: PathBuf,
}

/// Why a session start failed.
#[derive(Debug, thiserror::Error)]
enum StartError {
    #[error("{0}")]
    InvalidParams(String),
    #[error("Unknown session: {0}")]
    NotFound(String),
    #[error("no model provider is logged in")]
    AuthRequired,
    #[error("eukhe ACP mode hosts one session per connection; start another eukhe process for a second session")]
    OneSession,
    #[error(transparent)]
    Daemon(#[from] DaemonCommandError),
    #[error("{0}")]
    Mcp(String),
}

impl StartError {
    fn response(&self, id: &Value, terminal: TerminalLogin) -> Value {
        match self {
            StartError::InvalidParams(reason) => jsonrpc::error_response(
                id,
                jsonrpc::INVALID_PARAMS,
                "Invalid params",
                Some(&json!({ "reason": reason })),
            ),
            StartError::NotFound(session_id) => jsonrpc::session_not_found(id, session_id),
            StartError::AuthRequired => auth::auth_required(id, terminal),
            StartError::OneSession | StartError::Daemon(_) | StartError::Mcp(_) => {
                crate::acp::internal_error(id, &self.to_string())
            }
        }
    }
}

/// `session/new`, `session/load`, `session/resume`: open the session, check
/// that a model can answer, install its MCP servers and pickers, host it,
/// answer (a load replays the history first).
pub(super) async fn handle_session_start(
    kind: StartKind,
    id: Value,
    params: Value,
    link: &Arc<DaemonLink>,
    state: &Arc<Mutex<DaemonAcpState>>,
    connection: &Connection,
    tx: producer::FrameSink,
) {
    let params = types::NewSessionParams::parse(&params);
    let (first, terminal) = {
        let mut guard = state.lock().await;
        if guard.session.is_some()
            || guard.session_new_in_flight
            || guard.session_close_done.is_some()
        {
            let _ = tx.send(StartError::OneSession.response(&id, guard.terminal_login));
            return;
        }
        guard.session_new_in_flight = true;
        let first = match kind {
            StartKind::New => guard.first_session.take(),
            StartKind::Load | StartKind::Resume => None,
        };
        (first, guard.terminal_login)
    };
    let outcome = start(
        kind,
        &params,
        first.clone(),
        link,
        state,
        connection,
        &id,
        &tx,
    )
    .await;
    if let Err(error) = outcome {
        let mut guard = state.lock().await;
        guard.session_new_in_flight = false;
        if guard.first_session.is_none() {
            guard.first_session = first;
        }
        drop(guard);
        let _ = tx.send(error.response(&id, terminal));
    }
}

#[allow(clippy::too_many_arguments)] // The handler's whole context, passed once.
async fn start(
    kind: StartKind,
    params: &types::NewSessionParams,
    first: Option<SavedSessionTarget>,
    link: &Arc<DaemonLink>,
    state: &Arc<Mutex<DaemonAcpState>>,
    connection: &Connection,
    id: &Value,
    tx: &producer::FrameSink,
) -> Result<(), StartError> {
    let target = target(kind, params, first, link, connection).await?;
    let resolved = crate::acp::mcp::resolve_acp_mcp_servers(&params.mcp_servers, target.cwd())
        .map_err(|reason| StartError::InvalidParams(reason.to_string()))?;
    crate::acp::mcp::acp_mcp_tool_names(&resolved)
        .map_err(|details| StartError::Mcp(details.to_string()))?;
    let daemon = open_session(link, connection, &target).await?;
    let prepared = prepare(kind, params, &daemon, &resolved, link, connection).await;
    let prepared = match prepared {
        Ok(prepared) => prepared,
        Err(error) => {
            release(link, connection, &daemon).await;
            return Err(error);
        }
    };
    host(kind, params, daemon, prepared, link, state, id, tx).await;
    Ok(())
}

/// The daemon session `kind` opens: a load or resume finds its saved
/// session; the first `session/new` opens the CLI's selection; every other
/// one a new session.
async fn target(
    kind: StartKind,
    params: &types::NewSessionParams,
    first: Option<SavedSessionTarget>,
    link: &DaemonLink,
    connection: &Connection,
) -> Result<Target, StartError> {
    let cwd = connection.options.cwd.clone();
    match kind {
        StartKind::New => Ok(match (first, connection.options.storage) {
            (Some(saved), _) => Target::Saved(saved),
            (None, SessionStorage::Saved) => Target::Fresh { cwd },
            (None, SessionStorage::Memory) => Target::Memory { cwd },
        }),
        StartKind::Load | StartKind::Resume => {
            let session_id = params
                .session_id
                .clone()
                .ok_or_else(|| StartError::InvalidParams("sessionId is required".to_string()))?;
            let row = saved_sessions(link, connection, None)
                .await?
                .into_iter()
                .find(|row| row.id == session_id)
                .ok_or(StartError::NotFound(session_id))?;
            Ok(Target::Saved(SavedSessionTarget {
                session_path: row.path,
                cwd: PathBuf::from(row.cwd),
            }))
        }
    }
}

/// Create and attach the daemon session of `target`. A failed attach
/// releases the created session.
async fn open_session(
    link: &DaemonLink,
    connection: &Connection,
    target: &Target,
) -> Result<DaemonSession, DaemonCommandError> {
    let (session_path, lifecycle) = match target {
        Target::Fresh { .. } => (None, DaemonSessionLifecycle::Resident),
        Target::Memory { .. } => (None, DaemonSessionLifecycle::ClientOwned),
        Target::Saved(saved) => (
            Some(saved.session_path.clone()),
            DaemonSessionLifecycle::Resident,
        ),
    };
    let mut config = connection
        .options
        .create_config
        .as_object()
        .cloned()
        .unwrap_or_default();
    config.insert("cwd".to_string(), json!(target.cwd().display().to_string()));
    let created = link
        .request(DaemonCommand::Create {
            id: None,
            session_path,
            continue_recent: None,
            no_session: matches!(target, Target::Memory { .. }).then_some(true),
            name: None,
            config: Some(Value::Object(config)),
            runtime_metadata: None,
            lifecycle: Some(lifecycle),
            env: None,
            launch_env: None,
            rest: Map::default(),
        })
        .await?;
    if !created.success {
        return Err(DaemonCommandError::Refused {
            message: created.error,
        });
    }
    let data = created.data.unwrap_or(Value::Null);
    let field = |key: &'static str| {
        data.get(key)
            .and_then(Value::as_str)
            .filter(|value| !value.is_empty())
            .map(str::to_string)
    };
    let session = DaemonSession {
        active_session_id: field("activeSessionId")
            .ok_or(DaemonCommandError::MissingField("activeSessionId"))?,
        session_id: field("sessionId").ok_or(DaemonCommandError::MissingField("sessionId"))?,
        session_file: field("sessionFile"),
        lifecycle,
        cwd: target.cwd().to_path_buf(),
    };
    let attached = link
        .request_ok(DaemonCommand::Attach {
            id: None,
            active_session_id: session.active_session_id.clone(),
            client_id: None,
            client_kind: None,
            capabilities: Some(
                crate::protocol::default_client_capabilities()
                    .into_iter()
                    .chain([permission::CAPABILITY.to_string()])
                    .collect(),
            ),
            resume_cursor: None,
            recovery_config: None,
            env: None,
            launch_env: None,
            rest: Map::default(),
        })
        .await;
    if let Err(error) = attached {
        release(link, connection, &session).await;
        return Err(error);
    }
    Ok(session)
}

/// What a session needs before it is hosted.
struct Prepared {
    config: Arc<HostedConfig>,
    children: Vec<Value>,
    history: Vec<Value>,
}

/// Check the model, read the pickers, install the MCP servers, read the
/// roster (and, for a load, the history). The caller releases the session
/// on failure.
async fn prepare(
    kind: StartKind,
    params: &types::NewSessionParams,
    daemon: &DaemonSession,
    resolved: &[eukhe_core::mcp::AcpMcpServerConfig],
    link: &Arc<DaemonLink>,
    connection: &Connection,
) -> Result<Prepared, StartError> {
    let _ = params;
    let state_value = fetch_connection_state(link, &daemon.active_session_id).await;
    if !has_model(state_value.as_ref())? {
        return Err(StartError::AuthRequired);
    }
    // Discovery failure degrades to an empty list (TS catches it).
    let models = fetch_available_models(link, &daemon.active_session_id)
        .await
        .unwrap_or_default();
    let published = picker_options_from_state(state_value.as_ref(), &models);
    let config = Arc::new(HostedConfig {
        queue: tokio::sync::Mutex::new(()),
        published: tokio::sync::Mutex::new(published),
        models: tokio::sync::Mutex::new(models),
    });
    if !resolved.is_empty() {
        replace_mcp_servers(
            link,
            &daemon.active_session_id,
            &connection.mcp_owner_id,
            resolved,
        )
        .await?;
    }
    let children = fetch_rlm_children(link, &daemon.active_session_id).await?;
    let history = match kind {
        StartKind::Load => history(link, &daemon.active_session_id).await?,
        StartKind::New | StartKind::Resume => Vec::new(),
    };
    Ok(Prepared {
        config,
        children,
        history,
    })
}

/// Whether the session resolved a model; an unreadable state fails the start.
fn has_model(state: Option<&Value>) -> Result<bool, StartError> {
    let state = state.ok_or(StartError::Daemon(DaemonCommandError::Refused {
        message: Some("the session's state could not be read".to_string()),
    }))?;
    Ok(!state.get("model").is_none_or(Value::is_null))
}

/// Host the prepared session and answer: the update producer opens after
/// the answer (a load's history goes out before it).
#[allow(clippy::too_many_arguments)] // The handler's whole context, passed once.
async fn host(
    kind: StartKind,
    params: &types::NewSessionParams,
    daemon: DaemonSession,
    prepared: Prepared,
    link: &Arc<DaemonLink>,
    state: &Arc<Mutex<DaemonAcpState>>,
    id: &Value,
    tx: &producer::FrameSink,
) {
    let acp_session_id = daemon.session_id.clone();
    let producer = UpdateProducer::new(acp_session_id.clone(), tx.clone());
    let mut mapping = WireMappingState::in_cwd(daemon.cwd.clone());
    let mut observed_children = std::collections::HashSet::new();
    for update in replay::replay_updates(&prepared.history, &daemon.cwd) {
        let _ = producer
            .publish(&update, 0, EukheEventPhase::Event, None)
            .await;
    }
    for child in prepared.children {
        let child_id = child.get("id").and_then(Value::as_str).unwrap_or_default();
        if !observed_children.insert(child_id.to_string()) {
            continue;
        }
        let event = json!({ "type": "rlm_child_update", "child": child });
        for update in wire_events::wire_updates(&event, &mut mapping) {
            let _ = producer
                .publish(&update, 0, EukheEventPhase::Event, None)
                .await;
        }
    }
    let mut result = json!({ "configOptions": *prepared.config.published.lock().await });
    if kind == StartKind::New {
        result["sessionId"] = json!(acp_session_id);
    }
    if let Some(requested) = params.cwd.as_deref().filter(|cwd| !cwd.is_empty()) {
        if !crate::acp::same_cwd(Path::new(requested), &daemon.cwd) {
            result["_meta"] = meta::eukhe_meta(&EukheSessionMeta {
                cwd: Some(meta::EukheCwdMeta {
                    requested: requested.to_string(),
                    actual: daemon.cwd.display().to_string(),
                }),
                ..Default::default()
            });
        }
    }
    let daemon_session_id = daemon.active_session_id.clone();
    // Installed before the answer leaves: a request right after it finds
    // the session.
    {
        let mut guard = state.lock().await;
        guard.session_new_in_flight = false;
        guard.session = Some(HostedSession::new(
            daemon,
            Arc::clone(&producer),
            prepared.config,
            mapping,
            observed_children,
        ));
    }
    match kind {
        StartKind::Load => {
            producer.commit_session_new_response().await;
            let _ = tx.send(jsonrpc::response(id, &result));
        }
        StartKind::New | StartKind::Resume => {
            let _ = tx.send(jsonrpc::response(id, &result));
            producer.commit_session_new_response().await;
        }
    }
    // In the start, before the next frame is read: a prompt's frames never
    // interleave with these.
    publish_available_commands(link, &daemon_session_id, &producer).await;
    publish_usage(link, &daemon_session_id, &producer).await;
}

/// The session's history rows (`get_messages`).
async fn history(link: &DaemonLink, session: &str) -> Result<Vec<Value>, DaemonCommandError> {
    let data = data(
        link,
        DaemonCommand::GetMessages {
            id: None,
            active_session_id: session.to_string(),
            rest: Map::default(),
        },
    )
    .await?;
    Ok(data
        .get("messages")
        .and_then(Value::as_array)
        .cloned()
        .unwrap_or_default())
}

/// One command's answer data.
async fn data(link: &DaemonLink, command: DaemonCommand) -> Result<Value, DaemonCommandError> {
    let response = link.request(command).await?;
    if !response.success {
        return Err(DaemonCommandError::Refused {
            message: response.error,
        });
    }
    Ok(response.data.unwrap_or(Value::Null))
}

pub(super) async fn replace_mcp_servers(
    link: &DaemonLink,
    daemon_session_id: &str,
    owner_id: &str,
    resolved: &[eukhe_core::mcp::AcpMcpServerConfig],
) -> Result<(), DaemonCommandError> {
    link.request_ok(DaemonCommand::ReplaceAcpMcpServers {
        id: None,
        active_session_id: daemon_session_id.to_string(),
        owner_id: owner_id.to_string(),
        servers: serde_json::to_value(resolved).map_err(DaemonCommandError::Encode)?,
        rest: Map::default(),
    })
    .await
}

/// Let go of a daemon session: its MCP servers go; a `--no-session` one
/// ends; a saved one never prompted is removed; any other is detached and
/// its idle worker released after the daemon's grace (it stays saved and
/// resumable by id). A failure is reported on stderr: nothing waits on it.
pub(super) async fn release(link: &DaemonLink, connection: &Connection, session: &DaemonSession) {
    let outcome = async {
        replace_mcp_servers(
            link,
            &session.active_session_id,
            &connection.mcp_owner_id,
            &[],
        )
        .await?;
        match session.lifecycle {
            DaemonSessionLifecycle::ClientOwned => {
                link.request_ok(DaemonCommand::CompleteOwnedSession {
                    id: None,
                    active_session_id: session.active_session_id.clone(),
                    rest: Map::default(),
                })
                .await
            }
            DaemonSessionLifecycle::Resident => match message_count(link, session).await? {
                0 => discard(link, session).await,
                _ => {
                    link.request_ok(DaemonCommand::Detach {
                        id: None,
                        active_session_id: Some(session.active_session_id.clone()),
                        reason: Some(DetachReason::Switch),
                        rest: Map::default(),
                    })
                    .await
                }
            },
        }
    }
    .await;
    if let Err(error) = outcome {
        eprintln!(
            "eukhe: releasing ACP session {} failed: {error}",
            session.session_id
        );
    }
}

async fn message_count(
    link: &DaemonLink,
    session: &DaemonSession,
) -> Result<u64, DaemonCommandError> {
    let state = data(
        link,
        DaemonCommand::GetState {
            id: None,
            active_session_id: session.active_session_id.clone(),
            rest: Map::default(),
        },
    )
    .await?;
    state
        .get("messageCount")
        .and_then(Value::as_u64)
        .ok_or(DaemonCommandError::MissingField("messageCount"))
}

/// Stop a saved session and delete its storage.
async fn discard(link: &DaemonLink, session: &DaemonSession) -> Result<(), DaemonCommandError> {
    link.request_ok(DaemonCommand::Kill {
        id: None,
        active_session_id: session.active_session_id.clone(),
        rest: Map::default(),
    })
    .await?;
    match session.session_file.as_ref() {
        Some(path) => delete_saved(link, path).await,
        None => Ok(()),
    }
}

async fn delete_saved(link: &DaemonLink, session_path: &str) -> Result<(), DaemonCommandError> {
    link.request_ok(DaemonCommand::DeleteSavedSession {
        id: None,
        active_session_id: None,
        session_path: session_path.to_string(),
        rest: Map::default(),
    })
    .await
}

/// One `list_saved_sessions` row.
#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct SavedRow {
    path: String,
    id: String,
    cwd: String,
    #[serde(default)]
    modified: Option<String>,
    #[serde(default)]
    name: Option<String>,
    #[serde(default)]
    first_message: Option<String>,
    #[serde(default)]
    rlm_depth: Option<u64>,
    #[serde(default)]
    parent_session_path: Option<String>,
}

#[derive(Debug, Deserialize)]
struct SavedList {
    sessions: Vec<SavedRow>,
}

/// The saved sessions of this connection's session dir: those of `cwd`,
/// else of every cwd.
async fn saved_sessions(
    link: &DaemonLink,
    connection: &Connection,
    cwd: Option<&str>,
) -> Result<Vec<SavedRow>, DaemonCommandError> {
    let data = data(
        link,
        DaemonCommand::ListSavedSessions {
            id: None,
            active_session_id: None,
            cwd: Some(cwd.map_or_else(
                || connection.options.cwd.display().to_string(),
                str::to_string,
            )),
            session_dir: connection
                .options
                .create_config
                .get("sessionDir")
                .and_then(Value::as_str)
                .map(str::to_string),
            scope: cwd.map_or(Value::Null, |_| json!("current")),
            rest: Map::default(),
        },
    )
    .await?;
    SavedList::deserialize(data)
        .map(|list| list.sessions)
        .map_err(DaemonCommandError::Decode)
}

/// `session/list`: the saved top-level sessions (of `cwd` when given).
pub(super) async fn handle_session_list(
    id: Value,
    params: Value,
    link: &DaemonLink,
    connection: &Connection,
    tx: producer::FrameSink,
) {
    let cwd = params.get("cwd").and_then(Value::as_str);
    let reply = match saved_sessions(link, connection, cwd).await {
        Ok(rows) => jsonrpc::response(
            &id,
            &json!({ "sessions": rows
                .into_iter()
                .filter(|row| row.rlm_depth.unwrap_or(0) == 0 && row.parent_session_path.is_none())
                .map(session_info)
                .collect::<Vec<_>>() }),
        ),
        Err(error) => crate::acp::internal_error(&id, &error.to_string()),
    };
    let _ = tx.send(reply);
}

/// A row as ACP `SessionInfo`: its name, else its first message, titles it.
fn session_info(row: SavedRow) -> Value {
    let title = [row.name, row.first_message]
        .into_iter()
        .flatten()
        .find(|text| !text.trim().is_empty());
    let mut info = json!({ "sessionId": row.id, "cwd": row.cwd });
    if let Some(title) = title {
        info["title"] = json!(title);
    }
    if let Some(modified) = row.modified.filter(|modified| !modified.is_empty()) {
        info["updatedAt"] = json!(modified);
    }
    info
}

/// `session/delete`: remove a saved session. The hosted one is let go
/// first (refused while a prompt runs); an unknown id is not found.
pub(super) async fn handle_session_delete(
    id: Value,
    params: Value,
    link: &DaemonLink,
    state: &Arc<Mutex<DaemonAcpState>>,
    connection: &Connection,
    tx: producer::FrameSink,
) {
    let Some(session_id) = params.get("sessionId").and_then(Value::as_str) else {
        let _ = tx.send(
            StartError::InvalidParams("sessionId is required".to_string())
                .response(&id, TerminalLogin::Unsupported),
        );
        return;
    };
    let hosted = {
        let mut guard = state.lock().await;
        match guard.session.as_ref() {
            Some(hosted) if hosted.acp_session_id == session_id => {
                if hosted.turn.is_some() || hosted.cancelling || guard.session_close_done.is_some()
                {
                    drop(guard);
                    let _ = tx.send(crate::acp::internal_error(
                        &id,
                        &format!("ACP session is busy: {session_id}; close it first"),
                    ));
                    return;
                }
                guard.session.take()
            }
            Some(_) | None => None,
        }
    };
    let outcome = match hosted {
        Some(hosted) => {
            hosted.producer.close().await;
            let daemon = hosted.daemon_session();
            let _ = replace_mcp_servers(
                link,
                &daemon.active_session_id,
                &connection.mcp_owner_id,
                &[],
            )
            .await;
            discard(link, &daemon).await.map(|()| true)
        }
        None => match saved_sessions(link, connection, None).await {
            Ok(rows) => match rows.into_iter().find(|row| row.id == session_id) {
                Some(row) => delete_saved(link, &row.path).await.map(|()| true),
                None => Ok(false),
            },
            Err(error) => Err(error),
        },
    };
    let reply = match outcome {
        Ok(true) => jsonrpc::response(&id, &json!({})),
        Ok(false) => jsonrpc::session_not_found(&id, session_id),
        Err(error) => crate::acp::internal_error(&id, &error.to_string()),
    };
    let _ = tx.send(reply);
}

/// `authenticate`: the user logged in outside the client; a probe session
/// tells whether a model answers now.
pub(super) async fn handle_authenticate(
    id: Value,
    params: Value,
    link: &Arc<DaemonLink>,
    state: &Arc<Mutex<DaemonAcpState>>,
    connection: &Connection,
    tx: producer::FrameSink,
) {
    let terminal = state.lock().await.terminal_login;
    let method = params
        .get("methodId")
        .and_then(Value::as_str)
        .unwrap_or_default();
    if !auth::is_method(method) {
        let _ = tx.send(
            StartError::InvalidParams(format!("Unknown auth method: {method}"))
                .response(&id, terminal),
        );
        return;
    }
    let probe = Target::Memory {
        cwd: connection.options.cwd.clone(),
    };
    let reply = match open_session(link, connection, &probe).await {
        Ok(session) => {
            let state_value = fetch_connection_state(link, &session.active_session_id).await;
            release(link, connection, &session).await;
            match has_model(state_value.as_ref()) {
                Ok(true) => jsonrpc::response(&id, &json!({})),
                Ok(false) => auth::auth_required(&id, terminal),
                Err(error) => error.response(&id, terminal),
            }
        }
        Err(error) => crate::acp::internal_error(&id, &error.to_string()),
    };
    let _ = tx.send(reply);
}

/// Publish the commands a prompt may start with: `/compact`, the prompt
/// templates and the skills.
async fn publish_available_commands(link: &DaemonLink, session: &str, producer: &UpdateProducer) {
    let Ok(data) = data(
        link,
        DaemonCommand::GetCommands {
            id: None,
            active_session_id: session.to_string(),
            rest: Map::default(),
        },
    )
    .await
    else {
        return;
    };
    let compact = types::AvailableCommand {
        name: "compact".to_string(),
        description: "Summarize the conversation to free context".to_string(),
        input: Some(types::CommandInput {
            hint: "instructions for the summary".to_string(),
        }),
    };
    let commands = std::iter::once(compact)
        .chain(
            data.get("commands")
                .and_then(Value::as_array)
                .into_iter()
                .flatten()
                .filter_map(available_command),
        )
        .collect();
    let _ = producer
        .publish(
            &types::AcpSessionUpdate::AvailableCommandsUpdate {
                available_commands: commands,
            },
            0,
            EukheEventPhase::Event,
            None,
        )
        .await;
}

/// One `get_commands` entry (a prompt template or `skill:<name>`).
fn available_command(command: &Value) -> Option<types::AvailableCommand> {
    let name = command.get("name").and_then(Value::as_str)?;
    Some(types::AvailableCommand {
        name: name.to_string(),
        description: command
            .get("description")
            .and_then(Value::as_str)
            .unwrap_or(name)
            .to_string(),
        input: command
            .get("argumentHint")
            .and_then(Value::as_str)
            .map(|hint| types::CommandInput {
                hint: hint.to_string(),
            }),
    })
}

/// Publish the context window in use and the cost so far
/// (`get_session_stats`); nothing without a model context window.
pub(super) async fn publish_usage(link: &DaemonLink, session: &str, producer: &UpdateProducer) {
    let Ok(stats) = data(
        link,
        DaemonCommand::GetSessionStats {
            id: None,
            active_session_id: session.to_string(),
            rest: Map::default(),
        },
    )
    .await
    else {
        return;
    };
    let usage = &stats["contextUsage"];
    let (Some(used), Some(size)) = (usage["tokens"].as_u64(), usage["contextWindow"].as_u64())
    else {
        return;
    };
    let _ = producer
        .publish(
            &types::AcpSessionUpdate::UsageUpdate {
                used,
                size,
                cost: stats["cost"].as_f64().map(|amount| types::UsageCost {
                    amount,
                    currency: "USD",
                }),
            },
            producer.active_prompt_turn().await,
            EukheEventPhase::Event,
            None,
        )
        .await;
}
