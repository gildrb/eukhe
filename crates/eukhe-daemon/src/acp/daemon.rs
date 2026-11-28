//! The daemon-attached ACP transport: the ACP JSON-RPC surface served over
//! daemon sessions (TS `runAcpModeWithConnection(DaemonAgentConnection)`).
//!
//! `session/new`, `session/load` and `session/resume` open and attach a
//! daemon session (`sessions.rs`), admit its MCP servers through the
//! `replace_acp_mcp_servers` wire command, and every prompt runs
//! `prompt_and_wait` while the streamed session events fan out as ACP
//! updates. The turn settlement (response boundary, completion envelope
//! with the live outstanding-subagent count, terminal frame after the RLM
//! family settles, stop reason) mirrors the TS captures, and the stop
//! sequence cancels the outstanding children (TS #1612). Each turn ends
//! with `_eukhe/run_report` (`run_report.rs`) before its response; the
//! `_eukhe/` requests run in `extensions.rs`.
//! The daemon worker's `loop_update` session events
//! surface through the wire mapping (`wire_events.rs`), and the autonomous
//! accounting rides the
//! `wait_for_headless_completion` response into the completion envelope
//! and the stop reason (TS `waitForHeadlessCompletion` + `acpStopReason`).
//!
//! The model and effort pickers (TS #2455) ride the worker's own wire
//! commands: `get_connection_state` for the live model/level,
//! `get_available_models` for discovery, `set_model` /
//! `set_thinking_level` for the applied selection.
//!
//! The attach advertises `editor_permission`: before an irreversible
//! effect runs the daemon sends an `editor_permission` frame, which
//! `permission.rs` turns into the editor's `session/request_permission`
//! (spec I12).

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use eukhe_types::daemon::{
    DaemonCommand, DaemonCommandEnvelope, DaemonCommandFrameType, DaemonErrorInfo,
    DaemonProtocolInfo, DaemonResponse, DaemonSessionLifecycle, DAEMON_PROTOCOL_NAME,
    DAEMON_PROTOCOL_VERSION,
};
use serde_json::{json, Map, Value};
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use tokio::sync::{mpsc, oneshot, Mutex};

use super::auth::{self, TerminalLogin};
use super::jsonrpc::{self, Incoming};
use super::meta::{self, EukheEventPhase, EukheOutcome, EukheSessionMeta};
use super::permission::{self, EditorRequests};
use super::producer::{self, UpdateProducer};
use super::types;
use super::wire_config::{handle_set_config_option, refresh_wire_config, HostedConfig};
use super::wire_events::{self, WireMappingState};

pub(super) mod error;
mod extensions;
mod run_report;
mod sessions;
mod stop;

use error::{AcpRefusal, DaemonCommandError, DaemonLinkError};
pub use sessions::SavedSessionTarget;
use sessions::{Connection, DaemonSession, StartKind};

use stop::{cancel_order, handle_session_close, run_cancel_stop, teardown, wait_for_session_close};

/// Response timeout for session-scoped commands.
const REQUEST_TIMEOUT: std::time::Duration = std::time::Duration::from_secs(30);

/// One inbound supervisor frame, classified by the reader.
enum LinkFrame {
    Event(Value),
    Response(DaemonResponse),
    /// The daemon-global heartbeat-catalog broadcast the supervisor
    /// re-broadcasts to every client (`heartbeats_changed`).
    HeartbeatsChanged,
    /// The daemon asks the editor before an irreversible effect runs
    /// (`editor_permission`, unsequenced).
    EditorPermission(Value),
}

/// A client connection to the supervisor socket: JSONL command envelopes
/// out, responses matched by id, session events forwarded raw.
pub(crate) struct DaemonLink {
    writer: mpsc::UnboundedSender<String>,
    pending: Arc<std::sync::Mutex<HashMap<String, oneshot::Sender<DaemonResponse>>>>,
    /// Set once the frame channel ends (the socket closed and every
    /// frame the reader read is delivered): every new request fails
    /// fast instead of waiting for a response no one will send.
    closed: Arc<std::sync::atomic::AtomicBool>,
    frames: Mutex<mpsc::UnboundedReceiver<LinkFrame>>,
    protocol_version: u64,
    next_request_id: std::sync::atomic::AtomicU64,
}

impl DaemonLink {
    /// Connect and complete the `daemon_hello` handshake.
    async fn connect(socket_path: &Path) -> Result<Self, DaemonLinkError> {
        let stream = tokio::time::timeout(
            std::time::Duration::from_secs(3),
            eukhe_types::platform::transport::connect_transport(
                socket_path,
                eukhe_bend::rules::server_peer::PEER_RULES,
            ),
        )
        .await
        .map_err(|_| DaemonLinkError::ConnectTimeout)?
        .map_err(DaemonLinkError::Connect)?;
        let (reader_half, writer_half) = stream.split();
        let (line_tx, mut line_rx) = mpsc::unbounded_channel::<String>();
        let (frame_tx, frame_rx) = mpsc::unbounded_channel::<LinkFrame>();
        let (hello_tx, hello_rx) = oneshot::channel::<Value>();
        let pending: Arc<std::sync::Mutex<HashMap<String, oneshot::Sender<DaemonResponse>>>> =
            Arc::new(std::sync::Mutex::new(HashMap::new()));
        let closed: Arc<std::sync::atomic::AtomicBool> =
            Arc::new(std::sync::atomic::AtomicBool::new(false));

        tokio::spawn(async move {
            let mut writer = writer_half;
            while let Some(line) = line_rx.recv().await {
                let mut payload = line.into_bytes();
                payload.push(b'\n');
                if writer.write_all(&payload).await.is_err() {
                    break;
                }
            }
            let _ = writer.shutdown().await;
        });
        // The reader only classifies frames; the consumer loop below owns
        // the ordering: every session event observed before a response on
        // the wire is published before that response resolves its caller,
        // so a turn's chunks always precede its boundary frames.
        tokio::spawn(async move {
            let mut reader = BufReader::new(reader_half);
            let mut line = String::new();
            let mut hello_tx = Some(hello_tx);
            loop {
                line.clear();
                match reader.read_line(&mut line).await {
                    Ok(0) | Err(_) => break,
                    Ok(_) => {}
                }
                let Ok(value) = serde_json::from_str::<Value>(line.trim()) else {
                    continue;
                };
                match value
                    .get("type")
                    .and_then(Value::as_str)
                    .unwrap_or_default()
                {
                    "daemon_hello" => {
                        if let Some(tx) = hello_tx.take() {
                            let _ = tx.send(value);
                        }
                    }
                    "response" => {
                        let Ok(response) = serde_json::from_value::<DaemonResponse>(value) else {
                            continue;
                        };
                        let _ = frame_tx.send(LinkFrame::Response(response));
                    }
                    "session_event" => {
                        let _ = frame_tx.send(LinkFrame::Event(value));
                    }
                    "heartbeats_changed" => {
                        let _ = frame_tx.send(LinkFrame::HeartbeatsChanged);
                    }
                    permission::FRAME => {
                        let _ = frame_tx.send(LinkFrame::EditorPermission(value));
                    }
                    _ => {}
                }
            }
        });

        let hello = tokio::time::timeout(std::time::Duration::from_secs(3), hello_rx)
            .await
            .map_err(|_| DaemonLinkError::HandshakeTimeout)?
            .map_err(|_| DaemonLinkError::HandshakeClosed)?;
        let protocol = hello
            .get("protocol")
            .cloned()
            .and_then(|p| serde_json::from_value::<DaemonProtocolInfo>(p).ok())
            .unwrap_or_else(|| DaemonProtocolInfo {
                name: DAEMON_PROTOCOL_NAME.to_string(),
                version: DAEMON_PROTOCOL_VERSION,
            });
        let version = protocol.version.min(DAEMON_PROTOCOL_VERSION);
        Ok(DaemonLink {
            writer: line_tx,
            pending,
            closed,
            frames: Mutex::new(frame_rx),
            protocol_version: version,
            next_request_id: std::sync::atomic::AtomicU64::new(0),
        })
    }

    /// Send one command envelope and wait for the matching response
    /// under the session-scoped response timeout.
    pub(crate) async fn request(
        &self,
        command: DaemonCommand,
    ) -> Result<DaemonResponse, DaemonLinkError> {
        self.exchange(command, Some(REQUEST_TIMEOUT)).await
    }

    pub(crate) async fn request_ok(
        &self,
        command: DaemonCommand,
    ) -> Result<(), DaemonCommandError> {
        let response = self.request(command).await?;
        if !response.success {
            return Err(DaemonCommandError::Refused {
                message: response.error,
            });
        }
        Ok(())
    }

    /// Send one command envelope with no fixed cap: the response or the
    /// link close ends the wait (turn-long commands — declared
    /// divergence, TS caps them at 24 h; the link-close signal is the
    /// liveness bound here, not a timer).
    async fn request_until_close(
        &self,
        command: DaemonCommand,
    ) -> Result<DaemonResponse, DaemonLinkError> {
        self.exchange(command, None).await
    }

    /// One exchange: register the response slot, send the envelope, and
    /// wait for the answer.
    async fn exchange(
        &self,
        command: DaemonCommand,
        timeout: Option<std::time::Duration>,
    ) -> Result<DaemonResponse, DaemonLinkError> {
        use std::sync::atomic::Ordering;
        let id = format!(
            "acp-{}",
            self.next_request_id.fetch_add(1, Ordering::SeqCst) + 1
        );
        let envelope = DaemonCommandEnvelope {
            frame_type: DaemonCommandFrameType::Command,
            id: id.clone(),
            protocol: DaemonProtocolInfo {
                name: DAEMON_PROTOCOL_NAME.to_string(),
                version: self.protocol_version,
            },
            client_id: Some(format!("acp:{}", std::process::id())),
            command,
        };
        let line = serde_json::to_string(&envelope).map_err(DaemonLinkError::Encode)?;
        let (tx, rx) = oneshot::channel::<DaemonResponse>();
        self.pending.lock().unwrap().insert(id.clone(), tx);
        // A request that races the close loses either way: the flag
        // fails it here, or the pending clear already dropped its
        // sender. The flag is stored before the clear, so no request
        // parks unnoticed.
        if self.closed.load(Ordering::SeqCst) {
            self.pending.lock().unwrap().remove(&id);
            return Err(DaemonLinkError::Closed);
        }
        if self.writer.send(line).is_err() {
            // A closed writer leaves the pending slot behind otherwise; a
            // link that never answers again would grow one entry per
            // request.
            self.pending.lock().unwrap().remove(&id);
            return Err(DaemonLinkError::Closed);
        }
        match timeout {
            Some(timeout) => tokio::time::timeout(timeout, rx).await.map_err(|_| {
                self.pending.lock().unwrap().remove(&id);
                DaemonLinkError::ResponseTimeout
            })?,
            None => rx.await,
        }
        .map_err(|_| DaemonLinkError::ClosedMidRequest)
    }
}

/// Everything the daemon-attached mode needs from the composition.
#[derive(Clone)]
pub struct DaemonAcpOptions {
    pub socket_path: PathBuf,
    pub product_version: String,
    /// The process cwd: a new session runs in it.
    pub cwd: PathBuf,
    /// The create config of every session (the CLI session flags); each
    /// create sets its `cwd`.
    pub create_config: Value,
    /// Where a `session/new` session lives.
    pub storage: SessionStorage,
    /// The saved session the first `session/new` opens (`--resume`,
    /// `--continue`, `--fork`); later ones start new.
    pub first_session: Option<SavedSessionTarget>,
}

/// Where a `session/new` session lives.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SessionStorage {
    /// Saved in the session dir, resident in the daemon.
    Saved,
    /// In memory, ended with the connection (`--no-session`).
    Memory,
}

/// The hosted daemon session: the ACP identity, the daemon routing id,
/// the update producer, and the stop state.
pub(crate) struct HostedSession {
    /// The session's durable id.
    pub(crate) acp_session_id: String,
    pub(crate) daemon_active_session_id: String,
    session_file: Option<String>,
    lifecycle: DaemonSessionLifecycle,
    cwd: PathBuf,
    pub(crate) producer: Arc<UpdateProducer>,
    /// The picker state (TS `AcpSessionEntry`'s configOptions/models) and
    /// the serialized config queue (`configTask`).
    pub(crate) config: Arc<HostedConfig>,
    cancelling: bool,
    stop_failure: Option<Arc<DaemonCommandError>>,
    input_pause_key: Option<String>,
    input_pause_id: Option<String>,
    cancel_task: Option<tokio::sync::watch::Receiver<bool>>,
    /// The running prompt turn; one at a time. A cancelled turn keeps
    /// the slot until its cancel stop finishes.
    turn: Option<ActiveTurn>,
    /// The newest assistant stop reason observed on the event stream,
    /// cleared when a prompt turn is admitted so a turn never reads a
    /// previous turn's stop reason (read after the settlement for the
    /// stop-reason response).
    assistant_stop_reason: Option<eukhe_types::ai::StopReason>,
    /// The text of the newest assistant message, cleared like the stop
    /// reason: the turn's answer in its run report.
    turn_answer: Option<String>,
    /// The event mapping state lives and dies with the session, like TS.
    mapping: WireMappingState,
    observed_children: std::collections::HashSet<String>,
    /// The editor answered `session/request_permission` as an unknown
    /// method: it is not asked again in this session.
    pub(crate) editor_unsupported: bool,
}

impl HostedSession {
    fn new(
        daemon: DaemonSession,
        producer: Arc<UpdateProducer>,
        config: Arc<HostedConfig>,
        mapping: WireMappingState,
        observed_children: std::collections::HashSet<String>,
    ) -> HostedSession {
        HostedSession {
            acp_session_id: daemon.session_id,
            daemon_active_session_id: daemon.active_session_id,
            session_file: daemon.session_file,
            lifecycle: daemon.lifecycle,
            cwd: daemon.cwd,
            producer,
            config,
            cancelling: false,
            stop_failure: None,
            input_pause_key: None,
            input_pause_id: None,
            cancel_task: None,
            turn: None,
            assistant_stop_reason: None,
            turn_answer: None,
            mapping,
            observed_children,
            editor_unsupported: false,
        }
    }

    /// The daemon session this hosts.
    fn daemon_session(&self) -> DaemonSession {
        DaemonSession {
            active_session_id: self.daemon_active_session_id.clone(),
            session_id: self.acp_session_id.clone(),
            session_file: self.session_file.clone(),
            lifecycle: self.lifecycle,
            cwd: self.cwd.clone(),
        }
    }
}

struct ActiveTurn {
    /// TS `admissionId`; the stop sequence cancels the admission by it.
    admission_id: String,
    /// TS the per-turn `AbortController`.
    cancelled: bool,
}

/// The ACP transport state: one hosted session at most.
#[derive(Default)]
pub(crate) struct DaemonAcpState {
    pub(crate) session: Option<HostedSession>,
    pub(crate) session_new_in_flight: bool,
    pub(crate) session_close_done: Option<tokio::sync::watch::Receiver<bool>>,
    /// The CLI's selection, until the first `session/new` opens it.
    first_session: Option<SavedSessionTarget>,
    /// The client's terminal login capability (`initialize`).
    terminal_login: TerminalLogin,
    /// Fires when a cancel or a close takes the running prompt's turn: a
    /// prompt holding for the session's background work answers at once
    /// instead of after that work ends.
    pub(crate) turn_lost: Arc<tokio::sync::Notify>,
}

/// Serve the daemon-attached ACP mode until stdin closes. The caller
/// guarantees the socket answers (the composition spawns a supervisor
/// when none is listening).
///
/// # Errors
///
/// Returns an error, before any ACP frame is written, when the daemon
/// socket connect, the startup create, or its attach fails; a daemon that
/// drops mid-session fails the hosted session's requests instead, exactly
/// like the TS daemon connection.
///
/// # Panics
///
/// The frame-consumer task panics when the link's pending-response map
/// lock is poisoned (a holder panicked while holding it).
pub async fn run_daemon_attached_acp_mode(options: DaemonAcpOptions) -> anyhow::Result<i32> {
    let (tx, mut rx) = tokio::sync::mpsc::unbounded_channel::<Value>();
    let writer = tokio::spawn(async move {
        let mut stdout = tokio::io::stdout();
        while let Some(frame) = rx.recv().await {
            let Ok(mut line) = serde_json::to_string(&frame) else {
                continue;
            };
            line.push('\n');
            if stdout.write_all(line.as_bytes()).await.is_err() {
                break;
            }
            if stdout.flush().await.is_err() {
                break;
            }
        }
    });

    let link = Arc::new(DaemonLink::connect(&options.socket_path).await?);
    let state = Arc::new(Mutex::new(DaemonAcpState {
        first_session: options.first_session.clone(),
        ..DaemonAcpState::default()
    }));
    let editor_requests = Arc::new(EditorRequests::default());

    // Session events and responses share one socket, so one consumer owns
    // the ordering: events publish at the active turn before the response
    // resolves the waiting request (a turn's chunks can never trail its
    // boundary frames).
    {
        let link = Arc::clone(&link);
        let state = Arc::clone(&state);
        let editor_requests = Arc::clone(&editor_requests);
        // Weak: the consumer lives as long as the daemon link, and must
        // not keep the stdout writer open past EOF.
        let sink = tx.downgrade();
        tokio::spawn(async move {
            let mut frames = link.frames.lock().await;
            while let Some(frame) = frames.recv().await {
                match frame {
                    LinkFrame::Event(frame) => on_session_event(&frame, &link, &state).await,
                    LinkFrame::Response(response) => {
                        let id = response.id.clone().unwrap_or_default();
                        if let Some(tx) = link.pending.lock().unwrap().remove(&id) {
                            let _ = tx.send(response);
                        }
                    }
                    // Heartbeats are connection-scoped, not session events,
                    // so the consumer maps the broadcast directly instead of
                    // `wire_updates`: TS publishes the change at origin turn 0
                    // even while a prompt runs.
                    LinkFrame::HeartbeatsChanged => {
                        let guard = state.lock().await;
                        if let Some(current) = guard.session.as_ref() {
                            let _ = current
                                .producer
                                .publish(
                                    &types::AcpSessionUpdate::SessionInfoUpdate {
                                        meta: meta::eukhe_meta(&EukheSessionMeta {
                                            heartbeats_changed: Some(true),
                                            ..Default::default()
                                        }),
                                    },
                                    0,
                                    EukheEventPhase::Event,
                                    None,
                                )
                                .await;
                        }
                    }
                    LinkFrame::EditorPermission(frame) => {
                        let Ok(frame) =
                            serde_json::from_value::<permission::PermissionFrame>(frame)
                        else {
                            continue;
                        };
                        let asked = state
                            .lock()
                            .await
                            .session
                            .as_ref()
                            .filter(|hosted| {
                                !hosted.editor_unsupported
                                    && hosted.daemon_active_session_id == frame.active_session_id
                            })
                            .map(|hosted| permission::Asked {
                                acp_session_id: hosted.acp_session_id.clone(),
                                params: permission::request_params(
                                    &hosted.acp_session_id,
                                    &frame.request,
                                ),
                            });
                        tokio::spawn(permission::answer(
                            Arc::clone(&link),
                            Arc::clone(&state),
                            Arc::clone(&editor_requests),
                            sink.clone(),
                            frame,
                            asked,
                        ));
                    }
                }
            }
            // The reader hit the socket close and every frame it read
            // has been delivered: fail the still-pending requests
            // (dropping a sender answers with the mid-request error)
            // and fail every later request fast. The flag goes up
            // before the clear; `request` covers the race.
            link.closed.store(true, std::sync::atomic::Ordering::SeqCst);
            link.pending.lock().unwrap().clear();
        });
    }
    let connection = Arc::new(Connection {
        options,
        mcp_owner_id: uuid::Uuid::new_v4().to_string(),
    });

    // Only the prompt handlers stay owned: EOF aborts them (TS aborts the
    // controller and exits), so the process never waits on a prompt still
    // settling its subagents. The other handlers spawn detached: a close
    // in flight at EOF finishes — its `tx` clone holds `writer.await` — so
    // its session still stops and releases its servers.
    let mut handlers = tokio::task::JoinSet::new();
    let mut stdin = BufReader::new(tokio::io::stdin());
    let mut input_line = String::new();
    loop {
        input_line.clear();
        match stdin.read_line(&mut input_line).await {
            Ok(0) | Err(_) => break,
            Ok(_) => {}
        }
        if input_line.trim().is_empty() {
            continue;
        }
        let incoming = match jsonrpc::parse_line(&input_line) {
            Ok(Incoming::Response { id, reply }) => {
                editor_requests.settle(&id, reply);
                continue;
            }
            Ok(incoming) => incoming,
            Err(error_response) => {
                let _ = tx.send(error_response);
                continue;
            }
        };
        // Handlers run concurrently (like the TS acp agent's request
        // handling): a prompt turn may span minutes, and `session/cancel`
        // must reach the daemon while it is in flight. The state machine
        // (one hosted session, one in-flight close) keeps the concurrency
        // bounded. Prompt admission and cancel marking run here, in frame
        // order (TS runs a request's synchronous prefix before the next
        // frame's handler).
        match frame_order_prefix(&incoming, &state).await {
            FrameOrder::Spawn => {
                // A session start settles before the next frame is read, so
                // EOF's teardown always sees the session it installs.
                if matches!(&incoming, Incoming::Request { method, .. } if StartKind::of_method(method).is_some())
                {
                    handle_incoming(incoming, &link, &state, &connection, tx.clone()).await;
                } else {
                    let link = Arc::clone(&link);
                    let state = Arc::clone(&state);
                    let connection = Arc::clone(&connection);
                    let options_tx = tx.clone();
                    tokio::spawn(async move {
                        handle_incoming(incoming, &link, &state, &connection, options_tx).await;
                    });
                }
            }
            FrameOrder::AdmitPrompt {
                id,
                params,
                admission_id,
            } => {
                let link = Arc::clone(&link);
                let state = Arc::clone(&state);
                let options_tx = tx.clone();
                handlers.spawn(async move {
                    handle_session_prompt(id, params, admission_id, &link, &state, options_tx)
                        .await;
                });
            }
            // A refused prompt or close answers from the prefix; the
            // running turn is untouched.
            FrameOrder::Refused { id, refusal } => {
                let _ = tx.send(refusal_response(&id, &refusal));
            }
            FrameOrder::Close { id, params, done } => {
                let link = Arc::clone(&link);
                let state = Arc::clone(&state);
                let connection = Arc::clone(&connection);
                let options_tx = tx.clone();
                tokio::spawn(async move {
                    handle_session_close(id, params, &link, &state, options_tx, done, &connection)
                        .await;
                });
            }
            FrameOrder::Cancel(order) => {
                let link = Arc::clone(&link);
                let state = Arc::clone(&state);
                tokio::spawn(async move {
                    let mut order = order;
                    loop {
                        order = match order {
                            CancelOrder::None => return,
                            CancelOrder::Armed(stop) => {
                                run_cancel_stop(stop, &link, &state).await;
                                return;
                            }
                            CancelOrder::WaitForClose { session_id } => {
                                wait_for_session_close(&state).await;
                                cancel_order(&json!({ "sessionId": session_id }), &state).await
                            }
                        };
                    }
                });
            }
        }
        // Reap finished prompt handlers.
        while handlers.try_join_next().is_some() {}
    }

    // The editor left: its open questions end unanswered (the daemon runs
    // them once this client detaches).
    editor_requests.close();
    handlers.shutdown().await;
    // A close frame is reserved synchronously but its stop runs detached.
    // Let it finish before EOF teardown takes the hosted session away.
    wait_for_session_close(&state).await;
    teardown(&link, &state, &connection).await;
    drop(tx);
    let _ = writer.await;
    Ok(0)
}

/// The session event types the ACP bridge acts on beyond the update
/// mapping.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AcpEventKind {
    RlmChildUpdate,
    /// A run that can restore a failover model or clamp a level
    /// (`agent_end`, `auto_retry_start`, `auto_retry_end`).
    ConfigRefresh,
    Other,
}

impl AcpEventKind {
    fn of(event: &Value) -> Self {
        match event.get("type").and_then(Value::as_str) {
            Some("rlm_child_update") => Self::RlmChildUpdate,
            Some("agent_end" | "auto_retry_start" | "auto_retry_end") => Self::ConfigRefresh,
            Some(_) | None => Self::Other,
        }
    }
}

/// One daemon session event: published as ACP updates on the hosted
/// session it belongs to; its answer and stop reason recorded for the turn.
async fn on_session_event(
    frame: &Value,
    link: &Arc<DaemonLink>,
    state: &Arc<Mutex<DaemonAcpState>>,
) {
    let event = frame.get("event").unwrap_or(&Value::Null);
    let event_kind = AcpEventKind::of(event);
    // The picker refresh triggers (TS refreshes on `agent_end`,
    // `auto_retry_start`, and `auto_retry_end` — the runs that can restore
    // a failover model or clamp a level): captured under the guard,
    // spawned once it is released.
    let (config, producer, daemon_session_id) = {
        let mut guard = state.lock().await;
        let Some(current) = guard.session.as_mut().filter(|hosted| {
            frame.get("activeSessionId").and_then(Value::as_str)
                == Some(hosted.daemon_active_session_id.as_str())
        }) else {
            return;
        };
        if let Some(stop) = wire_events::assistant_stop(event) {
            current.assistant_stop_reason = stop.stop_reason;
        }
        if let Some(answer) = wire_events::assistant_answer(event) {
            current.turn_answer = Some(answer);
        }
        if event_kind == AcpEventKind::RlmChildUpdate {
            if let Some(id) = event
                .get("child")
                .and_then(|child| child.get("id"))
                .and_then(Value::as_str)
            {
                current.observed_children.insert(id.to_string());
            }
        }
        let turn_id = current.producer.active_prompt_turn().await;
        for update in wire_events::wire_updates(event, &mut current.mapping) {
            let _ = current
                .producer
                .publish(&update, turn_id, EukheEventPhase::Event, None)
                .await;
        }
        (
            Arc::clone(&current.config),
            Arc::clone(&current.producer),
            current.daemon_active_session_id.clone(),
        )
    };
    if event_kind == AcpEventKind::ConfigRefresh {
        let link = Arc::clone(link);
        tokio::spawn(async move {
            // Serialized like every config operation (TS `enqueueConfig`);
            // the background trigger drops refresh failures (TS's
            // `.catch(() => undefined)`).
            let _guard = config.queue.lock().await;
            let _ = refresh_wire_config(&link, &daemon_session_id, &config, &producer).await;
        });
    }
}

/// The answer to a prompt or close refused before it reached the daemon.
fn refusal_response(id: &Value, refusal: &AcpRefusal) -> Value {
    match refusal {
        AcpRefusal::UnknownSession { session_id } => jsonrpc::session_not_found(id, session_id),
        AcpRefusal::Closing { .. }
        | AcpRefusal::AlreadyClosing { .. }
        | AcpRefusal::Cancelling { .. }
        | AcpRefusal::StopFailed { .. }
        | AcpRefusal::TurnRunning => super::internal_error(id, &refusal.to_string()),
    }
}

enum FrameOrder {
    Spawn,
    AdmitPrompt {
        id: Value,
        params: Value,
        admission_id: String,
    },
    Refused {
        id: Value,
        refusal: AcpRefusal,
    },
    Close {
        id: Value,
        params: Value,
        done: tokio::sync::watch::Sender<bool>,
    },
    Cancel(CancelOrder),
}

enum CancelOrder {
    None,
    Armed(CancelStop),
    WaitForClose { session_id: String },
}

struct CancelStop {
    acp_session_id: String,
    daemon_session_id: String,
    admission_id: Option<String>,
    done: tokio::sync::watch::Sender<bool>,
}

/// Prompt admission and cancel marking, in the client's frame order.
async fn frame_order_prefix(incoming: &Incoming, state: &Arc<Mutex<DaemonAcpState>>) -> FrameOrder {
    match incoming {
        Incoming::Request { id, method, params } if method == "session/prompt" => {
            match admit_prompt(params, state).await {
                Ok(admission_id) => FrameOrder::AdmitPrompt {
                    id: id.clone(),
                    params: params.clone(),
                    admission_id,
                },
                Err(refusal) => FrameOrder::Refused {
                    id: id.clone(),
                    refusal,
                },
            }
        }
        Incoming::Request { id, method, params } if method == "session/close" => {
            let session_id = params
                .get("sessionId")
                .and_then(Value::as_str)
                .unwrap_or_default()
                .to_string();
            let (done_tx, done_rx) = tokio::sync::watch::channel(false);
            let mut guard = state.lock().await;
            if guard
                .session
                .as_ref()
                .is_none_or(|hosted| hosted.acp_session_id != session_id)
            {
                return FrameOrder::Refused {
                    id: id.clone(),
                    refusal: AcpRefusal::UnknownSession { session_id },
                };
            }
            if guard.session_close_done.is_some() {
                return FrameOrder::Refused {
                    id: id.clone(),
                    refusal: AcpRefusal::AlreadyClosing { session_id },
                };
            }
            guard.session_close_done = Some(done_rx);
            FrameOrder::Close {
                id: id.clone(),
                params: params.clone(),
                done: done_tx,
            }
        }
        Incoming::Notification { method, params } if method == "session/cancel" => {
            FrameOrder::Cancel(cancel_order(params, state).await)
        }
        _ => FrameOrder::Spawn,
    }
}

/// Reserve the turn slot for one prompt. `Err` is the refusal message,
/// checked in TS order: unknown session, closing, cancelling, stop
/// failure, turn running.
async fn admit_prompt(
    params: &Value,
    state: &Arc<Mutex<DaemonAcpState>>,
) -> Result<String, AcpRefusal> {
    let session_id = params
        .get("sessionId")
        .and_then(Value::as_str)
        .unwrap_or_default();
    let mut guard = state.lock().await;
    let session_closing = guard.session_close_done.is_some();
    let Some(hosted) = guard
        .session
        .as_mut()
        .filter(|hosted| hosted.acp_session_id == session_id)
    else {
        return Err(AcpRefusal::UnknownSession {
            session_id: session_id.to_string(),
        });
    };
    if session_closing {
        return Err(AcpRefusal::Closing {
            session_id: session_id.to_string(),
        });
    }
    if hosted.cancelling {
        return Err(AcpRefusal::Cancelling {
            session_id: session_id.to_string(),
        });
    }
    if let Some(stop_failure) = hosted.stop_failure.as_ref() {
        return Err(AcpRefusal::StopFailed {
            source: Arc::clone(stop_failure),
        });
    }
    if hosted.turn.is_some() {
        return Err(AcpRefusal::TurnRunning);
    }
    let admission_id = format!("prompt-admission:{}", uuid::Uuid::new_v4());
    // The stop reason is per-turn: a turn that runs no model call (a
    // slash command) must not inherit the previous turn's stop reason.
    hosted.assistant_stop_reason = None;
    hosted.turn_answer = None;
    hosted.turn = Some(ActiveTurn {
        admission_id: admission_id.clone(),
        cancelled: false,
    });
    Ok(admission_id)
}

/// One incoming ACP frame. Requests answer.
async fn handle_incoming(
    incoming: Incoming,
    link: &Arc<DaemonLink>,
    state: &Arc<Mutex<DaemonAcpState>>,
    connection: &Arc<Connection>,
    tx: producer::FrameSink,
) {
    let Incoming::Request { id, method, params } = incoming else {
        return;
    };
    if let Some(kind) = StartKind::of_method(&method) {
        sessions::handle_session_start(kind, id, params, link, state, connection, tx).await;
        return;
    }
    if method.starts_with(extensions::PREFIX) {
        handle_extension(id, &method, &params, link, state, tx).await;
        return;
    }
    match method.as_str() {
        "initialize" => {
            handle_initialize(&id, &params, state, connection, &tx).await;
        }
        "authenticate" => {
            sessions::handle_authenticate(id, params, link, state, connection, tx).await;
        }
        "session/list" => {
            sessions::handle_session_list(id, params, link, connection, tx).await;
        }
        "session/delete" => {
            sessions::handle_session_delete(id, params, link, state, connection, tx).await;
        }
        "session/set_config_option" => {
            handle_set_config_option(id, params, link, state, tx).await;
        }
        other => {
            let _ = tx.send(jsonrpc::method_not_found(&id, other));
        }
    }
}

/// One `_eukhe/` request on the hosted session.
async fn handle_extension(
    id: Value,
    method: &str,
    params: &Value,
    link: &DaemonLink,
    state: &Arc<Mutex<DaemonAcpState>>,
    tx: producer::FrameSink,
) {
    let extension = match extensions::parse(method, params) {
        Ok(extension) => extension,
        Err(error) => {
            let _ = tx.send(extensions::error_response(&id, method, &error));
            return;
        }
    };
    let session_id = params
        .get("sessionId")
        .and_then(Value::as_str)
        .unwrap_or_default();
    let daemon_session_id = state
        .lock()
        .await
        .session
        .as_ref()
        .filter(|hosted| hosted.acp_session_id == session_id)
        .map(|hosted| hosted.daemon_active_session_id.clone());
    let Some(daemon_session_id) = daemon_session_id else {
        let _ = tx.send(jsonrpc::session_not_found(&id, session_id));
        return;
    };
    let reply = match extensions::run(link, &daemon_session_id, extension).await {
        Ok(result) => jsonrpc::response(&id, &result),
        Err(error) => extensions::error_response(&id, method, &error),
    };
    let _ = tx.send(reply);
}

async fn handle_initialize(
    id: &Value,
    params: &Value,
    state: &Arc<Mutex<DaemonAcpState>>,
    connection: &Connection,
    tx: &producer::FrameSink,
) {
    if let Err(error_response) = validate_initialize(id, params) {
        let _ = tx.send(error_response);
        return;
    }
    let terminal = TerminalLogin::of_initialize(params);
    state.lock().await.terminal_login = terminal;
    let result = serde_json::to_value(types::initialize_result(
        &connection.options.product_version,
        auth::auth_methods(terminal),
    ))
    .expect("serializes");
    let _ = tx.send(jsonrpc::response(id, &result));
}

/// The `initialize` schema check the TS SDK performs: the protocol version
/// must be a number. The error body mirrors the observed TS response.
fn validate_initialize(id: &Value, params: &Value) -> std::result::Result<(), Value> {
    let field_error = |received: &str| {
        jsonrpc::error_response(
            id,
            jsonrpc::INVALID_PARAMS,
            "Invalid params",
            Some(&json!({
                "_errors": [],
                "protocolVersion": {
                    "_errors": [format!("Invalid input: expected number, received {received}")]
                },
            })),
        )
    };
    match params.get("protocolVersion") {
        None => Err(field_error("undefined")),
        Some(value) if value.is_number() => Ok(()),
        Some(Value::String(_)) => Err(field_error("string")),
        Some(Value::Bool(_)) => Err(field_error("boolean")),
        Some(Value::Null) => Err(field_error("null")),
        Some(_) => Err(field_error("object")),
    }
}

/// One admitted prompt: its turn on the hosted session, then the turn's
/// run report, then its response.
async fn handle_session_prompt(
    id: Value,
    params: Value,
    admission_id: String,
    link: &Arc<DaemonLink>,
    state: &Arc<Mutex<DaemonAcpState>>,
    tx: producer::FrameSink,
) {
    let params = types::PromptParams::parse(&params);
    let hosted = {
        let guard = state.lock().await;
        guard
            .session
            .as_ref()
            .filter(|hosted| hosted.acp_session_id == params.session_id)
            .map(|hosted| {
                (
                    Arc::clone(&hosted.producer),
                    hosted.daemon_active_session_id.clone(),
                )
            })
    };
    let reply = match (types::AdmittedPrompt::parse(&params.prompt), hosted) {
        (Err(error), _) => prompt_block_error(&id, &error),
        // Admission checked the session id: a miss is a close since.
        (Ok(_), None) => cancelled_response(&id),
        (Ok(admitted), Some((producer, daemon_session_id))) => {
            let turn_id = producer.begin_prompt().await;
            let before = run_report::effects_before(link, &daemon_session_id).await;
            let turn = PromptTurn {
                producer,
                daemon_session_id,
                turn_id,
            };
            let reply = prompt_turn(id, admitted, &turn, &admission_id, link, state).await;
            let answer = state
                .lock()
                .await
                .session
                .as_mut()
                .filter(|hosted| hosted.acp_session_id == params.session_id)
                .and_then(|hosted| hosted.turn_answer.take());
            let report = run_report::report(
                link,
                run_report::Turn {
                    acp_session_id: &params.session_id,
                    daemon_session_id: &turn.daemon_session_id,
                    turn_id,
                    reply: &reply,
                    answer,
                    before,
                },
            )
            .await;
            let _ = tx.send(report);
            reply
        }
    };
    release_turn_slot(state, &admission_id).await;
    let _ = tx.send(reply);
}

/// The turn a prompt runs: its session's producer and daemon id, its id.
struct PromptTurn {
    producer: Arc<UpdateProducer>,
    daemon_session_id: String,
    turn_id: u64,
}

/// Release this prompt's turn slot, after its stop sequence if it was
/// cancelled. A slot holding another prompt's turn (close + new while
/// this prompt ran) is left alone.
async fn release_turn_slot(state: &Arc<Mutex<DaemonAcpState>>, admission_id: &str) {
    let mut cancel_task = {
        let mut guard = state.lock().await;
        let Some(hosted) = guard.session.as_mut() else {
            return;
        };
        let Some(turn) = hosted.turn.as_mut() else {
            return;
        };
        if turn.admission_id != admission_id {
            return;
        }
        hosted.cancel_task.clone()
    };
    if let Some(cancel_task) = cancel_task.as_mut() {
        let _ = cancel_task.changed().await;
    }
    if let Some(hosted) = state.lock().await.session.as_mut() {
        hosted
            .turn
            .take_if(|turn| turn.admission_id == admission_id);
    }
}

/// Whether this prompt lost its turn: cancelled, or its session was closed
/// (close, or close + new, takes the slot - like TS close aborting the turn).
fn turn_cancelled(state: &DaemonAcpState, admission_id: &str) -> bool {
    !state
        .session
        .as_ref()
        .and_then(|hosted| hosted.turn.as_ref())
        .is_some_and(|turn| turn.admission_id == admission_id && !turn.cancelled)
}

fn cancelled_response(id: &Value) -> Value {
    jsonrpc::response(
        id,
        &serde_json::to_value(types::AcpStopReasonResponse {
            stop_reason: types::AcpStopReason::Cancelled,
        })
        .expect("serializes"),
    )
}

/// Render a prompt-block failure as the ACP invalid-params error. The TS
/// SDK validates the request schema; the Rust port validates the blocks it
/// actually reads.
fn prompt_block_error(id: &Value, error: &types::PromptBlockError) -> Value {
    jsonrpc::error_response(
        id,
        jsonrpc::INVALID_PARAMS,
        "Invalid params",
        Some(&json!({ "reason": error.to_string() })),
    )
}

/// Run one admitted prompt turn and return its reply frame.
async fn prompt_turn(
    id: Value,
    admitted: types::AdmittedPrompt,
    turn: &PromptTurn,
    admission_id: &str,
    link: &Arc<DaemonLink>,
    state: &Arc<Mutex<DaemonAcpState>>,
) -> Value {
    let producer = Arc::clone(&turn.producer);
    let hosted_daemon_session_id = turn.daemon_session_id.clone();
    let turn_id = turn.turn_id;
    // TS `abort.signal.aborted` before `promptAndWait`.
    let cancelled = turn_cancelled(&*state.lock().await, admission_id);
    if cancelled {
        producer.finish_prompt(turn_id).await;
        return cancelled_response(&id);
    }
    let prompt = DaemonCommand::PromptAndWait {
        id: None,
        active_session_id: hosted_daemon_session_id.clone(),
        message: admitted.text,
        input: eukhe_types::daemon::PromptInput {
            content: None,
            // The image blocks ride the wire form `parse_prompt_images`
            // reads (`{type, data, mimeType}`); TS forwards `images`
            // only when the prompt carries any.
            images: (!admitted.images.is_empty()).then(|| {
                json!(admitted
                    .images
                    .into_iter()
                    .map(|image| json!({ "type": "image", "data": image.data, "mimeType": image.mime_type }))
                    .collect::<Vec<_>>())
            }),
            // TS sends `followUp` + `queueIfBusy: true` on every ACP
            // prompt (acp-mode.ts): a prompt carrying a streaming
            // behavior is the worker's resume site for the post-abort
            // queued-input suspension, so a prompt after a Stop runs.
            streaming_behavior: Some(eukhe_types::daemon::StreamingBehavior::FollowUp),
            queue_if_busy: Some(true),
            expand_prompt_templates: None,
            source: None,
            agent_message_id: None,
            custom_message: None,
            queue_key: None,
            prefix_messages: None,
            admission_id: Some(admission_id.to_string()),
            rlm_notice_nonce: None,
            reply_to: None,
        },
        rest: Map::default(),
    };
    let response = match link.request_until_close(prompt).await {
        Ok(response) => response,
        Err(error) => {
            publish_error_boundary(&producer, turn_id).await;
            producer.finish_prompt(turn_id).await;
            return super::internal_error(&id, &error.to_string());
        }
    };
    // TS `abort.signal.aborted` after `promptAndWait`: every turn frame
    // is published by now - the worker flushes its session events before
    // the response leaves its socket, and the supervisor's per-client
    // writer writes a queued event ahead of a queued response - so the
    // settle reads the stream directly, with no marker wait.
    let cancelled = {
        let guard = state.lock().await;
        turn_cancelled(&guard, admission_id)
    };
    if cancelled {
        producer.finish_prompt(turn_id).await;
        return cancelled_response(&id);
    }
    // TS settle catch: one error boundary, no terminal-quiescence update.
    if !response.success {
        // A run that failed at the length cap (its replies kept hitting the
        // output limit) ended on the output limit: an honest `max_tokens`.
        let truncated = state
            .lock()
            .await
            .session
            .as_ref()
            .and_then(|hosted| hosted.assistant_stop_reason)
            == Some(eukhe_types::ai::StopReason::Length);
        let prefix_refused = response.error_info == Some(DaemonErrorInfo::PrefixRefused);
        let failure = response
            .error
            .unwrap_or_else(|| "unknown error".to_string());
        // The failure text rides the internal_error reply, where a test
        // asserting only the stop reason loses it: echo it to stderr so
        // every harness's child-stderr dump shows WHY the turn failed.
        eprintln!("eukhe-daemon: acp turn failed: {failure}");
        publish_error_boundary(&producer, turn_id).await;
        producer.finish_prompt(turn_id).await;
        // A prompt whose run never began (its `/b` prefix did not read)
        // sent nothing: its refusal is the answer, never the stop reason
        // the run before left on the session.
        if prefix_refused {
            return super::internal_error(&id, &format!("eukhe turn failed: {failure}"));
        }
        if truncated {
            let stop_reason = types::AcpStopReason::MaxTokens;
            return jsonrpc::response(
                &id,
                &serde_json::to_value(types::AcpStopReasonResponse { stop_reason })
                    .expect("serializes"),
            );
        }
        // A turn the session's budget stopped (its request did not fit)
        // ended at that limit: its stop reason (the budget short in tokens:
        // `max_tokens`; else `max_turn_requests`).
        let budget_stop =
            fetch_autonomous_status(link, &hosted_daemon_session_id, CompletionWait::Run)
                .await
                .ok()
                .and_then(|status| meta::budget_stop_reason(status.budget.as_ref()));
        if let Some(stop_reason) = budget_stop {
            return jsonrpc::response(
                &id,
                &serde_json::to_value(types::AcpStopReasonResponse { stop_reason })
                    .expect("serializes"),
            );
        }
        return super::internal_error(&id, &format!("eukhe turn failed: {failure}"));
    }
    // The autonomous accounting for the completion envelope: the daemon's
    // headless-completion status (TS `waitForHeadlessCompletion`), fetched
    // after the turn settled (the response is the run's end). A failed
    // fetch degrades to no autonomous meta (the envelope still settles
    // without a run).
    let autonomous_status =
        fetch_autonomous_status(link, &hosted_daemon_session_id, CompletionWait::Run)
            .await
            .ok();
    // TS `abort.signal.aborted` after `waitForHeadlessCompletion`: queued
    // continuations (autonomous, post-compaction) run inside that wait.
    if turn_cancelled(&*state.lock().await, admission_id) {
        producer.finish_prompt(turn_id).await;
        return cancelled_response(&id);
    }
    // The completion observation's roster read (TS `getRlmChildSnapshots`
    // throws): a failed read errors the prompt before the boundary, never
    // publishes a wrong count.
    let children = match fetch_rlm_children(link, &hosted_daemon_session_id).await {
        Ok(children) => children,
        Err(error) => {
            publish_error_boundary(&producer, turn_id).await;
            producer.finish_prompt(turn_id).await;
            return super::internal_error(&id, &error.to_string());
        }
    };
    // What the turn's end left running (the session summary's
    // `waitingOn`): the completion names it, and the settle below holds
    // until it settled. A failed read errors the prompt like the roster
    // read: the completion never reads quiescent on an unknown.
    let waiting_on = async {
        let response = link
            .request(DaemonCommand::GetState {
                id: None,
                active_session_id: hosted_daemon_session_id.clone(),
                rest: Map::default(),
            })
            .await?;
        if !response.success {
            return Err(DaemonCommandError::Refused {
                message: response.error,
            });
        }
        let waiting_on = response
            .data
            .as_ref()
            .and_then(|state| state.get("waitingOn"))
            .cloned()
            .unwrap_or(Value::Null);
        serde_json::from_value::<Option<eukhe_types::daemon::WaitingOn>>(waiting_on)
            .map_err(DaemonCommandError::Decode)
    }
    .await;
    let waiting_on = match waiting_on {
        Ok(waiting_on) => waiting_on,
        Err(error) => {
            publish_error_boundary(&producer, turn_id).await;
            producer.finish_prompt(turn_id).await;
            return super::internal_error(&id, &error.to_string());
        }
    };
    if turn_cancelled(&*state.lock().await, admission_id) {
        producer.finish_prompt(turn_id).await;
        return cancelled_response(&id);
    }
    let autonomous_meta = autonomous_status
        .as_ref()
        .filter(|status| status.enabled)
        .map(meta::autonomous_meta);
    // The context in use after the turn's answer, ahead of its boundary.
    sessions::publish_usage(link, &hosted_daemon_session_id, &producer).await;
    // The boundary, completion, and terminal quiescence frames match the
    // TS captures.
    let boundary = types::AcpSessionUpdate::SessionInfoUpdate {
        meta: meta::eukhe_meta(&EukheSessionMeta {
            terminal_quiescence_expected: Some(true),
            ..Default::default()
        }),
    };
    let published = producer
        .publish(
            &boundary,
            turn_id,
            EukheEventPhase::ResponseBoundary,
            Some(EukheOutcome::Result),
        )
        .await;
    // The completion envelope: the turn's own observation, with the
    // live outstanding-subagent count and the work still running, which
    // the settle loop then waits down to nothing.
    let quiescence = types::AcpSessionUpdate::SessionInfoUpdate {
        meta: meta::eukhe_meta(&EukheSessionMeta {
            autonomous: autonomous_meta,
            quiescence: Some(quiescence_meta(&children, waiting_on)),
            ..Default::default()
        }),
    };
    let completion_published = producer
        .publish(&quiescence, turn_id, EukheEventPhase::Event, None)
        .await;
    // The settlement loop (TS `finalizePendingTerminal`): the barrier is
    // the event, no timer, and the roster re-read is the response-cut
    // signal (a child can publish a terminal status before its result
    // reaches the parent). The barrier holds past the parent's idle while
    // a child, a workflow run or a job runs, and through the turn each
    // one's end wakes. A cancel or a close ends the hold at once. A failed
    // barrier or read errors the prompt; a degraded status would spin the
    // loop.
    let turn_lost = Arc::clone(&state.lock().await.turn_lost);
    let settled_status = loop {
        let barrier =
            fetch_autonomous_status(link, &hosted_daemon_session_id, CompletionWait::Quiescence);
        let lost = async {
            loop {
                let notified = turn_lost.notified();
                tokio::pin!(notified);
                notified.as_mut().enable();
                if turn_cancelled(&*state.lock().await, admission_id) {
                    break;
                }
                notified.await;
            }
        };
        let status = tokio::select! {
            status = barrier => status,
            () = lost => {
                producer.finish_prompt(turn_id).await;
                return cancelled_response(&id);
            }
        };
        let status = match status {
            Ok(status) => status,
            Err(error) => {
                producer.finish_prompt(turn_id).await;
                return super::internal_error(
                    &id,
                    &format!("ACP lifecycle reconciliation failed: {error}"),
                );
            }
        };
        if turn_cancelled(&*state.lock().await, admission_id) {
            producer.finish_prompt(turn_id).await;
            return cancelled_response(&id);
        }
        let children = match fetch_rlm_children(link, &hosted_daemon_session_id).await {
            Ok(children) => children,
            Err(error) => {
                producer.finish_prompt(turn_id).await;
                return super::internal_error(
                    &id,
                    &format!("ACP lifecycle reconciliation failed: {error}"),
                );
            }
        };
        if turn_cancelled(&*state.lock().await, admission_id) {
            producer.finish_prompt(turn_id).await;
            return cancelled_response(&id);
        }
        let terminal_quiescence = quiescence_meta(&children, None);
        if terminal_quiescence.outstanding_subagents != 0 {
            continue;
        }
        // TS `sealTerminal`: the terminal frame is the last update stamped
        // with this turn; later events resume turn 0.
        producer.finish_prompt(turn_id).await;
        let terminal = types::AcpSessionUpdate::SessionInfoUpdate {
            meta: meta::eukhe_meta(&EukheSessionMeta {
                autonomous: status.enabled.then(|| meta::autonomous_meta(&status)),
                quiescence: Some(terminal_quiescence),
                ..Default::default()
            }),
        };
        let terminal_published = producer
            .publish(
                &terminal,
                turn_id,
                EukheEventPhase::TerminalQuiescence,
                Some(EukheOutcome::Result),
            )
            .await;
        if !published || !completion_published || !terminal_published {
            return super::internal_error(&id, "Failed to publish ACP completion");
        }
        break status;
    };
    // The stop reason follows the TS mapping (acp-stop-reason.ts) plus the
    // turn's final assistant stop reason (#3363): the abort flag read after
    // the settlement, the settlement's status (`pending.status`), not the
    // first observation's, and the newest assistant stop reason — the link's
    // one frame consumer applies every message_end (the autonomous
    // continuations' included, since they run inside the waits above) before
    // the response that ended each wait resolved, so this read after the
    // settlement sees the run's final one.
    let (cancelled, assistant_stop_reason) = {
        let guard = state.lock().await;
        (
            turn_cancelled(&guard, admission_id),
            guard
                .session
                .as_ref()
                .and_then(|hosted| hosted.assistant_stop_reason),
        )
    };
    let stop_reason =
        meta::acp_stop_reason_for_status(cancelled, Some(&settled_status), assistant_stop_reason);
    jsonrpc::response(
        &id,
        &serde_json::to_value(types::AcpStopReasonResponse { stop_reason }).expect("serializes"),
    )
}

/// The error boundary a failed turn publishes (TS
/// `terminalQuiescenceExpected: false`).
async fn publish_error_boundary(producer: &Arc<UpdateProducer>, turn_id: u64) {
    let boundary = types::AcpSessionUpdate::SessionInfoUpdate {
        meta: meta::eukhe_meta(&EukheSessionMeta {
            terminal_quiescence_expected: Some(false),
            ..Default::default()
        }),
    };
    let _ = producer
        .publish(
            &boundary,
            turn_id,
            EukheEventPhase::ResponseBoundary,
            Some(EukheOutcome::Error),
        )
        .await;
}

/// What the headless-completion wait holds for.
#[derive(Clone, Copy)]
enum CompletionWait {
    /// The run's own settle.
    Run,
    /// The quiescence barrier: past the run's idle, every child run,
    /// workflow run and running job until each settled and the turn its
    /// end woke settled too (the work that would wake the session again).
    Quiescence,
}

/// Fetch the session's autonomous-run status (`wait_for_headless_completion`
/// on the daemon wire; TS `waitForHeadlessCompletion`), once `wait` settled.
/// The quiescence barrier is the event the settlement loop waits on. A
/// failure is the caller's policy (TS throws for both callers): the
/// completion observation degrades, the settlement loop errors the prompt.
///
/// # Errors
///
/// Returns an error when the daemon connection fails or closes mid-request,
/// when the response reports a failure, or when the status payload does not
/// deserialize.
async fn fetch_autonomous_status(
    link: &Arc<DaemonLink>,
    active_session_id: &str,
    wait: CompletionWait,
) -> Result<eukhe_core::autonomous::AgentAutonomousStatus, DaemonCommandError> {
    let (wait_for_rlm_quiescence, rest) = match wait {
        CompletionWait::Run => (None, Map::default()),
        CompletionWait::Quiescence => (
            Some(true),
            Map::from_iter([("waitForBackgroundJobs".to_owned(), json!(true))]),
        ),
    };
    let response = link
        .request_until_close(DaemonCommand::WaitForHeadlessCompletion {
            id: None,
            active_session_id: active_session_id.to_string(),
            wait_for_rlm_quiescence,
            rest,
        })
        .await?;
    if !response.success {
        return Err(DaemonCommandError::Refused {
            message: response.error,
        });
    }
    serde_json::from_value(response.data.unwrap_or(Value::Null)).map_err(DaemonCommandError::Decode)
}

/// The live child roster (`get_rlm_children` on the daemon wire; TS
/// `getRlmChildSnapshots` throws).
///
/// # Errors
///
/// Returns an error when the daemon connection fails or closes mid-request,
/// when the response reports a failure, or when the answer carries no
/// children array.
async fn fetch_rlm_children(
    link: &Arc<DaemonLink>,
    active_session_id: &str,
) -> Result<Vec<Value>, DaemonCommandError> {
    let response = link
        .request(DaemonCommand::GetRlmChildren {
            id: None,
            active_session_id: active_session_id.to_string(),
            rest: Map::default(),
        })
        .await?;
    if !response.success {
        return Err(DaemonCommandError::Refused {
            message: response.error,
        });
    }
    response
        .data
        .unwrap_or(Value::Null)
        .get("children")
        .cloned()
        .and_then(|children| children.as_array().cloned())
        .ok_or(DaemonCommandError::NoChildrenArray)
}

/// TS `outstandingSubagentCount`: the roster's live statuses, verbatim.
fn outstanding_subagents(children: &[Value]) -> u64 {
    children
        .iter()
        .filter(|child| {
            matches!(
                child.get("status").and_then(Value::as_str),
                Some("queued" | "running")
            )
        })
        .count() as u64
}

/// TS `quiescenceMeta`: the outstanding-subagent count plus the run's
/// remaining continuation slots, observed together at one completion
/// point, with the work still running there (`None` when nothing runs).
fn quiescence_meta(
    children: &[Value],
    waiting_on: Option<eukhe_types::daemon::WaitingOn>,
) -> meta::EukheQuiescenceMeta {
    meta::EukheQuiescenceMeta {
        outstanding_subagents: outstanding_subagents(children),
        // The run has no continuation cap: at a settled completion its
        // continuations are over.
        remaining_autonomous_continuations: 0,
        waiting_on,
    }
}

#[cfg(test)]
mod tests {
    use super::stop::arm_cancel_locked;
    use super::*;

    fn hosted_session() -> HostedSession {
        let (sink, _drain) = mpsc::unbounded_channel();
        HostedSession::new(
            DaemonSession {
                active_session_id: "daemon-1".to_string(),
                session_id: "acp-1".to_string(),
                session_file: None,
                lifecycle: DaemonSessionLifecycle::ClientOwned,
                cwd: PathBuf::from("/tmp"),
            },
            UpdateProducer::new("acp-1", sink),
            Arc::new(HostedConfig {
                queue: tokio::sync::Mutex::new(()),
                published: tokio::sync::Mutex::new(Vec::new()),
                models: tokio::sync::Mutex::new(Vec::new()),
            }),
            WireMappingState::default(),
            std::collections::HashSet::new(),
        )
    }

    fn state(session: Option<HostedSession>) -> DaemonAcpState {
        DaemonAcpState {
            session,
            ..DaemonAcpState::default()
        }
    }

    #[tokio::test]
    async fn eof_waits_for_a_reserved_close_before_taking_the_session() {
        let state = Arc::new(Mutex::new(state(Some(hosted_session()))));
        let order = frame_order_prefix(
            &Incoming::Request {
                id: json!(1),
                method: "session/close".to_string(),
                params: json!({ "sessionId": "acp-1" }),
            },
            &state,
        )
        .await;
        let FrameOrder::Close { done, .. } = order else {
            panic!("the close should reserve its stop");
        };
        let eof = tokio::spawn({
            let state = Arc::clone(&state);
            async move {
                wait_for_session_close(&state).await;
                state.lock().await.session.take().is_some()
            }
        });
        tokio::task::yield_now().await;
        assert!(
            !eof.is_finished(),
            "EOF must not take the session before close finishes"
        );
        assert!(state.lock().await.session.is_some());
        done.send(true).unwrap();
        state.lock().await.session_close_done = None;
        assert!(eof.await.unwrap());

        // A close can settle before EOF checks the state. No stale watch
        // should be awaited, and the hosted session is still available.
        let (done, mut done_rx) = tokio::sync::watch::channel(false);
        let settled = Arc::new(Mutex::new(self::state(Some(hosted_session()))));
        done.send(true).unwrap();
        assert!(*done_rx.borrow_and_update());
        settled.lock().await.session_close_done = Some(done_rx);
        tokio::time::timeout(
            std::time::Duration::from_secs(2),
            wait_for_session_close(&settled),
        )
        .await
        .expect("an already completed close must not strand EOF");
    }

    #[tokio::test]
    async fn admit_prompt_matches_the_ts_refusal_order() {
        let none = Arc::new(Mutex::new(state(None)));
        assert_eq!(
            admit_prompt(&json!({ "sessionId": "nope" }), &none)
                .await
                .unwrap_err()
                .to_string(),
            "Unknown ACP session: nope"
        );

        let closing = Arc::new(Mutex::new({
            let mut state = state(Some(hosted_session()));
            let (_done_tx, done_rx) = tokio::sync::watch::channel(false);
            state.session_close_done = Some(done_rx);
            state
        }));
        assert_eq!(
            admit_prompt(&json!({ "sessionId": "acp-1" }), &closing)
                .await
                .unwrap_err()
                .to_string(),
            "ACP session is closing: acp-1"
        );

        let mut cancelling = state(Some(hosted_session()));
        cancelling.session.as_mut().unwrap().cancelling = true;
        let cancelling = Arc::new(Mutex::new(cancelling));
        assert_eq!(
            admit_prompt(&json!({ "sessionId": "acp-1" }), &cancelling)
                .await
                .unwrap_err()
                .to_string(),
            "ACP session is cancelling: acp-1"
        );

        let mut failed = state(Some(hosted_session()));
        failed.session.as_mut().unwrap().stop_failure =
            Some(Arc::new(DaemonCommandError::Refused {
                message: Some("boom".to_string()),
            }));
        failed.session.as_mut().unwrap().turn = Some(ActiveTurn {
            admission_id: "prompt-admission:1".to_string(),
            cancelled: false,
        });
        let failed = Arc::new(Mutex::new(failed));
        assert_eq!(
            admit_prompt(&json!({ "sessionId": "acp-1" }), &failed)
                .await
                .unwrap_err()
                .to_string(),
            "ACP session stop failed: boom"
        );

        let clean = Arc::new(Mutex::new(state(Some(hosted_session()))));
        let admitted = admit_prompt(&json!({ "sessionId": "acp-1" }), &clean)
            .await
            .unwrap();
        assert!(admitted.starts_with("prompt-admission:"));
        assert_eq!(
            admit_prompt(&json!({ "sessionId": "acp-1" }), &clean)
                .await
                .unwrap_err()
                .to_string(),
            "A prompt turn is already running for this ACP session"
        );
    }

    #[test]
    fn arm_cancel_arms_a_running_turn_a_stop_retry_or_nothing() {
        let mut running = state(Some(hosted_session()));
        running.session.as_mut().unwrap().turn = Some(ActiveTurn {
            admission_id: "prompt-admission:1".to_string(),
            cancelled: false,
        });
        let CancelOrder::Armed(stop) = arm_cancel_locked("acp-1", &mut running) else {
            panic!("a running turn arms its stop");
        };
        assert_eq!(stop.admission_id.as_deref(), Some("prompt-admission:1"));
        let turn = running.session.as_ref().unwrap().turn.as_ref().unwrap();
        assert!(turn.cancelled);
        assert!(running.session.as_ref().unwrap().cancelling);
        assert!(running.session.as_ref().unwrap().cancel_task.is_some());

        let mut idle = state(Some(hosted_session()));
        assert!(matches!(
            arm_cancel_locked("acp-1", &mut idle),
            CancelOrder::None
        ));
        assert!(idle.session.as_ref().unwrap().turn.is_none());

        let mut failed = state(Some(hosted_session()));
        failed.session.as_mut().unwrap().stop_failure =
            Some(Arc::new(DaemonCommandError::Refused {
                message: Some("boom".to_string()),
            }));
        let CancelOrder::Armed(stop) = arm_cancel_locked("acp-1", &mut failed) else {
            panic!("a stop failure arms the retry");
        };
        assert!(stop.admission_id.is_none());
        assert!(failed.session.as_ref().unwrap().turn.is_none());
        assert!(failed.session.as_ref().unwrap().cancelling);
        assert!(failed.session.as_ref().unwrap().cancel_task.is_some());
    }

    #[test]
    fn a_cancel_while_a_stop_runs_never_arms_a_second_stop() {
        let mut stopping = state(Some(hosted_session()));
        stopping.session.as_mut().unwrap().cancelling = true;
        stopping.session.as_mut().unwrap().turn = Some(ActiveTurn {
            admission_id: "prompt-admission:1".to_string(),
            cancelled: true,
        });
        assert!(matches!(
            arm_cancel_locked("acp-1", &mut stopping),
            CancelOrder::None
        ));
    }
}
