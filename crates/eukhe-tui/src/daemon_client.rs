//! JSONL daemon client for the interactive UI.
//!
//! Connects to the supervisor's client socket, performs the `daemon_hello`
//! handshake, sends `type: "command"` envelopes, and matches responses by
//! envelope id. Frames that are not responses (session events, list progress,
//! closing notices) are forwarded to the caller through an event channel, so
//! the UI loop can render live session state while requests are in flight.

use std::borrow::Cow;
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use anyhow::{anyhow, Context, Result};
use eukhe_types::daemon::{
    is_session_plane_daemon_command, DaemonCommand, DaemonCommandEnvelope, DaemonCommandFrameType,
    DaemonProtocolInfo, DaemonResponse, SessionEvent, DAEMON_PROTOCOL_NAME,
    DAEMON_PROTOCOL_VERSION,
};
use serde::Deserialize;
use serde_json::value::RawValue;
use serde_json::{Map, Value};
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use tokio::sync::{mpsc, oneshot};

use crate::direct_transport::{
    connect_direct, direct_attach_capabilities, read_session_transport_ticket,
    supervisor_supports_direct, DirectLink, TICKET_TIMEOUT_MS,
};

mod errors;
#[cfg(test)]
mod tests;

use errors::{command_type_debug, response_data_or_error, DaemonConnectFailed, DirectRequestError};
pub use errors::{
    is_connect_failure, is_daemon_rejection, is_daemon_timeout, is_daemon_unreachable,
    is_foreign_daemon, is_kernel_not_running, rejected_provider_unauthenticated, ForeignDaemon,
    ForeignGreeting, RequestRejected,
};

/// Default response timeout (TS `DEFAULT_DAEMON_REQUEST_TIMEOUT_MS`).
pub const DEFAULT_REQUEST_TIMEOUT_MS: u64 = 30_000;
/// Requests whose completion is bounded by the turn itself
/// (`prompt_and_wait`, `wait_for_idle`) use the supervisor's long route
/// timeout so a long turn cannot expire the request.
pub const LONG_RUNNING_REQUEST_TIMEOUT_MS: u64 = 600_000;
/// The socket connect budget of one [`DaemonClient::connect`].
pub(crate) const CONNECT_TIMEOUT_MS: u64 = 3_000;
/// Hello handshake budget. A daemon loading a very large session can take
/// well over the 3s TS default to greet.
pub(crate) const HELLO_TIMEOUT_MS: u64 = 15_000;
/// Connect attempts before a connect/handshake failure surfaces (the
/// fatal error paths the operator hit: "Timed out after 15000ms waiting
/// for the Eukhe daemon handshake" exited their TUI on the FIRST
/// miss at box load). A loaded or restarting daemon usually greets within
/// the retry window; the caller's error path only runs after the last
/// attempt.
pub(crate) const CONNECT_ATTEMPTS: u32 = 3;
/// The first retry's backoff; each further attempt doubles it.
const CONNECT_RETRY_BACKOFF_MS: u64 = 1_000;

/// A non-response frame forwarded to the UI event loop.
#[derive(Debug, Clone)]
pub enum DaemonClientEvent {
    /// `session_event`: one streamed agent/turn event for an attached
    /// session. The frame's `meta.sequence` (the worker's monotonic
    /// event counter -- the same counter the attach cursor rides) rides
    /// along: the cross-view layout handoff's stash keys the LATEST
    /// sequence the run has seen (`view::handoff`), so a turn during
    /// the run advances the stash's key to the value the next attach
    /// reports instead of the run's own stale attach sequence.
    SessionEvent {
        active_session_id: String,
        event: Box<SessionEvent>,
        meta_sequence: u64,
    },
    /// A `session_event` frame whose event this build cannot decode (a
    /// daemon of another build). The client reports it; the event is lost.
    UndecodableSessionEvent {
        active_session_id: String,
        error: String,
    },
    /// `session_closed`: the attached session stopped existing.
    SessionClosed {
        active_session_id: String,
        reason: String,
    },
    /// The direct worker link for `active_session_id` died (the worker
    /// process exited). TS `handleTransportClose` with a direct-transport
    /// loss: "a direct-transport loss is never itself a session loss" --
    /// the UI re-attaches through the supervisor, which respawns the
    /// worker and hands out a fresh peer ticket.
    DirectLinkLost { active_session_id: String },
    /// `session_list_item` progress frame of `list_saved_sessions`: one
    /// saved row as the scan streams it (newest first), tagged with the
    /// request id it belongs to (TS's connection routes the stream to
    /// the originating `listDaemonSavedSessions` callbacks; the agents
    /// view applies only the frames of its own in-flight fetch).
    SessionListItem { session: Value, request_id: String },
    /// `session_list_progress` progress frame of `list_saved_sessions`.
    SessionListProgress { loaded: u64, total: u64 },
    /// `daemon_closing`: the supervisor is going down; `reason` names
    /// the closing (`shutdown` arms the bounded shutdown recovery).
    DaemonClosing { reason: String },
    /// `side_question_event`: one streamed side-question run (the `/btw`
    /// pane tracks the run by its id).
    SideQuestionEvent {
        active_session_id: String,
        event: Value,
    },
    /// `shell_approval`: the session's `bash` tool asks whether one step
    /// may run; the client answers with `answer_shell_approval` (the first
    /// answer of any attached client wins). `agent` names the subagent
    /// that asks, when the question came up from one.
    ShellApproval {
        active_session_id: String,
        request: eukhe_types::shell::ShellApprovalRequest,
        agent: Option<String>,
    },
    /// `roster_update`: live roster deltas for subscribers (the agents
    /// view): changed entries upsert by agent id, `removed` deletes, and
    /// `resync` replaces the whole roster.
    RosterUpdate {
        changed: Vec<Value>,
        removed: Vec<String>,
        resync: bool,
    },
    /// `heartbeats_changed`: the daemon-global broadcast every client sees
    /// when the heartbeat catalog changes (TS `broadcastGlobal`). The
    /// session view refreshes its open `/heartbeats` picker on it.
    HeartbeatsChanged,
    /// `session_binding`: the supervisor rebound a session to a new active
    /// id (a worker replacement) and the id this client holds is
    /// superseded. The session view re-attaches to the current id so its
    /// event routing follows the session.
    SessionBinding {
        previous_active_session_id: String,
        active_session_id: String,
    },
    /// `state_tree_update`: new records of a session's state tree. Only a
    /// connection that sent `subscribe_state_tree` gets it (`eukhe state
    /// --follow`); the interactive views never subscribe.
    StateTreeUpdate {
        active_session_id: String,
        update: eukhe_types::daemon::StateTreeRecords,
    },
}

/// Every field a non-response frame may carry, borrowed raw off the wire
/// bytes in one scan; only the fields the frame's type needs are decoded,
/// each straight into its typed shape.
#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct InboundFrame<'a> {
    #[serde(rename = "type", borrow, default)]
    kind: Option<Cow<'a, str>>,
    #[serde(borrow, default)]
    active_session_id: Option<&'a RawValue>,
    #[serde(borrow, default)]
    previous_active_session_id: Option<&'a RawValue>,
    #[serde(borrow, default)]
    event: Option<&'a RawValue>,
    #[serde(borrow, default)]
    meta: Option<&'a RawValue>,
    #[serde(borrow, default)]
    reason: Option<&'a RawValue>,
    #[serde(borrow, default)]
    session: Option<&'a RawValue>,
    #[serde(borrow, default)]
    id: Option<&'a RawValue>,
    #[serde(borrow, default)]
    loaded: Option<&'a RawValue>,
    #[serde(borrow, default)]
    total: Option<&'a RawValue>,
    #[serde(borrow, default)]
    changed: Option<&'a RawValue>,
    #[serde(borrow, default)]
    removed: Option<&'a RawValue>,
    #[serde(borrow, default)]
    resync: Option<&'a RawValue>,
    #[serde(borrow, default)]
    update: Option<&'a RawValue>,
    #[serde(borrow, default)]
    request: Option<&'a RawValue>,
    #[serde(borrow, default)]
    agent: Option<&'a RawValue>,
}

/// The `meta` fields a session event's sequence rides on.
#[derive(Deserialize)]
struct FrameMeta {
    #[serde(default)]
    sequence: Option<u64>,
    #[serde(default)]
    cursor: Option<FrameCursor>,
}

#[derive(Deserialize)]
struct FrameCursor {
    #[serde(default)]
    sequence: Option<u64>,
}

/// A raw field decoded as `T`; absent or another shape is `None` (a
/// field of the wrong type reads as missing, like the frame's other
/// optional fields).
fn decode<'a, T: Deserialize<'a>>(raw: Option<&'a RawValue>) -> Option<T> {
    serde_json::from_str(raw?.get()).ok()
}

fn decode_string(raw: Option<&RawValue>) -> String {
    decode(raw).unwrap_or_default()
}

/// One non-response frame, parsed from a supervisor JSONL line or a direct
/// worker frame payload (both carry the same `DaemonOutbound` shapes).
pub(crate) fn client_event_from_json(json: &[u8]) -> Option<DaemonClientEvent> {
    client_event_from_frame(&serde_json::from_slice(json).ok()?)
}

fn client_event_from_frame(frame: &InboundFrame<'_>) -> Option<DaemonClientEvent> {
    match frame.kind.as_deref().unwrap_or_default() {
        "session_event" => {
            let active_session_id = decode_string(frame.active_session_id);
            let Some(event) = frame.event else {
                return Some(DaemonClientEvent::UndecodableSessionEvent {
                    active_session_id,
                    error: "the frame carries no event".to_string(),
                });
            };
            Some(match serde_json::from_str::<SessionEvent>(event.get()) {
                Ok(event) => DaemonClientEvent::SessionEvent {
                    active_session_id,
                    event: Box::new(event),
                    meta_sequence: decode::<FrameMeta>(frame.meta)
                        .and_then(|meta| {
                            meta.sequence
                                .or_else(|| meta.cursor.and_then(|cursor| cursor.sequence))
                        })
                        .unwrap_or_default(),
                },
                Err(error) => DaemonClientEvent::UndecodableSessionEvent {
                    active_session_id,
                    error: error.to_string(),
                },
            })
        }
        "session_closed" => Some(DaemonClientEvent::SessionClosed {
            active_session_id: decode_string(frame.active_session_id),
            reason: decode_string(frame.reason),
        }),
        "side_question_event" => Some(DaemonClientEvent::SideQuestionEvent {
            active_session_id: decode_string(frame.active_session_id),
            event: decode(frame.event).unwrap_or(Value::Null),
        }),
        // A question that does not decode is dropped: this client leaves
        // it to the others (or to the detach, a denial).
        "shell_approval" => decode(frame.request).map(|request| DaemonClientEvent::ShellApproval {
            active_session_id: decode_string(frame.active_session_id),
            request,
            agent: decode(frame.agent),
        }),
        "session_list_item" => Some(DaemonClientEvent::SessionListItem {
            session: decode(frame.session).unwrap_or(Value::Null),
            request_id: decode_string(frame.id),
        }),
        "session_list_progress" => Some(DaemonClientEvent::SessionListProgress {
            loaded: decode(frame.loaded).unwrap_or(0),
            total: decode(frame.total).unwrap_or(0),
        }),
        "daemon_closing" => Some(DaemonClientEvent::DaemonClosing {
            reason: decode_string(frame.reason),
        }),
        "roster_update" => Some(DaemonClientEvent::RosterUpdate {
            changed: decode(frame.changed).unwrap_or_default(),
            removed: decode::<Vec<Value>>(frame.removed)
                .unwrap_or_default()
                .into_iter()
                .filter_map(|id| match id {
                    Value::String(id) => Some(id),
                    Value::Null
                    | Value::Bool(_)
                    | Value::Number(_)
                    | Value::Array(_)
                    | Value::Object(_) => None,
                })
                .collect(),
            resync: decode(frame.resync) == Some(true),
        }),
        "heartbeats_changed" => Some(DaemonClientEvent::HeartbeatsChanged),
        // A frame whose records do not decode is dropped: the next frame
        // starts after a cursor the follower lacks, and it re-subscribes.
        "state_tree_update" => {
            decode(frame.update).map(|update| DaemonClientEvent::StateTreeUpdate {
                active_session_id: decode_string(frame.active_session_id),
                update,
            })
        }
        "session_binding" => Some(DaemonClientEvent::SessionBinding {
            previous_active_session_id: decode_string(frame.previous_active_session_id),
            active_session_id: decode_string(frame.active_session_id),
        }),
        _ => None,
    }
}

/// Connection state shared between the request side and the reader task.
#[derive(Default)]
pub(crate) struct Shared {
    /// Pending requests keyed by envelope id. `Ok` is a daemon answer
    /// (including a `success: false` refusal); `Err` is a transport
    /// failure -- the two must stay distinguishable, because a refusal is
    /// recoverable UI data while a dead connection is fatal.
    pending: Mutex<HashMap<String, oneshot::Sender<Result<DaemonResponse, anyhow::Error>>>>,
    /// Direct links connected so far: link `n` owns the request-id
    /// namespace `direct_<n>_` in `pending`.
    pub(crate) next_direct_link: AtomicU64,
}

impl Shared {
    pub(crate) fn resolve(&self, id: &str, response: DaemonResponse) -> bool {
        let mut pending = self.pending.lock().unwrap();
        pending
            .remove(id)
            .is_some_and(|tx| tx.send(Ok(response)).is_ok())
    }

    /// Fail every pending request whose id starts with `prefix` with a
    /// transport error: the connection that carried them died.
    ///
    /// This is what keeps a dead supervisor or worker from leaving the UI
    /// waiting out the full request timeout -- the exit-hang class of bugs:
    /// the abort was accepted, but the client then hung on a request whose
    /// socket peer was already gone. The reader task of each connection
    /// calls this when its socket closes (supervisor reader fails the
    /// `daemon_`-routed requests, a direct worker pump only its own link's
    /// `direct_<n>_` ones, so a live link keeps serving its own in-flight
    /// requests even when a link it replaced reaches EOF late). The
    /// failure resolves on the `Err` half of the channel -- never as a
    /// synthetic response -- so a dead connection can never be mistaken
    /// for a daemon refusal.
    pub(crate) fn fail_pending(&self, prefix: &str, error: &str) {
        let mut pending = self.pending.lock().unwrap();
        let dead: Vec<String> = pending
            .keys()
            .filter(|id| id.starts_with(prefix))
            .cloned()
            .collect();
        for id in dead {
            if let Some(tx) = pending.remove(&id) {
                let _ = tx.send(Err(anyhow!(error.to_string())));
            }
        }
    }
}

/// A live connection to the daemon supervisor socket, optionally upgraded
/// with a direct worker link (session-plane commands and events go straight
/// to the session process; the supervisor stays the control plane).
///
/// Cheap to clone: clones share the same socket, pending-request table, and
/// direct link, so a background request (the Ctrl+C abort) races a live
/// client exactly.
#[derive(Clone)]
pub struct DaemonClient {
    socket_path: PathBuf,
    client_id: String,
    protocol: DaemonProtocolInfo,
    /// Full `daemon_hello` frame (schema id, app version, capabilities).
    hello: Value,
    next_request_id: Arc<AtomicU64>,
    shared: Arc<Shared>,
    writer: mpsc::UnboundedSender<String>,
    /// Direct-transport state (retained event sender + live worker link),
    /// one pointer so this struct stays small.
    direct: std::sync::Arc<crate::direct_transport::DirectState>,
    /// The supervisor reader's death watch (see `reader_dead`).
    reader_dead_rx: tokio::sync::watch::Receiver<bool>,
}

impl DaemonClient {
    /// Connect to `socket_path`, complete the hello handshake, and return the
    /// client plus the event receiver. The event receiver must be polled or
    /// the reader task stalls once the channel's buffer fills.
    ///
    /// # Errors
    ///
    /// Returns `Err` when the transport connect times out or fails, the
    /// hello handshake times out or the connection closes first, or the
    /// daemon speaks an unknown protocol.
    pub async fn connect(
        socket_path: &Path,
    ) -> Result<(Self, mpsc::UnboundedReceiver<DaemonClientEvent>)> {
        Self::open(socket_path, HELLO_TIMEOUT_MS, false).await
    }

    /// [`Self::connect`] for discovery probes (TS `probeDaemon`): the
    /// handshake waits `hello_timeout_ms`, and a hello naming another
    /// protocol is kept (envelopes echo the daemon's own protocol name
    /// and version) instead of failing with [`ForeignDaemon`]. An
    /// unparseable first line still fails with [`ForeignDaemon`].
    ///
    /// # Errors
    ///
    /// As [`Self::connect`], minus the foreign-protocol refusal.
    pub async fn connect_probe(
        socket_path: &Path,
        hello_timeout_ms: u64,
    ) -> Result<(Self, mpsc::UnboundedReceiver<DaemonClientEvent>)> {
        Self::open(socket_path, hello_timeout_ms, true).await
    }

    async fn open(
        socket_path: &Path,
        hello_timeout_ms: u64,
        keep_foreign: bool,
    ) -> Result<(Self, mpsc::UnboundedReceiver<DaemonClientEvent>)> {
        let connect = tokio::time::timeout(
            Duration::from_millis(CONNECT_TIMEOUT_MS),
            eukhe_types::platform::transport::connect_transport(socket_path),
        )
        .await
        .map_err(|_| {
            anyhow::Error::new(DaemonConnectFailed(format!(
                "Timed out after {CONNECT_TIMEOUT_MS}ms connecting to the Eukhe daemon. Socket: {}.",
                socket_path.display()
            )))
        })?
        .with_context(|| {
            DaemonConnectFailed(format!(
                "Failed to connect to the Eukhe daemon. Socket: {}.",
                socket_path.display()
            ))
        })?;

        let (reader_half, writer_half) = connect.split();
        let (line_tx, mut line_rx) = mpsc::unbounded_channel::<String>();
        let (event_tx, event_rx) = mpsc::unbounded_channel::<DaemonClientEvent>();
        let retained_event_tx = event_tx.clone();
        // The supervisor reader's death signal: the retained event sender
        // keeps the event channel open after the reader exits (direct
        // reader pumps may still feed it), so a channel close can never
        // observe a supervisor socket loss -- the watch is the observable
        // signal the UI loop arms its reconnect driver on.
        let (reader_dead_tx, reader_dead_rx) = tokio::sync::watch::channel(false);
        let (hello_tx, hello_rx) = oneshot::channel::<std::result::Result<Value, String>>();
        let shared = Arc::new(Shared::default());
        let reader_shared = Arc::clone(&shared);

        // Writer task: serializes one line per write.
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

        // Reader task: dispatch every inbound line. The handle is kept so
        // the handshake-failure paths can abort it: a daemon that accepts
        // the socket but never greets must not leave a blocked reader task
        // (and its socket halves) behind per retry attempt.
        let reader_task = tokio::spawn(async move {
            let mut reader = BufReader::new(reader_half);
            let mut line = String::new();
            let mut hello_tx = Some(hello_tx);
            loop {
                line.clear();
                match reader.read_line(&mut line).await {
                    Ok(0) | Err(_) => break,
                    Ok(_) => {}
                }
                let trimmed = line.trim();
                let Ok(frame) = serde_json::from_str::<InboundFrame>(trimmed) else {
                    // A first line that is not a JSON frame is no hello at
                    // all: a foreign server holds the socket.
                    if !trimmed.is_empty() {
                        if let Some(tx) = hello_tx.take() {
                            let _ = tx.send(Err(trimmed.chars().take(120).collect()));
                        }
                    }
                    continue;
                };
                match frame.kind.as_deref().unwrap_or_default() {
                    "daemon_hello" => {
                        let Some(tx) = hello_tx.take() else { continue };
                        let _ = tx.send(
                            serde_json::from_str(trimmed)
                                .map_err(|_| trimmed.chars().take(120).collect()),
                        );
                    }
                    "response" => {
                        if let Ok(response) = serde_json::from_str::<DaemonResponse>(trimmed) {
                            let id = response.id.clone().unwrap_or_default();
                            reader_shared.resolve(&id, response);
                        }
                    }
                    _ => {
                        if let Some(event) = client_event_from_frame(&frame) {
                            let _ = event_tx.send(event);
                        }
                    }
                }
            }
            // The supervisor socket closed: every supervisor-routed request
            // in flight fails now instead of riding out its timeout, and
            // the death watch wakes the UI loop's reconnect driver.
            let _ = reader_dead_tx.send(true);
            reader_shared.fail_pending("daemon_", "the daemon connection closed");
        });

        // Hello handshake: the supervisor sends daemon_hello immediately on
        // connect (TS `waitForHello`). Every failure path aborts the
        // blocked reader task so a failed attempt leaks no socket halves.
        let hello = tokio::time::timeout(Duration::from_millis(hello_timeout_ms), hello_rx)
            .await
            .map_err(|_| {
                reader_task.abort();
                anyhow!(
                    "Timed out after {hello_timeout_ms}ms waiting for the Eukhe daemon handshake. Socket: {}.",
                    socket_path.display()
                )
            })?
            .map_err(|_| {
                reader_task.abort();
                anyhow!("the daemon connection closed before the handshake")
            })?
            .map_err(|line| {
                reader_task.abort();
                anyhow::Error::new(ForeignDaemon {
                    socket_path: socket_path.to_path_buf(),
                    greeting: ForeignGreeting::Unparseable(line),
                })
            })?;
        let protocol = hello
            .get("protocol")
            .cloned()
            .and_then(|p| serde_json::from_value::<DaemonProtocolInfo>(p).ok())
            .unwrap_or(DaemonProtocolInfo {
                name: DAEMON_PROTOCOL_NAME.to_string(),
                version: DAEMON_PROTOCOL_VERSION,
            });
        let protocol = if protocol.name == DAEMON_PROTOCOL_NAME {
            // Envelope protocol version: the shared minimum (TS `request`).
            DaemonProtocolInfo {
                name: protocol.name,
                version: protocol.version.min(DAEMON_PROTOCOL_VERSION),
            }
        } else if keep_foreign {
            protocol
        } else {
            reader_task.abort();
            return Err(anyhow::Error::new(ForeignDaemon {
                socket_path: socket_path.to_path_buf(),
                greeting: ForeignGreeting::Protocol(protocol.name),
            }));
        };

        Ok((
            DaemonClient {
                socket_path: socket_path.to_path_buf(),
                client_id: format!("daemon-tui:{}", std::process::id()),
                protocol,
                hello,
                next_request_id: Arc::new(AtomicU64::new(0)),
                shared,
                writer: line_tx,
                direct: std::sync::Arc::new(crate::direct_transport::DirectState::new(
                    retained_event_tx,
                )),
                reader_dead_rx,
            },
            event_rx,
        ))
    }

    /// A fresh receiver for the supervisor reader's death watch: fires
    /// (`true`) when the supervisor socket's reader task ends -- a daemon
    /// hiccup the UI loop's reconnect driver observes (the event channel
    /// itself stays open: the retained sender keeps it alive for direct
    /// reader pumps). Poll it with `watch::Receiver::changed`.
    #[must_use]
    pub fn reader_dead(&self) -> tokio::sync::watch::Receiver<bool> {
        self.reader_dead_rx.clone()
    }

    #[must_use]
    pub fn socket_path(&self) -> &Path {
        &self.socket_path
    }

    /// [`Self::connect`] with bounded retries and doubling backoff: a
    /// missed hello (a loaded daemon mid-fanout, a supervisor coming up
    /// after a restart) is a hiccup, not a fatal condition -- the one-shot
    /// connect cost the operator their TUI twice on 2026-09-24 ("Timed
    /// out after 15000ms waiting for the Eukhe daemon handshake").
    /// The caller's error path (fatal exit or view fallback) only runs
    /// after the last attempt.
    ///
    /// # Errors
    ///
    /// Returns the last attempt's [`Self::connect`] error once the
    /// bounded retries are exhausted.
    pub async fn connect_with_retry(
        socket_path: &Path,
    ) -> Result<(Self, mpsc::UnboundedReceiver<DaemonClientEvent>)> {
        let mut delay = CONNECT_RETRY_BACKOFF_MS;
        for attempt in 1..=CONNECT_ATTEMPTS {
            match DaemonClient::connect(socket_path).await {
                Ok(pair) => return Ok(pair),
                Err(error) => {
                    if attempt == CONNECT_ATTEMPTS {
                        return Err(error);
                    }
                    tokio::time::sleep(Duration::from_millis(delay)).await;
                    delay = delay.saturating_mul(2);
                }
            }
        }
        unreachable!("the attempt range is non-empty")
    }

    /// Protocol identity negotiated in the hello handshake.
    #[must_use]
    pub fn protocol(&self) -> &DaemonProtocolInfo {
        &self.protocol
    }

    /// The full `daemon_hello` frame the supervisor sent on connect.
    /// Whether the daemon's `daemon_hello` advertised `capability` (TS
    /// `supportsServerCapability`): capability-gated commands fall back to
    /// their older shape without it.
    pub fn supports_server_capability(&self, capability: &str) -> bool {
        self.hello
            .get("serverCapabilities")
            .and_then(Value::as_array)
            .is_some_and(|capabilities| {
                capabilities
                    .iter()
                    .any(|entry| entry.as_str() == Some(capability))
            })
    }

    #[must_use]
    pub fn hello(&self) -> &Value {
        &self.hello
    }

    /// The daemon's build: its hello `appVersion` and `runtime.buildId`
    /// (empty when the hello does not report them). A hello without a
    /// `runtime.buildId` whose `appVersion` is absent or this build's
    /// version has nothing to compare: it reads as this build.
    #[must_use]
    pub fn daemon_build(&self) -> crate::daemon_build::Build<'_> {
        let version = self.hello.get("appVersion").and_then(Value::as_str);
        let id = self
            .hello
            .get("runtime")
            .and_then(|runtime| runtime.get("buildId"))
            .and_then(Value::as_str);
        match (version, id) {
            (None, None) => crate::daemon_build::Build::THIS,
            (Some(version), None) if version == eukhe_build_info::VERSION => {
                crate::daemon_build::Build::THIS
            }
            (version, id) => crate::daemon_build::Build {
                version: version.unwrap_or_default(),
                id: id.unwrap_or_default(),
            },
        }
    }

    /// Send one command envelope and wait for the matching response, using
    /// the TS default timeout for the command class.
    ///
    /// # Errors
    ///
    /// Returns `Err` like [`Self::request_with_timeout`]: the frame
    /// cannot be sent, the connection dies before the response, or the
    /// command-class timeout elapses.
    pub async fn request(&self, command: DaemonCommand) -> Result<DaemonResponse> {
        let timeout_ms = match &command {
            DaemonCommand::PromptAndWait { .. } | DaemonCommand::WaitForIdle { .. } => {
                LONG_RUNNING_REQUEST_TIMEOUT_MS
            }
            _ => DEFAULT_REQUEST_TIMEOUT_MS,
        };
        self.request_with_timeout(command, timeout_ms).await
    }

    /// Send one command envelope and wait up to `timeout_ms` for the response.
    ///
    /// Session-plane commands for the direct link's session go straight to
    /// the session worker socket; everything else goes to the supervisor.
    /// A direct link that died before the request was written falls back to
    /// the supervisor (the request never reached the worker); a request that
    /// was sent and timed out surfaces the error instead of retrying, so a
    /// prompt can never execute twice.
    ///
    /// # Errors
    ///
    /// Returns `Err` when the frame cannot be written (the connection is
    /// closed), the reader dies before resolving, or the timeout elapses;
    /// a direct frame that never reached the worker falls back to the
    /// supervisor instead of failing.
    pub async fn request_with_timeout(
        &self,
        command: DaemonCommand,
        timeout_ms: u64,
    ) -> Result<DaemonResponse> {
        if let Some(link) = self.direct_link_for(&command) {
            let sequence = self.next_request_id.fetch_add(1, Ordering::SeqCst) + 1;
            let id = format!("{}{sequence}", link.request_prefix);
            match self.request_direct(&link, &command, &id, timeout_ms).await {
                Ok(response) => return Ok(response),
                Err(DirectRequestError::NotSent) => {
                    // The link was dead before the frame was queued; the
                    // request never reached the worker, so supervisor
                    // routing is safe.
                    self.direct.drop_link();
                }
                Err(DirectRequestError::Wait(error)) => return Err(error),
            }
        }
        self.request_supervisor(command, timeout_ms).await
    }

    /// Send one command envelope to the supervisor, bypassing any direct
    /// worker link, and require `success: true`. The supervisor-owned arms
    /// (`abort_compaction`) must reach the supervisor even when a direct
    /// link serves the session: the direct link IS the wedged worker in
    /// the case the supervisor arm exists for.
    ///
    /// # Errors
    ///
    /// Returns `Err` when the supervisor request fails or times out, or
    /// the response carries `success: false` (the daemon error string
    /// surfaces).
    pub async fn request_ok_via_supervisor(&self, command: DaemonCommand) -> Result<Value> {
        let name = command_type_debug(&command);
        let response = self
            .request_supervisor(command, DEFAULT_REQUEST_TIMEOUT_MS)
            .await?;
        response_data_or_error(&name, response)
    }

    /// The supervisor leg of [`Self::request_with_timeout`]: one JSONL
    /// envelope on the supervisor connection.
    async fn request_supervisor(
        &self,
        command: DaemonCommand,
        timeout_ms: u64,
    ) -> Result<DaemonResponse> {
        let id = format!(
            "daemon_{}",
            self.next_request_id.fetch_add(1, Ordering::SeqCst) + 1
        );
        self.request_supervisor_with_id(command, &id, timeout_ms)
            .await
    }

    /// The refusal for a supervisor reader that already ended: its
    /// close-time failure pass has run (or is imminent), so nothing can
    /// ever answer a request registered now -- TS `requestWire` refuses
    /// a destroyed socket the same way.
    fn dead_reader_error(&self) -> anyhow::Error {
        anyhow!(
            "the daemon connection is closed. Socket: {}.",
            self.socket_path.display()
        )
    }

    /// One JSONL envelope on the supervisor connection, under the caller's
    /// own envelope id: the streamed `session_list_item` frames of
    /// `list_saved_sessions` carry it, so the caller can attribute the
    /// catalog stream to its own fetch (TS's connection routes the
    /// stream to the originating `listDaemonSavedSessions` callbacks).
    /// The id must start with `daemon_` - the supervisor reader's
    /// socket-close failure pass filters by that prefix.
    ///
    /// # Errors
    ///
    /// Returns `Err` when the envelope cannot be serialized, the writer
    /// send fails (the connection is already closed), the supervisor
    /// reader has already died (nothing can ever resolve the request),
    /// the reader task dies before resolving, or the timeout elapses.
    ///
    /// # Panics
    ///
    /// Panics when the shared pending-request mutex is poisoned (a
    /// thread panicked while holding it).
    pub async fn request_supervisor_with_id(
        &self,
        command: DaemonCommand,
        id: &str,
        timeout_ms: u64,
    ) -> Result<DaemonResponse> {
        if *self.reader_dead_rx.borrow() {
            return Err(self.dead_reader_error());
        }
        let id = id.to_string();
        let envelope = DaemonCommandEnvelope {
            frame_type: DaemonCommandFrameType::Command,
            id: id.clone(),
            protocol: self.protocol.clone(),
            client_id: Some(self.client_id.clone()),
            command,
        };
        let line = serde_json::to_string(&envelope)?;
        let (tx, rx) = oneshot::channel::<Result<DaemonResponse>>();
        self.shared.pending.lock().unwrap().insert(id.clone(), tx);
        // The reader runs on another worker: it can die (and run its
        // failure sweep) between the entry check and this registration,
        // and the writer channel outlives the reader's EOF -- an entry
        // the sweep missed would ride the caller's whole timeout.
        // Re-check after inserting: a death the sweep already served
        // resolves the oneshot on the Err half, a death it missed is
        // caught here.
        if *self.reader_dead_rx.borrow() {
            self.shared.pending.lock().unwrap().remove(&id);
            return Err(self.dead_reader_error());
        }
        self.writer
            .send(line)
            .map_err(|_| anyhow!("the daemon connection is closed"))?;
        match tokio::time::timeout(Duration::from_millis(timeout_ms), rx).await {
            // The daemon answered (its response says whether it was happy).
            Ok(Ok(result)) => result,
            // The reader task died before resolving this request: the
            // connection was already gone.
            Ok(Err(_)) => Err(anyhow!(
                "Connection to the Eukhe daemon closed. Socket: {}.",
                self.socket_path.display()
            )),
            Err(_) => {
                self.shared.pending.lock().unwrap().remove(&id);
                Err(anyhow!(
                    "Timed out after {timeout_ms}ms waiting for the Eukhe daemon response. Socket: {}.",
                    self.socket_path.display()
                ))
            }
        }
    }

    /// Send a command and require `success: true`, surfacing the daemon error
    /// string otherwise.
    ///
    /// # Errors
    ///
    /// Returns `Err` when [`Self::request`] fails or the response
    /// carries `success: false` (the daemon error string surfaces).
    pub async fn request_ok(&self, command: DaemonCommand) -> Result<Value> {
        let name = command_type_debug(&command);
        let response = self.request(command).await?;
        response_data_or_error(&name, response)
    }

    /// Whether a session-plane command for the direct link's session may
    /// travel over the direct link (TS `servesDirect`).
    /// The live direct link that may serve `command` (TS `servesDirect`):
    /// the command must be session-plane and address the link's session.
    fn direct_link_for(&self, command: &DaemonCommand) -> Option<DirectLink> {
        let link = self.direct.live_link()?;
        let command_type = command_type_debug(command);
        if !is_session_plane_daemon_command(&command_type) {
            return None;
        }
        let session = serde_json::to_value(command).ok().and_then(|payload| {
            payload
                .get("activeSessionId")
                .and_then(serde_json::Value::as_str)
                .map(str::to_string)
        });
        (session.as_deref() == Some(link.active_session_id.as_str())).then_some(link)
    }

    /// One request over the direct worker link.
    async fn request_direct(
        &self,
        link: &DirectLink,
        command: &DaemonCommand,
        id: &str,
        timeout_ms: u64,
    ) -> std::result::Result<DaemonResponse, DirectRequestError> {
        let payload = self
            .direct_command_payload(command)
            .map_err(|_| DirectRequestError::NotSent)?;
        let frame = eukhe_types::daemon::framing::encode_private_frame(
            &serde_json::json!({
                "kind": "command",
                "requestId": id,
                "commandType": command_type_debug(command),
            }),
            &serde_json::to_vec(&payload).unwrap_or_default(),
            eukhe_types::daemon::framing::DEFAULT_PRIVATE_FRAME_LIMITS,
        )
        .map_err(|_| DirectRequestError::NotSent)?;
        let (reply_tx, reply_rx) = oneshot::channel::<Result<DaemonResponse>>();
        self.shared
            .pending
            .lock()
            .unwrap()
            .insert(id.to_string(), reply_tx);
        if !link.send(frame) {
            self.shared.pending.lock().unwrap().remove(id);
            return Err(DirectRequestError::NotSent);
        }
        match tokio::time::timeout(Duration::from_millis(timeout_ms), reply_rx).await {
            // The worker answered (its response says whether it was happy).
            Ok(Ok(Ok(response))) => Ok(response),
            // The worker link died: a transport failure, never a refusal.
            Ok(Ok(Err(error))) => Err(DirectRequestError::Wait(error)),
            Ok(Err(_)) => Err(DirectRequestError::Wait(anyhow!(
                "the direct session connection closed. Socket: {}.",
                link.socket_path
            ))),
            Err(_) => {
                self.shared.pending.lock().unwrap().remove(id);
                Err(DirectRequestError::Wait(anyhow!(
                    "Timed out after {timeout_ms}ms waiting for the session response. Socket: {}.",
                    link.socket_path
                )))
            }
        }
    }

    /// The wire payload for a direct session command: the command itself,
    /// stamped with this client's id (the supervisor stamps it on the routed
    /// path) and, for attach, the slim-snapshot capability set the
    /// supervisor's routed attach uses, so both paths return identical
    /// attach results.
    fn direct_command_payload(&self, command: &DaemonCommand) -> Result<Value> {
        let mut payload = serde_json::to_value(command)?;
        if let Some(object) = payload.as_object_mut() {
            object.insert("clientId".to_string(), serde_json::json!(self.client_id));
            if matches!(command, DaemonCommand::Attach { .. }) {
                object.insert(
                    "capabilities".to_string(),
                    serde_json::json!(direct_attach_capabilities()),
                );
            }
        }
        Ok(payload)
    }

    /// The active direct link's session, when this client upgraded.
    #[must_use]
    pub fn direct_session_id(&self) -> Option<String> {
        self.direct.session_id()
    }

    /// Drop the direct link and keep plain supervisor routing (TS
    /// `fallbackToSupervisor`).
    pub fn drop_direct(&self) {
        self.direct.drop_link();
    }

    /// Upgrade this connection with a direct worker link for
    /// `active_session_id` (TS `createDaemonSessionTransport`): request a
    /// ticket from the supervisor, validate it, connect to the worker
    /// socket, and authenticate with the single-use grant. Every failure
    /// returns `Ok(false)` and leaves the plain supervisor connection in
    /// place.
    ///
    /// # Errors
    ///
    /// Never returns `Err`: every failure path (an unsupported
    /// supervisor, a failed or refused ticket request, an invalid
    /// ticket, or a failed worker connect) returns `Ok(false)` and keeps
    /// the plain supervisor connection.
    pub async fn upgrade_direct(&self, active_session_id: &str) -> Result<bool> {
        if !supervisor_supports_direct(&self.hello) {
            return Ok(false);
        }
        if self.direct_session_id().as_deref() == Some(active_session_id) {
            return Ok(true);
        }
        self.drop_direct();
        let Ok(ticket_response) = self
            .request_with_timeout(
                DaemonCommand::GetDirectWorkerTransport {
                    id: None,
                    active_session_id: active_session_id.to_string(),
                    rest: Map::default(),
                },
                TICKET_TIMEOUT_MS,
            )
            .await
        else {
            return Ok(false);
        };
        if !ticket_response.success {
            return Ok(false);
        }
        let Some(data) = ticket_response.data else {
            return Ok(false);
        };
        let Ok(ticket) = read_session_transport_ticket(&data, active_session_id) else {
            return Ok(false);
        };
        let Some(event_tx) = self.direct.event_sender() else {
            return Ok(false);
        };
        match connect_direct(&ticket, Arc::clone(&self.shared), event_tx).await {
            Ok(link) => {
                self.direct.set_link(link);
                Ok(true)
            }
            Err(_) => Ok(false),
        }
    }

    /// Close the connection; pending requests fail with the closed error.
    pub fn close(&self) {
        self.direct.take_event_sender();
        self.drop_direct();
        let _ = self.writer.send(String::new());
    }

    /// Dispose the connection outright: like [`Self::close`], but the
    /// writer sender is DROPPED too (a replacement dummy takes its
    /// place), so the writer task finishes its queue, shuts the socket's
    /// write half down, and the reader EOFs -- a half-attached client is
    /// never left running through the reconnect window. The failure
    /// paths that replace an installed client use this (the plain
    /// `close` keeps the writer alive for teardown-order cases).
    pub fn hard_close(&mut self) {
        self.direct.take_event_sender();
        self.drop_direct();
        let (replacement, _) = mpsc::unbounded_channel::<String>();
        let writer = std::mem::replace(&mut self.writer, replacement);
        let _ = writer.send(String::new());
    }
}
