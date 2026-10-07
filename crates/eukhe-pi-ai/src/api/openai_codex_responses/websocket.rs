//! The WebSocket abstraction the Codex transport runs on (TS
//! `WebSocketLike` plus the runtime `WebSocket` constructor), the connect
//! handshake, and per-request event parsing. Section of the port of
//! `api/openai-codex-responses.ts`.

use std::collections::VecDeque;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::AbortSignal;
use eukhe_types::pi_ai::IndexMap;
use eukhe_types::pi_ai::{JsonValue, ProviderEnv};
use futures::StreamExt;
use reqwest::header::HeaderMap;
use tokio::sync::mpsc;

use crate::utils::diagnostics::{format_thrown_value, ErrorObject, Thrown};
use crate::utils::headers::headers_to_record;
use crate::utils::js::number_to_js_string;
use crate::utils::sleep::timer_duration;

use super::errors::{
    aborted_error, codex_protocol_error, extract_websocket_close_error, extract_websocket_error,
};
use super::events::EventSource;

/// TS `DEFAULT_WEBSOCKET_CONNECT_TIMEOUT_MS`.
pub(crate) const DEFAULT_WEBSOCKET_CONNECT_TIMEOUT_MS: f64 = 15_000.0;

/// `WebSocket.OPEN`.
pub(crate) const READY_STATE_OPEN: u16 = 1;

/// The payload of a `message` event.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum WebSocketData {
    Text(String),
    Binary(Vec<u8>),
}

/// A WebSocket event as the TS listeners see it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum WebSocketEvent {
    Open,
    Message(WebSocketData),
    /// `error`: the event's message (or its nested error's message).
    Error {
        message: Option<String>,
    },
    /// `close`: the close code and reason when present.
    Close {
        code: Option<u16>,
        reason: Option<String>,
        was_clean: Option<bool>,
    },
}

/// Receives the events dispatched while it is alive: TS
/// `addEventListener` for every event type; dropping it removes the
/// listeners.
pub(crate) struct WebSocketListener {
    receiver: mpsc::UnboundedReceiver<WebSocketEvent>,
}

impl WebSocketListener {
    /// The next dispatched event; pending forever once the socket dropped
    /// its listener set (a socket that never fires again).
    pub(crate) async fn next(&mut self) -> WebSocketEvent {
        match self.receiver.recv().await {
            Some(event) => event,
            None => std::future::pending().await,
        }
    }
}

/// Listener registry a socket dispatches to (TS `EventTarget`).
#[derive(Debug, Default)]
pub(crate) struct WebSocketListeners {
    senders: Mutex<Vec<mpsc::UnboundedSender<WebSocketEvent>>>,
}

impl WebSocketListeners {
    /// Add a listener.
    pub(crate) fn subscribe(&self) -> WebSocketListener {
        let (sender, receiver) = mpsc::unbounded_channel();
        self.senders
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(sender);
        WebSocketListener { receiver }
    }

    /// Deliver `event` to every live listener.
    pub(crate) fn dispatch(&self, event: &WebSocketEvent) {
        self.senders
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .retain(|sender| sender.send(event.clone()).is_ok());
    }
}

/// TS `WebSocketLike`: the socket surface the Codex transport uses.
///
/// Implementations deliver `open`, `message`, `error`, and `close` events
/// to the listeners returned by [`WebSocketLike::listen`] in the order the
/// runtime fires them; events fired while nobody listens are lost.
/// `send` follows the WHATWG `WebSocket.send` contract (an error while
/// connecting, silently dropped once closing); `close` never fails.
pub(crate) trait WebSocketLike: Send + Sync {
    /// `socket.send(data)`.
    fn send(&self, data: String) -> Result<(), Thrown>;
    /// `socket.close(code, reason)`.
    fn close(&self, code: u16, reason: &str);
    /// `socket.readyState`, when the runtime exposes it.
    fn ready_state(&self) -> Option<u16>;
    /// `addEventListener` for every event type.
    fn listen(&self) -> WebSocketListener;
}

/// TS `new WebSocket(url, { headers })`: create a connecting socket.
pub(crate) type WebSocketConstructor = Arc<
    dyn Fn(
            &str,
            IndexMap<String, String>,
            Option<&ProviderEnv>,
        ) -> Result<Arc<dyn WebSocketLike>, Thrown>
        + Send
        + Sync,
>;

#[cfg(test)]
static WEBSOCKET_CONSTRUCTOR_OVERRIDE: Mutex<Option<WebSocketConstructor>> = Mutex::new(None);

/// Test hook: TS `vi.stubGlobal("WebSocket", MockWebSocket)`.
#[cfg(test)]
pub(crate) fn set_websocket_constructor(constructor: Option<WebSocketConstructor>) {
    *WEBSOCKET_CONSTRUCTOR_OVERRIDE
        .lock()
        .unwrap_or_else(PoisonError::into_inner) = constructor;
}

/// TS `getWebSocketConstructor`: the runtime socket (with proxy support
/// from the environment, like the Bun branch).
fn get_websocket_constructor() -> WebSocketConstructor {
    #[cfg(test)]
    if let Some(constructor) = WEBSOCKET_CONSTRUCTOR_OVERRIDE
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
    {
        return constructor;
    }
    Arc::new(|url, headers, env| {
        super::tungstenite_socket::TungsteniteWebSocket::connect(url, headers, env)
    })
}

/// TS `closeWebSocketSilently`.
pub(crate) fn close_websocket_silently(socket: &dyn WebSocketLike, code: u16, reason: &str) {
    socket.close(code, reason);
}

/// TS `isWebSocketReusable`: open, or the runtime does not expose a state.
pub(crate) fn is_websocket_reusable(socket: &dyn WebSocketLike) -> bool {
    socket
        .ready_state()
        .is_none_or(|state| state == READY_STATE_OPEN)
}

async fn abort_wait(signal: Option<&AbortSignal>) {
    match signal {
        Some(signal) => signal.cancellation_token().cancelled_owned().await,
        None => std::future::pending().await,
    }
}

async fn timeout_wait(ms: f64) {
    if ms > 0.0 {
        tokio::time::sleep(timer_duration(ms)).await;
    } else {
        std::future::pending::<()>().await;
    }
}

/// TS `connectWebSocket`: open a socket and wait for `open`.
pub(crate) async fn connect_websocket(
    url: &str,
    headers: &HeaderMap,
    signal: Option<&AbortSignal>,
    connect_timeout_ms: Option<f64>,
    env: Option<&ProviderEnv>,
) -> Result<Arc<dyn WebSocketLike>, Thrown> {
    let connect_timeout_ms = connect_timeout_ms.unwrap_or(DEFAULT_WEBSOCKET_CONNECT_TIMEOUT_MS);
    let constructor = get_websocket_constructor();

    let mut ws_headers = headers_to_record(headers);
    // TS deletes the capitalized key from the lowercased record, which
    // removes nothing: the `openai-beta` header stays on the handshake.
    ws_headers.shift_remove("OpenAI-Beta");

    let socket = constructor(url, ws_headers, env)?;
    let mut listener = socket.listen();
    if signal.is_some_and(AbortSignal::aborted) {
        close_websocket_silently(socket.as_ref(), 1000, "aborted");
        return Err(aborted_error());
    }
    let timeout = timeout_wait(connect_timeout_ms);
    tokio::pin!(timeout);
    let outcome = loop {
        tokio::select! {
            biased;
            () = abort_wait(signal) => {
                close_websocket_silently(socket.as_ref(), 1000, "aborted");
                break Err(aborted_error());
            }
            event = listener.next() => match event {
                WebSocketEvent::Open => break Ok(()),
                WebSocketEvent::Error { message } => break Err(extract_websocket_error(message.as_deref())),
                WebSocketEvent::Close { code, reason, .. } => {
                    break Err(extract_websocket_close_error(code, reason.as_deref()));
                }
                WebSocketEvent::Message(_) => {}
            },
            () = &mut timeout => {
                close_websocket_silently(socket.as_ref(), 1000, "connect_timeout");
                break Err(ErrorObject::new(format!(
                    "WebSocket connect timeout after {}ms",
                    number_to_js_string(connect_timeout_ms)
                ))
                .thrown());
            }
        }
    };
    drop(listener);
    outcome.map(|()| socket)
}

/// TS `decodeWebSocketData`.
fn decode_websocket_data(data: WebSocketData) -> String {
    match data {
        WebSocketData::Text(text) => text,
        WebSocketData::Binary(bytes) => String::from_utf8_lossy(&bytes).into_owned(),
    }
}

struct ParseState {
    socket: Arc<dyn WebSocketLike>,
    listener: WebSocketListener,
    signal: Option<AbortSignal>,
    idle_timeout_ms: Option<f64>,
    queue: VecDeque<JsonValue>,
    done: bool,
    failed: Option<Thrown>,
    saw_completion: bool,
}

impl ParseState {
    fn on_event(&mut self, event: WebSocketEvent) {
        match event {
            WebSocketEvent::Message(data) => {
                let text = decode_websocket_data(data);
                if text.is_empty() {
                    return;
                }
                match serde_json::from_str::<JsonValue>(&text) {
                    Ok(parsed) => {
                        let event_type =
                            parsed.get("type").and_then(JsonValue::as_str).unwrap_or("");
                        if matches!(
                            event_type,
                            "response.completed" | "response.done" | "response.incomplete"
                        ) {
                            self.saw_completion = true;
                            self.done = true;
                        }
                        self.queue.push_back(parsed);
                    }
                    Err(cause) => {
                        self.failed = Some(codex_protocol_error(format!(
                            "Invalid Codex WebSocket JSON: {}",
                            format_thrown_value(&crate::utils::diagnostics::thrown(cause))
                        )));
                        self.done = true;
                    }
                }
            }
            WebSocketEvent::Error { message } => {
                self.failed = Some(extract_websocket_error(message.as_deref()));
                self.done = true;
            }
            WebSocketEvent::Close { code, reason, .. } => {
                if self.saw_completion {
                    self.done = true;
                    return;
                }
                if self.failed.is_none() {
                    self.failed = Some(extract_websocket_close_error(code, reason.as_deref()));
                }
                self.done = true;
            }
            WebSocketEvent::Open => {}
        }
    }

    async fn next(&mut self) -> Option<Result<JsonValue, Thrown>> {
        loop {
            if self.signal.as_ref().is_some_and(AbortSignal::aborted) {
                return Some(Err(aborted_error()));
            }
            if let Some(event) = self.queue.pop_front() {
                return Some(Ok(event));
            }
            if self.done {
                if let Some(failed) = self.failed.take() {
                    return Some(Err(failed));
                }
                if !self.saw_completion {
                    return Some(Err(ErrorObject::new(
                        "WebSocket stream closed before response.completed",
                    )
                    .thrown()));
                }
                return None;
            }
            let idle_timeout_ms = self.idle_timeout_ms.unwrap_or(0.0);
            tokio::select! {
                biased;
                () = abort_wait(self.signal.as_ref()) => {
                    self.failed = Some(aborted_error());
                    self.done = true;
                }
                event = self.listener.next() => self.on_event(event),
                () = timeout_wait(idle_timeout_ms) => {
                    let error = ErrorObject::new(format!(
                        "WebSocket idle timeout after {}ms",
                        number_to_js_string(idle_timeout_ms)
                    ))
                    .thrown();
                    self.failed = Some(Arc::clone(&error));
                    self.done = true;
                    close_websocket_silently(self.socket.as_ref(), 1000, "idle_timeout");
                    return Some(Err(error));
                }
            }
        }
    }
}

/// TS `parseWebSocket`: one request's events until the terminal event,
/// an error, a close, an abort, or the idle timeout. The listeners attach
/// when this is called (before the request is sent) and detach when the
/// stream is dropped.
pub(crate) fn parse_websocket(
    socket: Arc<dyn WebSocketLike>,
    signal: Option<AbortSignal>,
    idle_timeout_ms: Option<f64>,
) -> EventSource {
    let listener = socket.listen();
    let state = ParseState {
        socket,
        listener,
        signal,
        idle_timeout_ms,
        queue: VecDeque::new(),
        done: false,
        failed: None,
        saw_completion: false,
    };
    futures::stream::unfold(Some(state), |state| async move {
        let mut state = state?;
        let item = state.next().await?;
        let failed = item.is_err();
        Some((item, (!failed).then_some(state)))
    })
    .boxed()
}
