//! Test helpers: models, contexts, tokens, a `fetch` mock, a WebSocket mock
//! (TS `vi.stubGlobal("WebSocket", MockWebSocket)`), and per-test isolation
//! of the module's process-wide caches (TS `afterEach`).

use std::sync::atomic::{AtomicBool, AtomicU16, AtomicUsize, Ordering};
use std::sync::{Arc, LazyLock, Mutex, PoisonError, Weak};

use base64::Engine as _;
use bytes::Bytes;
use eukhe_types::pi_ai::{
    AssistantMessage, AssistantMessageEvent, Context, IndexMap, JsonValue, Message, Model,
    TranscriptContext,
};
use futures::future::BoxFuture;
use futures::StreamExt;
use reqwest::header::HeaderMap;
use serde_json::json;

use super::super::websocket::{
    set_websocket_constructor, WebSocketConstructor, WebSocketData, WebSocketEvent, WebSocketLike,
    WebSocketListener, WebSocketListeners,
};
use super::super::{
    close_openai_codex_websocket_sessions, reset_openai_codex_websocket_debug_stats, test_clock,
};
use crate::types::FetchFunction;
use crate::utils::diagnostics::Thrown;
use crate::utils::event_stream::AssistantMessageEventStream;
use crate::utils::transcript::normalize_context;

static TEST_LOCK: LazyLock<tokio::sync::Mutex<()>> = LazyLock::new(|| tokio::sync::Mutex::new(()));

/// Serializes tests over the module's process-wide caches and resets them
/// on both ends (TS `afterEach`).
pub(crate) struct Isolation {
    _guard: tokio::sync::MutexGuard<'static, ()>,
}

fn reset_globals() {
    set_websocket_constructor(None);
    close_openai_codex_websocket_sessions(None);
    reset_openai_codex_websocket_debug_stats(None);
    test_clock::set_offset_ms(0.0);
}

pub(crate) async fn isolate() -> Isolation {
    let guard = TEST_LOCK.lock().await;
    reset_globals();
    Isolation { _guard: guard }
}

impl Drop for Isolation {
    fn drop(&mut self) {
        reset_globals();
    }
}

/// TS `mockToken(accountId)`.
pub(crate) fn mock_token(account_id: &str) -> String {
    let payload = base64::engine::general_purpose::STANDARD.encode(
        serde_json::to_string(
            &json!({ "https://api.openai.com/auth": { "chatgpt_account_id": account_id } }),
        )
        .expect("serializable"),
    );
    format!("aaa.{payload}.bbb")
}

/// The Codex test model (`gpt-5.1-codex` unless overridden by `patch`).
pub(crate) fn model_with(patch: JsonValue) -> Model {
    let mut model = json!({
        "id": "gpt-5.1-codex",
        "name": "GPT-5.1 Codex",
        "api": "openai-codex-responses",
        "provider": "openai-codex",
        "baseUrl": "https://chatgpt.com/backend-api",
        "reasoning": true,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 400_000,
        "maxTokens": 128_000,
    });
    if let (Some(model), JsonValue::Object(patch)) = (model.as_object_mut(), patch) {
        model.extend(patch);
    }
    serde_json::from_value(model).expect("valid model")
}

pub(crate) fn model() -> Model {
    model_with(json!({}))
}

/// A message from its TS literal.
pub(crate) fn message(value: JsonValue) -> Message {
    serde_json::from_value(value).expect("valid message")
}

pub(crate) fn user(text: &str, timestamp: u64) -> Message {
    message(json!({ "role": "user", "content": text, "timestamp": timestamp }))
}

/// TS `normalizeContext({ systemPrompt, messages, tools })`.
pub(crate) fn context(
    system_prompt: Option<&str>,
    messages: Vec<Message>,
    tools: Option<JsonValue>,
) -> TranscriptContext {
    normalize_context(Context {
        system_prompt: system_prompt.map(str::to_owned),
        messages,
        tools: tools.map(|tools| serde_json::from_value(tools).expect("valid tools")),
    })
}

/// `normalizeContext({ systemPrompt: "You are a helpful assistant.", messages: [user] })`.
pub(crate) fn say_hello() -> TranscriptContext {
    context(
        Some("You are a helpful assistant."),
        vec![user("Say hello", 1)],
        None,
    )
}

pub(crate) fn assistant(message: AssistantMessage) -> Message {
    Message::Assistant(message)
}

/// The concatenated text of the first text block, like the TS
/// `content.find((c) => c.type === "text")?.text`.
pub(crate) fn first_text(message: &AssistantMessage) -> Option<String> {
    let value = serde_json::to_value(message).expect("serializable");
    value["content"]
        .as_array()?
        .iter()
        .find(|block| block["type"] == "text")
        .and_then(|block| block["text"].as_str())
        .map(str::to_owned)
}

/// Collect every event of `stream`.
pub(crate) async fn collect_events(
    stream: &AssistantMessageEventStream,
) -> Vec<AssistantMessageEvent> {
    stream.events().collect().await
}

/// TS `buildSSEPayload`.
pub(crate) fn build_sse_payload(
    status: &str,
    include_done: bool,
    end_turn: Option<bool>,
) -> String {
    let terminal_type = if status == "incomplete" {
        "response.incomplete"
    } else {
        "response.completed"
    };
    let mut response = serde_json::Map::new();
    response.insert("status".into(), json!(status));
    if let Some(end_turn) = end_turn {
        response.insert("end_turn".into(), json!(end_turn));
    }
    response.insert(
        "incomplete_details".into(),
        if status == "incomplete" {
            json!({ "reason": "max_output_tokens" })
        } else {
            JsonValue::Null
        },
    );
    response.insert(
        "usage".into(),
        json!({
            "input_tokens": 5,
            "output_tokens": 3,
            "total_tokens": 8,
            "input_tokens_details": { "cached_tokens": 0 },
        }),
    );
    let mut events = hello_events();
    events.push(json!({ "type": terminal_type, "response": response }));
    let mut lines: Vec<String> = events
        .iter()
        .map(|event| format!("data: {event}"))
        .collect();
    if include_done {
        lines.push("data: [DONE]".to_owned());
    }
    format!("{}\n\n", lines.join("\n\n"))
}

/// The four non-terminal events of a "Hello" text response.
pub(crate) fn hello_events() -> Vec<JsonValue> {
    vec![
        json!({
            "type": "response.output_item.added",
            "item": { "type": "message", "id": "msg_1", "role": "assistant", "status": "in_progress", "content": [] },
        }),
        json!({ "type": "response.content_part.added", "part": { "type": "output_text", "text": "" } }),
        json!({ "type": "response.output_text.delta", "delta": "Hello" }),
        json!({
            "type": "response.output_item.done",
            "item": {
                "type": "message",
                "id": "msg_1",
                "role": "assistant",
                "status": "completed",
                "content": [{ "type": "output_text", "text": "Hello" }],
            },
        }),
    ]
}

/// `data:` frames of `events`, blank-line separated.
pub(crate) fn sse_frames(events: &[JsonValue]) -> String {
    let lines: Vec<String> = events
        .iter()
        .map(|event| format!("data: {event}"))
        .collect();
    format!("{}\n\n", lines.join("\n\n"))
}

/// One captured `fetch` call.
#[derive(Debug, Clone)]
pub(crate) struct FetchCall {
    pub url: String,
    pub headers: HeaderMap,
    pub body: Option<Vec<u8>>,
    pub at: tokio::time::Instant,
}

impl FetchCall {
    /// TS `decodeCodexRequestBody`.
    pub(crate) fn json_body(&self) -> Option<JsonValue> {
        let body = self.body.as_ref()?;
        let bytes = if self
            .headers
            .get("content-encoding")
            .is_some_and(|value| value == "zstd")
        {
            zstd::decode_all(body.as_slice()).expect("zstd body")
        } else {
            body.clone()
        };
        serde_json::from_slice(&bytes).ok()
    }
}

/// Recorded `fetch` calls (TS `vi.fn` mock calls).
#[derive(Debug, Default)]
pub(crate) struct FetchRecorder {
    calls: Mutex<Vec<FetchCall>>,
}

impl FetchRecorder {
    pub(crate) fn calls(&self) -> Vec<FetchCall> {
        self.calls
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone()
    }

    pub(crate) fn count(&self) -> usize {
        self.calls
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .len()
    }
}

/// A `fetch` mock answering each call with `respond(call_index, call)`.
pub(crate) fn mock_fetch(
    respond: impl Fn(usize, &FetchCall) -> BoxFuture<'static, Result<reqwest::Response, Thrown>>
        + Send
        + Sync
        + 'static,
) -> (FetchFunction, Arc<FetchRecorder>) {
    let recorder = Arc::new(FetchRecorder::default());
    let calls = Arc::clone(&recorder);
    let fetch: FetchFunction = Arc::new(move |request: reqwest::Request| {
        let call = FetchCall {
            url: request.url().to_string(),
            headers: request.headers().clone(),
            body: request
                .body()
                .and_then(reqwest::Body::as_bytes)
                .map(<[u8]>::to_vec),
            at: tokio::time::Instant::now(),
        };
        let index = {
            let mut log = calls.calls.lock().unwrap_or_else(PoisonError::into_inner);
            log.push(call.clone());
            log.len() - 1
        };
        respond(index, &call)
    });
    (fetch, recorder)
}

/// An HTTP response for a `fetch` mock.
pub(crate) fn http_response(
    status: u16,
    headers: &[(&str, &str)],
    body: reqwest::Body,
) -> reqwest::Response {
    let mut builder = http::Response::builder().status(status);
    for (name, value) in headers {
        builder = builder.header(*name, *value);
    }
    reqwest::Response::from(builder.body(body).expect("valid response"))
}

/// A complete `text/event-stream` response.
pub(crate) fn sse_response(body: &str) -> reqwest::Response {
    http_response(
        200,
        &[("content-type", "text/event-stream")],
        reqwest::Body::from(body.to_owned()),
    )
}

/// A `text/event-stream` response whose body sends `body` and then stays open.
pub(crate) fn open_sse_response(body: &str) -> reqwest::Response {
    let chunk = Bytes::from(body.to_owned());
    let stream =
        futures::stream::iter([Ok::<_, std::io::Error>(chunk)]).chain(futures::stream::pending());
    http_response(
        200,
        &[("content-type", "text/event-stream")],
        reqwest::Body::wrap_stream(stream),
    )
}

/// Sets the flag when dropped (a cancelled response body).
pub(crate) struct DropFlag(pub Arc<AtomicBool>);

impl Drop for DropFlag {
    fn drop(&mut self) {
        self.0.store(true, Ordering::SeqCst);
    }
}

// ---------------------------------------------------------------------------
// WebSocket mock
// ---------------------------------------------------------------------------

/// What one mock connection does when the transport sends a frame.
pub(crate) enum SendReply {
    /// Dispatch these events asynchronously (TS `queueMicrotask`).
    Events(Vec<WebSocketEvent>),
    /// Fail `send` synchronously.
    Throw(String),
}

/// `message` events carrying `events` as JSON text.
pub(crate) fn messages(events: Vec<JsonValue>) -> SendReply {
    SendReply::Events(
        events
            .into_iter()
            .map(|event| WebSocketEvent::Message(WebSocketData::Text(event.to_string())))
            .collect(),
    )
}

/// Configuration of the mock `WebSocket` class.
pub(crate) struct MockWebSocketConfig {
    /// Dispatch `open` after construction.
    pub open: bool,
    /// Expose `readyState` (OPEN, CLOSED after `close()`).
    pub ready_state: bool,
    /// `send(data)`: connection id (1-based), parsed frame, 1-based index of
    /// the frame across all connections.
    pub on_send: Box<OnSend>,
}

/// `MockWebSocket.send` behavior.
pub(crate) type OnSend = dyn Fn(usize, &JsonValue, usize) -> SendReply + Send + Sync;

/// What the mock class observed.
#[derive(Debug, Default)]
pub(crate) struct MockWebSocketRecorder {
    pub connections: AtomicUsize,
    pub closed: AtomicUsize,
    pub headers: Mutex<Vec<IndexMap<String, String>>>,
    /// `(connection id, frame)` per `send`.
    pub sent: Mutex<Vec<(usize, JsonValue)>>,
}

impl MockWebSocketRecorder {
    pub(crate) fn sent(&self) -> Vec<(usize, JsonValue)> {
        self.sent
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone()
    }

    pub(crate) fn headers(&self) -> Vec<IndexMap<String, String>> {
        self.headers
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone()
    }

    pub(crate) fn connections(&self) -> usize {
        self.connections.load(Ordering::SeqCst)
    }

    pub(crate) fn closed(&self) -> usize {
        self.closed.load(Ordering::SeqCst)
    }
}

struct MockWebSocket {
    id: usize,
    this: Weak<MockWebSocket>,
    listeners: WebSocketListeners,
    ready_state: Option<AtomicU16>,
    config: Arc<MockWebSocketConfig>,
    recorder: Arc<MockWebSocketRecorder>,
}

impl MockWebSocket {
    fn dispatch_later(&self, events: Vec<WebSocketEvent>) {
        let Some(this) = self.this.upgrade() else {
            return;
        };
        tokio::spawn(async move {
            tokio::task::yield_now().await;
            for event in &events {
                this.listeners.dispatch(event);
            }
        });
    }
}

impl WebSocketLike for MockWebSocket {
    fn send(&self, data: String) -> Result<(), Thrown> {
        let frame: JsonValue = serde_json::from_str(&data).expect("JSON frame");
        let index = {
            let mut sent = self
                .recorder
                .sent
                .lock()
                .unwrap_or_else(PoisonError::into_inner);
            sent.push((self.id, frame.clone()));
            sent.len()
        };
        match (self.config.on_send)(self.id, &frame, index) {
            SendReply::Events(events) => {
                self.dispatch_later(events);
                Ok(())
            }
            SendReply::Throw(message) => {
                Err(crate::utils::diagnostics::ErrorObject::new(message).thrown())
            }
        }
    }

    fn close(&self, _code: u16, _reason: &str) {
        self.recorder.closed.fetch_add(1, Ordering::SeqCst);
        if let Some(state) = &self.ready_state {
            state.store(3, Ordering::SeqCst);
        }
    }

    fn ready_state(&self) -> Option<u16> {
        self.ready_state
            .as_ref()
            .map(|state| state.load(Ordering::SeqCst))
    }

    fn listen(&self) -> WebSocketListener {
        self.listeners.subscribe()
    }
}

/// Install the mock `WebSocket` class.
pub(crate) fn mock_websocket(config: MockWebSocketConfig) -> Arc<MockWebSocketRecorder> {
    let recorder = Arc::new(MockWebSocketRecorder::default());
    let config = Arc::new(config);
    let class_recorder = Arc::clone(&recorder);
    let constructor: WebSocketConstructor = Arc::new(move |_url, headers, _env| {
        let id = class_recorder.connections.fetch_add(1, Ordering::SeqCst) + 1;
        class_recorder
            .headers
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(headers);
        let socket = Arc::new_cyclic(|this| MockWebSocket {
            id,
            this: this.clone(),
            listeners: WebSocketListeners::default(),
            ready_state: config.ready_state.then(|| AtomicU16::new(1)),
            config: Arc::clone(&config),
            recorder: Arc::clone(&class_recorder),
        });
        if config.open {
            socket.dispatch_later(vec![WebSocketEvent::Open]);
        }
        Ok(socket as Arc<dyn WebSocketLike>)
    });
    set_websocket_constructor(Some(constructor));
    recorder
}

/// A `fetch` that answers 500 "unexpected fetch" (TS tests that must not fetch).
pub(crate) fn unexpected_fetch() -> (FetchFunction, Arc<FetchRecorder>) {
    mock_fetch(|_, _| {
        Box::pin(async {
            Ok(http_response(
                500,
                &[],
                reqwest::Body::from("unexpected fetch"),
            ))
        })
    })
}
