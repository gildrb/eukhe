//! Test fixtures shared by the Google API module tests.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_types::pi_ai::{
    Context, JsonValue, Model, ThinkingBudgets, ThinkingLevel, TranscriptContext,
};
use serde_json::json;
use tokio::io::{AsyncReadExt, AsyncWriteExt};

use crate::types::{OnPayload, SimpleStreamOptions};
use crate::utils::diagnostics::ErrorObject;
use crate::utils::event_stream::AssistantMessageEventStream;
use crate::utils::transcript::normalize_context;

/// A chat model from its TS object-literal fields.
pub(crate) fn model(fields: &JsonValue) -> Model {
    let mut object = json!({
        "name": fields["id"],
        "reasoning": true,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 128_000,
        "maxTokens": 8192
    });
    for (key, value) in fields.as_object().into_iter().flatten() {
        object[key] = value.clone();
    }
    serde_json::from_value(object).expect("model")
}

/// A built-in catalog model (TS `getModel(provider, id)`).
pub(crate) fn builtin_model(provider: &str, id: &str) -> Model {
    crate::providers::all::get_builtin_model(provider, id).expect("builtin model")
}

/// `normalizeContext(context)` of a TS context literal.
pub(crate) fn context(value: &JsonValue) -> TranscriptContext {
    let context: Context = serde_json::from_value(value.clone()).expect("context");
    normalize_context(context)
}

/// An assistant message literal with zero usage.
pub(crate) fn assistant(api: &str, provider: &str, model: &str, content: &JsonValue) -> JsonValue {
    json!({
        "role": "assistant",
        "content": content,
        "api": api,
        "provider": provider,
        "model": model,
        "usage": {
            "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
            "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 }
        },
        "stopReason": "toolUse",
        "timestamp": 0
    })
}

/// A single user "hello" message context.
pub(crate) fn hello_context() -> TranscriptContext {
    context(&json!({ "messages": [{ "role": "user", "content": "hello", "timestamp": 0 }] }))
}

/// An `onPayload` hook that stores the payload and throws
/// `payload captured` (the thinking-level-map capture helpers).
pub(crate) fn capturing_on_payload() -> (OnPayload<Model>, Arc<Mutex<Option<JsonValue>>>) {
    let captured = Arc::new(Mutex::new(None));
    let sink = Arc::clone(&captured);
    let hook: OnPayload<Model> = Arc::new(move |payload, _model| {
        *sink.lock().unwrap_or_else(PoisonError::into_inner) = Some(payload);
        Box::pin(async { Err(ErrorObject::new("payload captured").thrown()) })
    });
    (hook, captured)
}

/// Run a `streamSimple` with a capturing `onPayload` and return the payload.
/// Holds the SDK mock's test lock: the request constructs a real client,
/// which a concurrently installed mock would otherwise record.
pub(crate) async fn capture_simple_payload(
    stream_simple: fn(
        &Model,
        &TranscriptContext,
        SimpleStreamOptions,
    ) -> AssistantMessageEventStream,
    model: &Model,
    reasoning: Option<ThinkingLevel>,
    thinking_budgets: Option<ThinkingBudgets>,
) -> JsonValue {
    let _serial = super::genai::mock::serial().await;
    let (hook, captured) = capturing_on_payload();
    let mut options = SimpleStreamOptions {
        reasoning,
        thinking_budgets,
        ..SimpleStreamOptions::default()
    };
    options.stream.request.api_key = Some("test".to_owned());
    options.stream.request.on_payload = Some(hook);
    let context =
        context(&json!({ "messages": [{ "role": "user", "content": "Hello", "timestamp": 0 }] }));
    let result = stream_simple(model, &context, options).result().await;
    assert!(
        result
            .error_message
            .as_deref()
            .unwrap_or_default()
            .contains("payload captured"),
        "{:?}",
        result.error_message
    );
    let payload = captured
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .take();
    payload.expect("payload was not captured")
}

/// One HTTP request received by [`serve_once`].
#[derive(Debug, Clone)]
pub(crate) struct CapturedRequest {
    pub(crate) request_line: String,
    /// Lowercase header names in arrival order.
    pub(crate) headers: Vec<(String, String)>,
    pub(crate) body: String,
}

impl CapturedRequest {
    pub(crate) fn header(&self, name: &str) -> Option<&str> {
        self.headers
            .iter()
            .find(|(key, _)| key == name)
            .map(|(_, value)| value.as_str())
    }
}

/// Serve one HTTP/1.1 response on a local port; returns the base URL and
/// the captured request.
pub(crate) async fn serve_once(
    status_line: &'static str,
    content_type: &'static str,
    body: String,
) -> (String, tokio::task::JoinHandle<CapturedRequest>) {
    let listener = tokio::net::TcpListener::bind("127.0.0.1:0")
        .await
        .expect("bind");
    let address = listener.local_addr().expect("address");
    let handle = tokio::spawn(async move {
        let (mut socket, _) = listener.accept().await.expect("accept");
        let mut received = Vec::new();
        let mut buffer = [0_u8; 8192];
        let (head_end, content_length) = loop {
            let read = socket.read(&mut buffer).await.expect("read");
            received.extend_from_slice(&buffer[..read]);
            if let Some(end) = received.windows(4).position(|w| w == b"\r\n\r\n") {
                let head = String::from_utf8_lossy(&received[..end]).to_lowercase();
                let length = head
                    .lines()
                    .find_map(|line| line.strip_prefix("content-length:"))
                    .and_then(|value| value.trim().parse::<usize>().ok())
                    .unwrap_or(0);
                break (end + 4, length);
            }
        };
        while received.len() < head_end + content_length {
            let read = socket.read(&mut buffer).await.expect("read");
            received.extend_from_slice(&buffer[..read]);
        }
        let head = String::from_utf8_lossy(&received[..head_end - 4]).into_owned();
        let mut lines = head.lines();
        let request_line = lines.next().unwrap_or_default().to_owned();
        let headers = lines
            .filter_map(|line| line.split_once(':'))
            .map(|(name, value)| (name.trim().to_lowercase(), value.trim().to_owned()))
            .collect();
        let request_body =
            String::from_utf8_lossy(&received[head_end..head_end + content_length]).into_owned();
        let response = format!(
            "HTTP/1.1 {status_line}\r\ncontent-type: {content_type}\r\ncontent-length: {}\r\nconnection: close\r\n\r\n{body}",
            body.len()
        );
        socket.write_all(response.as_bytes()).await.expect("write");
        socket.shutdown().await.ok();
        CapturedRequest {
            request_line,
            headers,
            body: request_body,
        }
    });
    (format!("http://{address}"), handle)
}
