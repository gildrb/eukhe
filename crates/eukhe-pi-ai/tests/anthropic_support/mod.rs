//! Test helpers for the `anthropic-messages` tests: a `fetch` mock that
//! records requests and answers with canned SSE bodies (the TS tests' fake
//! SDK clients and `fetch` spies), plus model and context builders.

#![allow(dead_code)] // Each test binary uses a subset.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_pi_ai::types::{AssistantMessage, AssistantMessageEvent, FetchFunction, JsonValue};
use eukhe_pi_ai::utils::event_stream::AssistantMessageEventStream;
use eukhe_types::pi_ai::Model;
use futures::StreamExt;
use serde_json::json;

/// One captured request.
#[derive(Debug, Clone)]
pub struct CapturedRequest {
    pub url: String,
    pub headers: reqwest::header::HeaderMap,
    /// The parsed JSON body (`Null` when the body is not JSON).
    pub body: JsonValue,
}

impl CapturedRequest {
    /// A header value by case-insensitive name.
    #[must_use]
    pub fn header(&self, name: &str) -> Option<String> {
        self.headers
            .get(name)
            .and_then(|value| value.to_str().ok())
            .map(str::to_owned)
    }

    /// The URL path (no query).
    #[must_use]
    pub fn path(&self) -> String {
        reqwest::Url::parse(&self.url)
            .map(|url| url.path().to_owned())
            .unwrap_or_default()
    }
}

/// A canned response.
#[derive(Debug, Clone)]
pub struct MockResponse {
    pub status: u16,
    pub headers: Vec<(String, String)>,
    pub body: String,
}

impl MockResponse {
    /// A 200 `text/event-stream` response.
    #[must_use]
    pub fn sse(body: impl Into<String>) -> Self {
        Self {
            status: 200,
            headers: vec![("content-type".into(), "text/event-stream".into())],
            body: body.into(),
        }
    }

    /// A JSON response with `status`.
    #[must_use]
    pub fn json(status: u16, body: impl Into<String>) -> Self {
        Self {
            status,
            headers: vec![("content-type".into(), "application/json".into())],
            body: body.into(),
        }
    }

    /// Add a response header.
    #[must_use]
    pub fn with_header(mut self, name: &str, value: &str) -> Self {
        self.headers.push((name.into(), value.into()));
        self
    }
}

/// TS `createSseResponse(events)`: `event: <name>\ndata: <data>\n` joined by `\n`.
#[must_use]
pub fn sse_body(events: &[(&str, JsonValue)]) -> String {
    events
        .iter()
        .map(|(event, data)| {
            let data = match data {
                JsonValue::String(text) => text.clone(),
                other => other.to_string(),
            };
            format!("event: {event}\ndata: {data}\n")
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// SSE body of typed events: each event name is the payload's `type`.
#[must_use]
pub fn sse_of(events: &[JsonValue]) -> String {
    let named: Vec<(&str, JsonValue)> = events
        .iter()
        .map(|event| {
            (
                event.get("type").and_then(JsonValue::as_str).unwrap_or(""),
                event.clone(),
            )
        })
        .collect();
    sse_body(&named)
}

/// A minimal successful text response (`message_start` .. `message_stop`).
#[must_use]
pub fn text_response_events(text: &str) -> Vec<JsonValue> {
    vec![
        json!({"type": "message_start", "message": {"id": "msg_test", "usage": {"input_tokens": 12, "output_tokens": 0, "cache_read_input_tokens": 0, "cache_creation_input_tokens": 0}}}),
        json!({"type": "content_block_start", "index": 0, "content_block": {"type": "text", "text": ""}}),
        json!({"type": "content_block_delta", "index": 0, "delta": {"type": "text_delta", "text": text}}),
        json!({"type": "content_block_stop", "index": 0}),
        json!({"type": "message_delta", "delta": {"stop_reason": "end_turn"}, "usage": {"input_tokens": 12, "output_tokens": 5, "cache_read_input_tokens": 0, "cache_creation_input_tokens": 0}}),
        json!({"type": "message_stop"}),
    ]
}

/// The shared recorder of captured requests.
pub type Captured = Arc<Mutex<Vec<CapturedRequest>>>;

/// All captured requests so far.
#[must_use]
pub fn requests(captured: &Captured) -> Vec<CapturedRequest> {
    captured
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
}

/// A fetch mock that answers through `respond` and records every request.
pub fn mock_fetch_with(
    respond: impl Fn(&CapturedRequest) -> MockResponse + Send + Sync + 'static,
) -> (FetchFunction, Captured) {
    let captured: Captured = Arc::default();
    let sink = Arc::clone(&captured);
    let respond = Arc::new(respond);
    let fetch: FetchFunction = Arc::new(move |request: reqwest::Request| {
        let body = request
            .body()
            .and_then(reqwest::Body::as_bytes)
            .map_or(JsonValue::Null, |bytes| {
                serde_json::from_slice(bytes).unwrap_or(JsonValue::Null)
            });
        let captured_request = CapturedRequest {
            url: request.url().to_string(),
            headers: request.headers().clone(),
            body,
        };
        let response = respond(&captured_request);
        sink.lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(captured_request);
        Box::pin(async move {
            let mut builder = http::Response::builder().status(response.status);
            for (name, value) in &response.headers {
                builder = builder.header(name, value);
            }
            let http = builder.body(response.body).expect("mock response");
            Ok(reqwest::Response::from(http))
        })
    });
    (fetch, captured)
}

/// A fetch mock answering every request with `response`.
#[must_use]
pub fn mock_fetch(response: MockResponse) -> (FetchFunction, Captured) {
    mock_fetch_with(move |_| response.clone())
}

/// A fetch mock answering with the minimal successful text response.
#[must_use]
pub fn ok_fetch() -> (FetchFunction, Captured) {
    mock_fetch(MockResponse::sse(sse_of(&text_response_events("Hello"))))
}

/// All events of a stream and its final message.
pub async fn collect(
    stream: AssistantMessageEventStream,
) -> (Vec<AssistantMessageEvent>, AssistantMessage) {
    let events: Vec<AssistantMessageEvent> = stream.events().collect().await;
    let result = stream.result().await;
    (events, result)
}

/// An `anthropic-messages` model from JSON overrides over a base model
/// (TS `{ ...base, ...overrides }`).
#[must_use]
pub fn model(overrides: &JsonValue) -> Model {
    let mut base = json!({
        "id": "claude-test",
        "name": "Claude Test",
        "api": "anthropic-messages",
        "provider": "anthropic",
        "baseUrl": "https://api.anthropic.com",
        "reasoning": false,
        "input": ["text"],
        "cost": {"input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0},
        "contextWindow": 100_000,
        "maxTokens": 4096,
    });
    if let (Some(base), Some(overrides)) = (base.as_object_mut(), overrides.as_object()) {
        for (key, value) in overrides {
            base.insert(key.clone(), value.clone());
        }
    }
    serde_json::from_value(base).expect("model")
}

/// A transcript context from JSON (`Context` shape: `systemPrompt`,
/// `messages`, `tools`), normalized like TS `normalizeContext`.
#[must_use]
pub fn context(value: &JsonValue) -> eukhe_types::pi_ai::TranscriptContext {
    let context: eukhe_types::pi_ai::Context =
        serde_json::from_value(value.clone()).expect("context");
    eukhe_pi_ai::utils::transcript::normalize_context(context)
}

/// The TS fake SDK's `createSseResponse()`: `message_start`, `message_delta`
/// (`end_turn`), `message_stop`.
#[must_use]
pub fn minimal_sse() -> MockResponse {
    MockResponse::sse(sse_of(&[
        json!({"type": "message_start", "message": {"id": "msg_test", "usage": {"input_tokens": 1, "output_tokens": 0}}}),
        json!({"type": "message_delta", "delta": {"stop_reason": "end_turn"}, "usage": {"output_tokens": 1}}),
        json!({"type": "message_stop"}),
    ]))
}

/// TS `createFetch` of the federation tests: `/v1/oauth/token` answers
/// `{ access_token: "federated-token", expires_in: 3600 }`, everything else
/// [`minimal_sse`]. Each call is a distinct fetch identity (the module's
/// process-wide federation token cache is keyed by it).
#[must_use]
pub fn federation_fetch() -> (FetchFunction, Captured) {
    mock_fetch_with(|request| {
        if request.path() == "/v1/oauth/token" {
            MockResponse::json(
                200,
                r#"{"access_token":"federated-token","expires_in":3600}"#,
            )
        } else {
            minimal_sse()
        }
    })
}

/// A built-in catalog model with JSON overrides (TS `{ ...getModel(p, id), ...overrides }`).
#[must_use]
pub fn builtin_model(provider: &str, id: &str, overrides: &JsonValue) -> Model {
    let model = eukhe_pi_ai::compat::get_model(provider, id)
        .unwrap_or_else(|| panic!("built-in model {provider}/{id}"));
    let mut value = serde_json::to_value(model).expect("model json");
    if let (Some(base), Some(overrides)) = (value.as_object_mut(), overrides.as_object()) {
        for (key, value) in overrides {
            base.insert(key.clone(), value.clone());
        }
    }
    serde_json::from_value(value).expect("model")
}

/// The payload recorded by [`capturing_on_payload`].
pub type CapturedPayload = Arc<Mutex<Option<JsonValue>>>;

/// TS `onPayload: (payload) => { capturedPayload = payload; throw new PayloadCaptured(); }`.
#[must_use]
pub fn capturing_on_payload() -> (eukhe_pi_ai::types::OnPayload<Model>, CapturedPayload) {
    let captured: CapturedPayload = Arc::default();
    let sink = Arc::clone(&captured);
    let on_payload: eukhe_pi_ai::types::OnPayload<Model> = Arc::new(move |payload, _model| {
        *sink.lock().unwrap_or_else(PoisonError::into_inner) = Some(payload);
        Box::pin(async {
            Err(eukhe_pi_ai::utils::diagnostics::ErrorObject::named(
                "PayloadCaptured",
                "payload captured",
            )
            .thrown())
        })
    });
    (on_payload, captured)
}

/// The captured payload; panics like TS "Expected payload to be captured before request failure".
#[must_use]
pub fn take_payload(captured: &CapturedPayload) -> JsonValue {
    captured
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .take()
        .expect("Expected payload to be captured before request failure")
}

/// TS `capturePayload(model, options)` of the thinking/temperature tests:
/// `streamSimple` with `baseUrl: "http://127.0.0.1:9"`, `apiKey: "fake-key"`,
/// and an `onPayload` that records the payload and throws.
pub async fn capture_simple_payload(
    model: &Model,
    options: eukhe_pi_ai::types::SimpleStreamOptions,
) -> JsonValue {
    let mut model = model.clone();
    "http://127.0.0.1:9".clone_into(&mut model.base_url);
    let (on_payload, captured) = capturing_on_payload();
    let mut options = options;
    options.stream.request.api_key = Some("fake-key".into());
    options.stream.request.on_payload = Some(on_payload);
    let context: eukhe_types::pi_ai::Context = serde_json::from_value(json!({
        "messages": [{ "role": "user", "content": "Hello", "timestamp": 1 }],
    }))
    .expect("context");
    let stream = eukhe_pi_ai::compat::stream_simple(&model, context, options).expect("stream");
    let _ = stream.result().await;
    take_payload(&captured)
}

/// Vitest `toMatchObject`: objects match as subsets, arrays element-wise
/// with equal length, other values by equality.
pub fn assert_match_object(actual: &JsonValue, expected: &JsonValue) {
    assert!(
        matches_object(actual, expected),
        "expected {actual} to match object {expected}"
    );
}

fn matches_object(actual: &JsonValue, expected: &JsonValue) -> bool {
    match (actual, expected) {
        (JsonValue::Object(actual), JsonValue::Object(expected)) => {
            expected.iter().all(|(key, value)| {
                actual
                    .get(key)
                    .is_some_and(|actual| matches_object(actual, value))
            })
        }
        (JsonValue::Array(actual), JsonValue::Array(expected)) => {
            actual.len() == expected.len()
                && actual
                    .iter()
                    .zip(expected)
                    .all(|(actual, expected)| matches_object(actual, expected))
        }
        _ => actual == expected,
    }
}

/// TS `resolveApiKey(provider)` from `test/oauth.ts` reads
/// `~/.pi/agent/auth.json`; the Rust e2e tests take the resolved key from
/// `PI_TEST_<PROVIDER>_TOKEN` (e.g. `PI_TEST_GITHUB_COPILOT_TOKEN`).
#[must_use]
pub fn resolve_test_api_key(provider: &str) -> Option<String> {
    let name = format!(
        "PI_TEST_{}_TOKEN",
        provider.to_uppercase().replace('-', "_")
    );
    std::env::var(name).ok().filter(|value| !value.is_empty())
}
