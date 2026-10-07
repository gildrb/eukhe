//! Port of `test/pi-messages.test.ts`, against a local HTTP server.

use std::collections::HashMap;
use std::fmt::Write as _;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_pi_ai::api::pi_messages::{stream, stream_simple};
use eukhe_pi_ai::compat::get_api_provider;
use eukhe_pi_ai::types::{
    OnProviderStreamEvent, OnResponse, ProviderStreamOptions, SimpleStreamOptions,
};
use eukhe_pi_ai::utils::transcript::normalize_context;
use eukhe_types::pi_ai::{
    AssistantMessageEvent, Context, JsonValue, Model, ProviderHeaders, StopReason,
    TranscriptContext, Usage,
};
use futures::StreamExt;
use serde_json::json;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpListener;

/// One request the server received.
#[derive(Debug, Clone)]
struct RecordedRequest {
    url: String,
    headers: HashMap<String, String>,
    body: Option<JsonValue>,
}

/// TS `ResponderOptions`.
#[derive(Default, Clone)]
struct ResponderOptions {
    status: Option<u16>,
    headers: Vec<(String, String)>,
    events: Vec<JsonValue>,
    raw_body: Option<String>,
}

fn reason_phrase(status: u16) -> &'static str {
    reqwest::StatusCode::from_u16(status)
        .ok()
        .and_then(|status| status.canonical_reason())
        .unwrap_or("")
}

fn find(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    haystack
        .windows(needle.len())
        .position(|window| window == needle)
}

/// TS `startServer`: a one-connection-at-a-time HTTP/1.1 server.
async fn start_server(options: ResponderOptions) -> (String, Arc<Mutex<Vec<RecordedRequest>>>) {
    let listener = TcpListener::bind("127.0.0.1:0").await.expect("bind");
    let address = listener.local_addr().expect("address");
    let requests = Arc::new(Mutex::new(Vec::new()));
    let recorded = Arc::clone(&requests);
    tokio::spawn(async move {
        loop {
            let Ok((mut socket, _)) = listener.accept().await else {
                return;
            };
            let options = options.clone();
            let recorded = Arc::clone(&recorded);
            tokio::spawn(async move {
                let mut data = Vec::new();
                let mut buf = [0u8; 4096];
                let header_end = loop {
                    let n = socket.read(&mut buf).await.expect("read");
                    if n == 0 {
                        return;
                    }
                    data.extend_from_slice(&buf[..n]);
                    if let Some(end) = find(&data, b"\r\n\r\n") {
                        break end;
                    }
                };
                let head = String::from_utf8_lossy(&data[..header_end]).into_owned();
                let mut lines = head.split("\r\n");
                let request_line = lines.next().unwrap_or_default();
                let url = request_line
                    .split(' ')
                    .nth(1)
                    .unwrap_or_default()
                    .to_owned();
                let headers: HashMap<String, String> = lines
                    .filter_map(|line| line.split_once(':'))
                    .map(|(name, value)| (name.trim().to_lowercase(), value.trim().to_owned()))
                    .collect();
                let length: usize = headers
                    .get("content-length")
                    .and_then(|value| value.parse().ok())
                    .unwrap_or(0);
                let mut body = data[header_end + 4..].to_vec();
                while body.len() < length {
                    let n = socket.read(&mut buf).await.expect("read body");
                    if n == 0 {
                        break;
                    }
                    body.extend_from_slice(&buf[..n]);
                }
                let raw = String::from_utf8_lossy(&body).into_owned();
                recorded
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .push(RecordedRequest {
                        url,
                        headers,
                        body: (!raw.is_empty()).then(|| serde_json::from_str(&raw).expect("json")),
                    });

                let response = if let Some(status) = options.status.filter(|status| *status != 200)
                {
                    let body = options.raw_body.clone().unwrap_or_else(|| "{}".to_owned());
                    format!(
                        "HTTP/1.1 {status} {}\r\ncontent-type: application/json\r\ncontent-length: {}\r\nconnection: close\r\n\r\n{body}",
                        reason_phrase(status),
                        body.len()
                    )
                } else {
                    let mut body = String::new();
                    for event in &options.events {
                        write!(body, "data: {event}\n\n").expect("write to string");
                    }
                    let mut head = String::new();
                    for (name, value) in &options.headers {
                        write!(head, "{name}: {value}\r\n").expect("write to string");
                    }
                    format!(
                        "HTTP/1.1 200 OK\r\ncontent-type: text/event-stream\r\n{head}content-length: {}\r\nconnection: close\r\n\r\n{body}",
                        body.len()
                    )
                };
                socket.write_all(response.as_bytes()).await.expect("write");
                socket.shutdown().await.ok();
            });
        }
    });
    (format!("http://127.0.0.1:{}/v1", address.port()), requests)
}

fn create_model(base_url: &str) -> Model {
    serde_json::from_value(json!({
        "id": "auto",
        "name": "Radius Auto",
        "api": "pi-messages",
        "provider": "radius",
        "baseUrl": base_url,
        "reasoning": false,
        "input": ["text"],
        "cost": { "input": 1, "output": 2, "cacheRead": 0.1, "cacheWrite": 0.2 },
        "contextWindow": 128_000,
        "maxTokens": 16384,
    }))
    .expect("model")
}

fn raw_context() -> JsonValue {
    json!({ "messages": [{ "role": "user", "content": "Hello", "timestamp": 1_700_000_000_000_u64 }] })
}

fn context() -> TranscriptContext {
    normalize_context(serde_json::from_value::<Context>(raw_context()).expect("context"))
}

fn usage_json() -> JsonValue {
    json!({
        "input": 10,
        "output": 5,
        "cacheRead": 0,
        "cacheWrite": 0,
        "totalTokens": 15,
        "cost": { "input": 0.1, "output": 0.2, "cacheRead": 0, "cacheWrite": 0, "total": 0.3 },
    })
}

fn usage() -> Usage {
    serde_json::from_value(usage_json()).expect("usage")
}

fn options_with_key(api_key: &str) -> ProviderStreamOptions {
    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = Some(api_key.to_owned());
    options
}

fn partial_of(event: &AssistantMessageEvent) -> Option<&eukhe_types::pi_ai::AssistantMessage> {
    match event {
        AssistantMessageEvent::Start { partial }
        | AssistantMessageEvent::TextStart { partial, .. }
        | AssistantMessageEvent::TextDelta { partial, .. }
        | AssistantMessageEvent::TextEnd { partial, .. }
        | AssistantMessageEvent::ThinkingStart { partial, .. }
        | AssistantMessageEvent::ThinkingDelta { partial, .. }
        | AssistantMessageEvent::ThinkingEnd { partial, .. }
        | AssistantMessageEvent::ToolCallStart { partial, .. }
        | AssistantMessageEvent::ToolCallDelta { partial, .. }
        | AssistantMessageEvent::ToolCallEnd { partial, .. } => Some(partial),
        AssistantMessageEvent::Done { .. } | AssistantMessageEvent::Error { .. } => None,
    }
}

#[tokio::test]
async fn streams_text_and_tool_calls_and_resolves_the_terminal_message() {
    let (base_url, requests) = start_server(ResponderOptions {
        events: vec![
            json!({ "type": "start" }),
            json!({ "type": "text_start", "contentIndex": 0 }),
            json!({ "type": "text_delta", "contentIndex": 0, "delta": "Hel" }),
            json!({ "type": "text_delta", "contentIndex": 0, "delta": "lo" }),
            json!({ "type": "text_end", "contentIndex": 0, "content": "Hello" }),
            json!({ "type": "toolcall_start", "contentIndex": 1, "id": "call_1", "toolName": "read" }),
            json!({ "type": "toolcall_delta", "contentIndex": 1, "delta": "{\"path\":" }),
            json!({ "type": "toolcall_delta", "contentIndex": 1, "delta": "\"a.txt\"}" }),
            json!({
                "type": "toolcall_end",
                "contentIndex": 1,
                "toolCall": { "type": "toolCall", "id": "call_1", "name": "read", "arguments": { "path": "a.txt" } },
            }),
            json!({
                "type": "done",
                "reason": "toolUse",
                "usage": usage_json(),
                "responseId": "resp_1",
                "providerThinkingLevel": "high",
            }),
        ],
        ..ResponderOptions::default()
    })
    .await;
    let model = create_model(&base_url);

    let mut options = options_with_key("test-key");
    options.stream.session_id = Some("session-1".into());
    options.stream.max_tokens = Some(100);
    let mut headers = ProviderHeaders::new();
    headers.insert("x-custom".into(), Some("1".into()));
    options.stream.request.headers = Some(headers);
    options.extra.insert("toolChoice".into(), "auto".into());
    let event_stream = stream(&model, &context(), options);
    let mut events = Vec::new();
    let mut partial_stop_reasons = Vec::new();
    let mut iter = event_stream.events();
    while let Some(event) = iter.next().await {
        if let Some(partial) = partial_of(&event) {
            partial_stop_reasons.push(partial.stop_reason);
        }
        events.push(event);
    }
    let message = event_stream.result().await;

    assert_eq!(partial_stop_reasons[0], StopReason::Pending);
    assert_eq!(message.stop_reason, StopReason::ToolUse);
    assert_eq!(message.usage, usage());
    assert_eq!(message.response_id.as_deref(), Some("resp_1"));
    assert_eq!(message.provider_thinking_level.as_deref(), Some("high"));
    assert_eq!(message.model, "auto");
    assert_eq!(message.provider.as_str(), "radius");
    assert_eq!(
        serde_json::to_value(&message.content).expect("content"),
        json!([
            { "type": "text", "text": "Hello" },
            { "type": "toolCall", "id": "call_1", "name": "read", "arguments": { "path": "a.txt" } },
        ])
    );
    assert!(events
        .iter()
        .any(|event| matches!(event, AssistantMessageEvent::TextDelta { .. })));
    assert_eq!(
        events
            .iter()
            .filter(|event| matches!(event, AssistantMessageEvent::ToolCallEnd { .. }))
            .count(),
        1
    );

    let requests = requests
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone();
    assert_eq!(requests.len(), 1);
    let request = &requests[0];
    assert_eq!(request.url, "/v1/messages");
    assert_eq!(
        request.headers.get("authorization").map(String::as_str),
        Some("Bearer test-key")
    );
    assert_eq!(
        request.headers.get("x-custom").map(String::as_str),
        Some("1")
    );
    assert_eq!(
        request.body,
        Some(json!({
            "model": "auto",
            "context": raw_context(),
            "options": { "maxTokens": 100, "sessionId": "session-1", "toolChoice": "auto" },
        }))
    );
}

#[tokio::test]
async fn forwards_parsed_wire_events_in_order_before_converting_them() {
    let wire_events = vec![
        json!({ "type": "start" }),
        json!({ "type": "text_start", "contentIndex": 0 }),
        json!({ "type": "text_delta", "contentIndex": 0, "delta": "Hello", "gatewayField": "upstream-value" }),
        json!({ "type": "text_end", "contentIndex": 0, "content": "Hello" }),
        json!({ "type": "done", "reason": "stop", "usage": usage_json(), "responseId": "resp_1" }),
    ];
    let (base_url, _) = start_server(ResponderOptions {
        events: wire_events.clone(),
        ..ResponderOptions::default()
    })
    .await;
    let model = create_model(&base_url);
    let received: Arc<Mutex<Vec<(JsonValue, Model)>>> = Arc::new(Mutex::new(Vec::new()));
    let sink = Arc::clone(&received);
    let observer: OnProviderStreamEvent = Arc::new(move |event, event_model| {
        let sink = Arc::clone(&sink);
        let entry = (event.clone(), event_model.clone());
        Box::pin(async move {
            tokio::task::yield_now().await;
            sink.lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(entry);
            Ok(())
        })
    });
    let mut options = SimpleStreamOptions::default();
    options.stream.request.api_key = Some("test-key".into());
    options.stream.on_provider_stream_event = Some(observer);
    let message = stream_simple(&model, &context(), options).result().await;

    let received = received
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone();
    assert_eq!(
        received
            .iter()
            .map(|(event, _)| event.clone())
            .collect::<Vec<_>>(),
        wire_events
    );
    assert!(received
        .iter()
        .all(|(_, event_model)| *event_model == model));
    assert_eq!(message.stop_reason, StopReason::Stop);
    assert_eq!(message.response_id.as_deref(), Some("resp_1"));
    assert_eq!(
        serde_json::to_value(&message.content).expect("content"),
        json!([{ "type": "text", "text": "Hello" }])
    );
}

/// TS passes `debug: true` through `streamSimple`'s untyped options; Rust
/// `SimpleStreamOptions` has no extra keys, so this goes through `stream`
/// with `extra.debug`.
#[tokio::test]
async fn appends_debug_1_and_reports_response_headers_via_on_response() {
    let (base_url, requests) = start_server(ResponderOptions {
        headers: vec![("x-pi-gateway-upstream-provider".into(), "anthropic".into())],
        events: vec![json!({ "type": "done", "reason": "stop", "usage": usage_json() })],
        ..ResponderOptions::default()
    })
    .await;
    let model = create_model(&base_url);
    let observed: Arc<Mutex<Option<HashMap<String, String>>>> = Arc::new(Mutex::new(None));
    let sink = Arc::clone(&observed);
    let on_response: OnResponse<Model> = Arc::new(move |response, _| {
        *sink.lock().unwrap_or_else(PoisonError::into_inner) =
            Some(response.headers.into_iter().collect());
        Box::pin(async { Ok(()) })
    });
    let mut options = options_with_key("test-key");
    options.extra.insert("debug".into(), true.into());
    options.stream.request.on_response = Some(on_response);
    let message = stream(&model, &context(), options).result().await;

    assert_eq!(message.stop_reason, StopReason::Stop);
    assert_eq!(
        requests.lock().unwrap_or_else(PoisonError::into_inner)[0].url,
        "/v1/messages?debug=1"
    );
    assert_eq!(
        observed
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .as_ref()
            .and_then(|headers| headers.get("x-pi-gateway-upstream-provider").cloned())
            .as_deref(),
        Some("anthropic")
    );
}

#[tokio::test]
async fn surfaces_backend_error_responses_with_diagnostics() {
    let (base_url, _) = start_server(ResponderOptions {
        status: Some(401),
        raw_body: Some(
            json!({ "error": { "message": "Token expired", "code": "unauthorized" } }).to_string(),
        ),
        ..ResponderOptions::default()
    })
    .await;
    let model = create_model(&base_url);

    let message = stream(&model, &context(), options_with_key("stale"))
        .result()
        .await;

    assert_eq!(message.stop_reason, StopReason::Error);
    let error_message = message.error_message.clone().unwrap_or_default();
    assert_eq!(
        error_message,
        "401 Unauthorized: Token expired (unauthorized)"
    );
    let diagnostic = &message.diagnostics.as_ref().expect("diagnostics")[0];
    assert_eq!(diagnostic.kind, "pi_messages_response_failure");
    assert_eq!(
        diagnostic
            .details
            .as_ref()
            .and_then(|details| details.get("status")),
        Some(&json!(401))
    );
}

#[tokio::test]
async fn propagates_server_sent_error_events() {
    let (base_url, _) = start_server(ResponderOptions {
        events: vec![
            json!({ "type": "start" }),
            json!({ "type": "error", "reason": "error", "usage": usage_json(), "errorMessage": "Upstream failed" }),
        ],
        ..ResponderOptions::default()
    })
    .await;
    let model = create_model(&base_url);

    let message = stream(&model, &context(), options_with_key("test-key"))
        .result()
        .await;

    assert_eq!(message.stop_reason, StopReason::Error);
    assert_eq!(message.error_message.as_deref(), Some("Upstream failed"));
    assert_eq!(message.usage, usage());
}

#[tokio::test]
async fn errors_when_no_api_key_is_provided() {
    let model = create_model("http://127.0.0.1:1/v1");

    let message = stream(&model, &context(), ProviderStreamOptions::default())
        .result()
        .await;

    assert_eq!(message.stop_reason, StopReason::Error);
    assert!(message
        .error_message
        .unwrap_or_default()
        .contains("No API key provided"));
}

#[tokio::test]
async fn errors_when_the_stream_ends_without_a_terminal_event() {
    let (base_url, _) = start_server(ResponderOptions {
        events: vec![
            json!({ "type": "start" }),
            json!({ "type": "text_start", "contentIndex": 0 }),
            json!({ "type": "text_delta", "contentIndex": 0, "delta": "partial" }),
        ],
        ..ResponderOptions::default()
    })
    .await;
    let model = create_model(&base_url);

    let message = stream(&model, &context(), options_with_key("test-key"))
        .result()
        .await;

    assert_eq!(message.stop_reason, StopReason::Error);
    assert!(message
        .error_message
        .unwrap_or_default()
        .contains("stream ended without a terminal event"));
}

#[test]
fn is_registered_as_a_builtin_api_provider() {
    assert!(get_api_provider("pi-messages").is_some());
}

#[test]
fn is_a_known_api_usable_on_models() {
    let api: eukhe_types::pi_ai::Api = serde_json::from_value(json!("pi-messages")).expect("api");
    assert_eq!(api.as_str(), "pi-messages");
}
