//! Shared helpers of the `openai-completions` tests. The TS tests replace
//! the `openai` SDK class (`vi.mock("openai")`) with a fake whose
//! `chat.completions.create` captures `params` and yields fixed chunks; here
//! the `fetch` option plays that role: it records the HTTP request the SDK
//! layer sends and answers with the chunks as a server-sent-event body.

use std::sync::Arc;

use futures::StreamExt;
use serde_json::json;

use crate::api::system_one_shared::test_fetch::{
    mock_fetch, recorded, response, Recorded, Requests,
};
use crate::types::{
    AssistantMessage, AssistantMessageEvent, Context, FetchFunction, JsonValue, Model,
    ProviderRequestOptions, StreamOptions, TranscriptContext,
};
use crate::utils::event_stream::AssistantMessageEventStream;
use crate::utils::transcript::normalize_context;

use super::super::{stream_with_options, OpenAICompletionsOptions};

/// A chat model from TS-shaped JSON.
pub(crate) fn model(value: JsonValue) -> Model {
    serde_json::from_value(value).expect("valid model JSON")
}

/// The usual test model: `{ id, name, api: "openai-completions", provider,
/// baseUrl, reasoning, input: ["text"], cost: 0, contextWindow: 128000,
/// maxTokens: 4096 }`, with `overrides` merged on top.
// Test helpers take literal JSON by value, mirroring the TS call shape.
#[allow(clippy::needless_pass_by_value)]
pub(crate) fn test_model(overrides: JsonValue) -> Model {
    let mut base = json!({
        "id": "test-model",
        "name": "Test Model",
        "api": "openai-completions",
        "provider": "openai",
        "baseUrl": "https://api.openai.com/v1",
        "reasoning": false,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 128_000,
        "maxTokens": 4096,
    });
    if let (Some(base), Some(overrides)) = (base.as_object_mut(), overrides.as_object()) {
        for (key, value) in overrides {
            base.insert(key.clone(), value.clone());
        }
    }
    model(base)
}

/// `normalizeContext(context)` of TS-shaped context JSON.
pub(crate) fn context(value: JsonValue) -> TranscriptContext {
    let context: Context = serde_json::from_value(value).expect("valid context JSON");
    normalize_context(context)
}

/// `normalizeContext({ messages: [{ role: "user", content: text, timestamp }] })`.
pub(crate) fn user_context(text: &str) -> TranscriptContext {
    context(json!({ "messages": [{ "role": "user", "content": text, "timestamp": 1 }] }))
}

/// The chunks as an SSE body terminated by `data: [DONE]`.
pub(crate) fn sse_body(chunks: &[JsonValue]) -> String {
    let mut body = String::new();
    for chunk in chunks {
        body.push_str("data: ");
        body.push_str(&serde_json::to_string(chunk).expect("serialize chunk"));
        body.push_str("\n\n");
    }
    body.push_str("data: [DONE]\n\n");
    body
}

/// The minimal successful stream: one chunk with `finish_reason: "stop"`.
pub(crate) fn stop_chunks() -> Vec<JsonValue> {
    vec![json!({
        "id": "chatcmpl-test",
        "choices": [{ "index": 0, "delta": {}, "finish_reason": "stop" }],
    })]
}

/// A `fetch` answering every request with `chunks` as a 200 SSE response.
// Test helpers take literal JSON by value, mirroring the TS call shape.
#[allow(clippy::needless_pass_by_value)]
pub(crate) fn sse_fetch(chunks: Vec<JsonValue>) -> (FetchFunction, Requests) {
    let body = sse_body(&chunks);
    mock_fetch(move |_| response(200, &[("content-type", "text/event-stream")], body.clone()))
}

/// A `fetch` answering every request with `status` and a JSON body.
pub(crate) fn error_fetch(status: u16, body: &JsonValue) -> (FetchFunction, Requests) {
    let body = serde_json::to_string(body).expect("serialize body");
    mock_fetch(move |_| {
        response(
            status,
            &[("content-type", "application/json")],
            body.clone(),
        )
    })
}

/// Options with `api_key: "test"` and `fetch`.
pub(crate) fn options_with_fetch(fetch: FetchFunction) -> OpenAICompletionsOptions {
    OpenAICompletionsOptions {
        stream: StreamOptions {
            request: ProviderRequestOptions {
                api_key: Some("test".to_owned()),
                fetch: Some(fetch),
                ..ProviderRequestOptions::default()
            },
            ..StreamOptions::default()
        },
        ..OpenAICompletionsOptions::default()
    }
}

/// Drain a stream: every event and the final message.
pub(crate) async fn collect(
    stream: AssistantMessageEventStream,
) -> (Vec<AssistantMessageEvent>, AssistantMessage) {
    let events: Vec<AssistantMessageEvent> = stream.events().collect().await;
    let message = stream.result().await;
    (events, message)
}

/// Run one request whose server answers with `chunks`; returns the request
/// the SDK sent and the final message.
pub(crate) async fn run_with_chunks(
    model: &Model,
    context: &TranscriptContext,
    mut options: OpenAICompletionsOptions,
    chunks: Vec<JsonValue>,
) -> (
    Option<Recorded>,
    Vec<AssistantMessageEvent>,
    AssistantMessage,
) {
    let (fetch, requests) = sse_fetch(chunks);
    options.stream.request.fetch = Some(fetch);
    if options.stream.request.api_key.is_none() {
        options.stream.request.api_key = Some("test".to_owned());
    }
    let (events, message) = collect(stream_with_options(model, context, options)).await;
    (recorded(&requests).into_iter().next(), events, message)
}

/// The JSON request body `buildParams` produced (TS: the `params` the fake
/// `create` captured), for a request answered with a plain stop.
pub(crate) async fn capture_payload(
    model: &Model,
    context: &TranscriptContext,
    options: OpenAICompletionsOptions,
) -> JsonValue {
    let (request, _, message) = run_with_chunks(model, context, options, stop_chunks()).await;
    request
        .unwrap_or_else(|| panic!("no request was sent: {:?}", message.error_message))
        .json()
}

/// An `on_payload` hook that records each payload it sees.
pub(crate) fn payload_recorder() -> (
    crate::types::OnPayload<Model>,
    Arc<std::sync::Mutex<Vec<JsonValue>>>,
) {
    let seen: Arc<std::sync::Mutex<Vec<JsonValue>>> = Arc::default();
    let sink = Arc::clone(&seen);
    let hook: crate::types::OnPayload<Model> = Arc::new(move |payload, _model| {
        sink.lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .push(payload);
        Box::pin(async { Ok(None) })
    });
    (hook, seen)
}
