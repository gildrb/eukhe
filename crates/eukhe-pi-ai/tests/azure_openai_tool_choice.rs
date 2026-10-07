//! Port of `test/azure-openai-tool-choice.test.ts`.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_pi_ai::api::azure_openai_responses::{stream, stream_simple};
use eukhe_pi_ai::types::{
    JsonValue, Model, OnPayload, ProviderStreamOptions, SimpleStreamOptions, StreamOptions,
};
use eukhe_pi_ai::utils::diagnostics::ErrorObject;
use eukhe_pi_ai::utils::transcript::normalize_context;
use eukhe_types::pi_ai::{Context, ToolChoice, TranscriptContext};
use serde_json::json;

fn model() -> Model {
    serde_json::from_value(json!({
        "id": "test-deployment",
        "name": "Test Deployment",
        "api": "azure-openai-responses",
        "provider": "azure",
        "baseUrl": "http://127.0.0.1:9/openai/v1",
        "reasoning": false,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 10_000,
        "maxTokens": 1_000,
    }))
    .expect("model")
}

fn context() -> TranscriptContext {
    let context: Context = serde_json::from_value(json!({
        "messages": [{ "role": "user", "content": "Summarize this", "timestamp": 1 }],
        "tools": [{
            "name": "read",
            "description": "Read a file",
            "parameters": {
                "type": "object",
                "properties": { "path": { "type": "string" } },
                "required": ["path"],
            },
        }],
    }))
    .expect("context");
    normalize_context(context)
}

/// An `onPayload` that records the payload and throws "payload captured".
fn capture_payload() -> (OnPayload<Model>, Arc<Mutex<Option<JsonValue>>>) {
    let payload: Arc<Mutex<Option<JsonValue>>> = Arc::default();
    let sink = Arc::clone(&payload);
    let on_payload: OnPayload<Model> = Arc::new(move |request_payload, _model| {
        *sink.lock().unwrap_or_else(PoisonError::into_inner) = Some(request_payload);
        Box::pin(async { Err(ErrorObject::new("payload captured").thrown()) })
    });
    (on_payload, payload)
}

fn stream_options(on_payload: OnPayload<Model>) -> StreamOptions {
    let mut options = StreamOptions::default();
    options.request.api_key = Some("test-key".to_owned());
    options.request.on_payload = Some(on_payload);
    options
}

fn assert_payload(payload: &Arc<Mutex<Option<JsonValue>>>, tool_choice: &str) {
    let payload = payload
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
        .expect("payload");
    assert_eq!(payload["tool_choice"], json!(tool_choice));
    assert_eq!(payload["tools"].as_array().map(Vec::len), Some(1));
}

#[tokio::test]
async fn forwards_provider_specific_tool_choice_while_preserving_tool_definitions() {
    let (on_payload, payload) = capture_payload();
    let mut extra = serde_json::Map::new();
    extra.insert("toolChoice".to_owned(), json!("required"));
    let result = stream(
        &model(),
        &context(),
        ProviderStreamOptions {
            stream: stream_options(on_payload),
            extra,
        },
    );

    result.result().await;

    assert_payload(&payload, "required");
}

#[tokio::test]
async fn forwards_provider_neutral_tool_choice_from_simple_options() {
    let (on_payload, payload) = capture_payload();
    let result = stream_simple(
        &model(),
        &context(),
        SimpleStreamOptions {
            stream: stream_options(on_payload),
            tool_choice: Some(ToolChoice::None),
            ..SimpleStreamOptions::default()
        },
    );

    result.result().await;

    assert_payload(&payload, "none");
}
