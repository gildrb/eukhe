//! Port of `openai-completions-provider-stream-event.test.ts`.

use std::sync::{Arc, Mutex, PoisonError};

use serde_json::json;

use super::support::{collect, model, sse_fetch, user_context};
use crate::api::openai_completions::stream_simple;
use crate::types::{
    JsonValue, Model, OnProviderStreamEvent, ProviderRequestOptions, SimpleStreamOptions,
    StreamOptions,
};

fn open_router_model() -> Model {
    model(json!({
        "id": "openrouter/auto",
        "name": "OpenRouter Auto",
        "api": "openai-completions",
        "provider": "openrouter",
        "baseUrl": "https://openrouter.ai/api/v1",
        "reasoning": false,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 200_000,
        "maxTokens": 8192,
    }))
}

// Regression test for #9784.
#[tokio::test]
async fn exposes_provider_chunks_including_openrouter_metadata() {
    let first_chunk = json!({
        "id": "chatcmpl-1",
        "model": "anthropic/claude-sonnet-4.6",
        "choices": [{ "index": 0, "delta": { "content": "hello" } }],
    });
    let final_chunk = json!({
        "id": "chatcmpl-1",
        "model": "anthropic/claude-sonnet-4.6",
        "choices": [{ "index": 0, "delta": {}, "finish_reason": "stop" }],
        "usage": {
            "prompt_tokens": 10,
            "completion_tokens": 2,
            "total_tokens": 12,
            "cost": 0.0012,
            "is_byok": false,
        },
        "openrouter_metadata": { "strategy": "direct", "region": "iad" },
    });
    let (fetch, _) = sse_fetch(vec![first_chunk.clone(), final_chunk.clone()]);
    let events: Arc<Mutex<Vec<JsonValue>>> = Arc::default();
    let sink = Arc::clone(&events);
    let on_event: OnProviderStreamEvent = Arc::new(move |data: &JsonValue, _model: &Model| {
        sink.lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(data.clone());
        Box::pin(async { Ok(()) })
    });

    let (_, message) = collect(stream_simple(
        &open_router_model(),
        &user_context("hi"),
        SimpleStreamOptions {
            stream: StreamOptions {
                request: ProviderRequestOptions {
                    api_key: Some("test".to_owned()),
                    fetch: Some(fetch),
                    ..ProviderRequestOptions::default()
                },
                on_provider_stream_event: Some(on_event),
                ..StreamOptions::default()
            },
            ..SimpleStreamOptions::default()
        },
    ))
    .await;

    assert_eq!(
        serde_json::to_value(&message.content).expect("serialize content"),
        json!([{ "type": "text", "text": "hello" }])
    );
    assert_eq!(
        *events.lock().unwrap_or_else(PoisonError::into_inner),
        vec![first_chunk, final_chunk]
    );
}
