//! Port of the payload cases of `openrouter-reasoning-options.test.ts`.
//!
//! The `getOpenRouterThinkingLevelMap` cases test the TS catalog generator
//! script (`scripts/openrouter-reasoning-options.ts`), which is not part of
//! the crate. The mandatory map below is the value that script returns for
//! `{ mandatory: true, supported_efforts: ["max", "high", "low"] }`.

use std::sync::{Arc, Mutex, PoisonError};

use serde_json::json;

use super::support::{collect, context, model};
use crate::api::openai_completions::stream_simple;
use crate::types::{
    JsonValue, Model, OnPayload, ProviderRequestOptions, SimpleStreamOptions, StreamOptions,
    ThinkingLevel,
};
use crate::utils::diagnostics::ErrorObject;

/// `getOpenRouterThinkingLevelMap({ mandatory: true, supported_efforts: ["max", "high", "low"] })`.
fn mandatory_map() -> JsonValue {
    json!({
        "minimal": null,
        "low": "low",
        "medium": null,
        "high": "high",
        "xhigh": null,
        "max": "max",
        "off": null,
    })
}

fn open_router_model(thinking_level_map: Option<JsonValue>) -> Model {
    let mut value = json!({
        "id": "stealth/ox-alpha",
        "name": "Ox Alpha",
        "api": "openai-completions",
        "provider": "openrouter",
        "baseUrl": "https://example.invalid/v1",
        "reasoning": true,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 128_000,
        "maxTokens": 4096,
        "compat": { "thinkingFormat": "openrouter" },
    });
    if let Some(map) = thinking_level_map {
        value
            .as_object_mut()
            .expect("model object")
            .insert("thinkingLevelMap".to_owned(), map);
    }
    model(value)
}

async fn capture_payload(model: &Model, reasoning: Option<ThinkingLevel>) -> JsonValue {
    let captured: Arc<Mutex<Option<JsonValue>>> = Arc::default();
    let sink = Arc::clone(&captured);
    let on_payload: OnPayload<Model> = Arc::new(move |payload: JsonValue, _model: &Model| {
        *sink.lock().unwrap_or_else(PoisonError::into_inner) = Some(payload);
        Box::pin(async { Err(ErrorObject::new("payload captured").thrown()) })
    });
    collect(stream_simple(
        model,
        &context(json!({ "messages": [{ "role": "user", "content": "Hello", "timestamp": 0 }] })),
        SimpleStreamOptions {
            stream: StreamOptions {
                request: ProviderRequestOptions {
                    api_key: Some("test".to_owned()),
                    on_payload: Some(on_payload),
                    ..ProviderRequestOptions::default()
                },
                ..StreamOptions::default()
            },
            reasoning,
            ..SimpleStreamOptions::default()
        },
    ))
    .await;
    let payload = captured
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .take();
    payload.expect("OpenRouter payload was not captured")
}

#[tokio::test]
async fn omits_reasoning_when_a_background_call_does_not_request_it() {
    let payload = capture_payload(&open_router_model(Some(mandatory_map())), None).await;

    assert_eq!(payload.get("reasoning"), None);
}

#[tokio::test]
async fn still_sends_an_explicitly_selected_supported_effort() {
    let payload = capture_payload(
        &open_router_model(Some(mandatory_map())),
        Some(ThinkingLevel::Low),
    )
    .await;

    // `toMatchObject({ reasoning: { effort: "low" } })`.
    assert_eq!(payload["reasoning"]["effort"], json!("low"));
}

#[tokio::test]
async fn continues_to_explicitly_disable_reasoning_for_optional_models() {
    let payload = capture_payload(&open_router_model(None), None).await;

    // `toMatchObject({ reasoning: { effort: "none" } })`.
    assert_eq!(payload["reasoning"]["effort"], json!("none"));
}
