//! Port of the `openai-completions` cases of `sampling-options.test.ts`.
//!
//! The TS file dispatches through `compat.stream`/`streamSimple`; these
//! cases call this module's `stream`/`stream_simple` directly. The
//! `openai-responses`, `azure-openai-responses`, and `anthropic-messages`
//! cases belong to those modules' test suites.

use std::sync::{Arc, Mutex, PoisonError};

use serde_json::json;

use super::support::{collect, model, user_context};
use crate::api::openai_completions::{stream, stream_simple};
use crate::types::{
    JsonObject, JsonValue, Model, OnPayload, ProviderRequestOptions, ProviderStreamOptions,
    SimpleStreamOptions, StreamOptions, ThinkingLevel,
};
use crate::utils::diagnostics::ErrorObject;

/// TS `makeModel("openai-completions", samplingParams, overrides)`.
fn make_model(sampling_params: Option<JsonValue>, overrides: &JsonValue) -> Model {
    let mut value = json!({
        "id": "custom-model",
        "name": "Custom Model",
        "api": "openai-completions",
        "provider": "custom-provider",
        "baseUrl": "http://127.0.0.1:9/v1",
        "reasoning": false,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 128_000,
        "maxTokens": 16384,
    });
    let object = value.as_object_mut().expect("model object");
    if let Some(sampling_params) = sampling_params {
        object.insert("samplingParams".to_owned(), sampling_params);
    }
    for (key, field) in overrides.as_object().into_iter().flatten() {
        object.insert(key.clone(), field.clone());
    }
    model(value)
}

fn params(value: &JsonValue) -> JsonObject {
    value.as_object().expect("sampling params object").clone()
}

/// TS `capturingOptions`: `apiKey: "fake-key"` and an `onPayload` that
/// records the payload and throws `PayloadCaptured`.
fn capturing_request() -> (ProviderRequestOptions, Arc<Mutex<Option<JsonValue>>>) {
    let captured: Arc<Mutex<Option<JsonValue>>> = Arc::default();
    let sink = Arc::clone(&captured);
    let on_payload: OnPayload<Model> = Arc::new(move |payload: JsonValue, _model: &Model| {
        *sink.lock().unwrap_or_else(PoisonError::into_inner) = Some(payload);
        Box::pin(async { Err(ErrorObject::named("PayloadCaptured", "payload captured").thrown()) })
    });
    let request = ProviderRequestOptions {
        api_key: Some("fake-key".to_owned()),
        on_payload: Some(on_payload),
        ..ProviderRequestOptions::default()
    };
    (request, captured)
}

fn take_captured(captured: &Mutex<Option<JsonValue>>) -> JsonValue {
    captured
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .take()
        .expect("Expected payload to be captured before request failure")
}

/// TS `capturePayload`: `stream` with `StreamOptions & { reasoningEffort }`.
async fn capture_payload(
    model: &Model,
    stream_options: StreamOptions,
    reasoning_effort: Option<&str>,
) -> JsonValue {
    let (request, captured) = capturing_request();
    let mut extra = JsonObject::new();
    if let Some(effort) = reasoning_effort {
        extra.insert("reasoningEffort".to_owned(), json!(effort));
    }
    collect(stream(
        model,
        &user_context("Hello"),
        ProviderStreamOptions {
            stream: StreamOptions {
                request,
                ..stream_options
            },
            extra,
        },
    ))
    .await;
    take_captured(&captured)
}

/// TS `captureSimplePayload`.
async fn capture_simple_payload(model: &Model, options: SimpleStreamOptions) -> JsonValue {
    let (request, captured) = capturing_request();
    collect(stream_simple(
        model,
        &user_context("Hello"),
        SimpleStreamOptions {
            stream: StreamOptions {
                request,
                ..options.stream
            },
            ..options
        },
    ))
    .await;
    take_captured(&captured)
}

#[tokio::test]
async fn merges_request_sampling_params_into_the_request_body() {
    let payload = capture_payload(
        &make_model(None, &json!({})),
        StreamOptions {
            sampling_params: Some(params(&json!({ "top_p": 0.95, "top_k": 0, "min_p": 0 }))),
            ..StreamOptions::default()
        },
        None,
    )
    .await;

    assert_eq!(payload.get("top_p"), Some(&json!(0.95)));
    assert_eq!(payload.get("top_k"), Some(&json!(0)));
    assert_eq!(payload.get("min_p"), Some(&json!(0)));
}

#[tokio::test]
async fn omits_sampling_params_when_neither_options_nor_model_set_them() {
    let payload = capture_payload(
        &make_model(None, &json!({})),
        StreamOptions::default(),
        None,
    )
    .await;

    assert_eq!(payload.get("temperature"), None);
    assert_eq!(payload.get("top_p"), None);
}

// Model defaults must apply to direct stream()/complete() calls, not only streamSimple() (#9506).
#[tokio::test]
async fn applies_model_level_sampling_params_with_request_keys_taking_precedence_for_openai_completions(
) {
    let payload = capture_payload(
        &make_model(Some(json!({ "top_p": 0.95, "min_p": 0.05 })), &json!({})),
        StreamOptions {
            sampling_params: Some(params(&json!({ "top_p": 0.5 }))),
            ..StreamOptions::default()
        },
        None,
    )
    .await;

    assert_eq!(payload.get("top_p"), Some(&json!(0.5)));
    assert_eq!(payload.get("min_p"), Some(&json!(0.05)));
}

#[tokio::test]
async fn passes_request_sampling_params_through_stream_simple() {
    let payload = capture_simple_payload(
        &make_model(None, &json!({})),
        SimpleStreamOptions {
            stream: StreamOptions {
                sampling_params: Some(params(&json!({ "top_p": 0.5 }))),
                ..StreamOptions::default()
            },
            ..SimpleStreamOptions::default()
        },
    )
    .await;

    assert_eq!(payload.get("top_p"), Some(&json!(0.5)));
}

#[tokio::test]
async fn applies_sampling_params_for_the_effective_thinking_level_over_model_defaults() {
    let payload = capture_simple_payload(
        &make_model(
            Some(json!({ "temperature": 1, "top_p": 0.95 })),
            &json!({
                "reasoning": true,
                "thinkingLevelMap": { "low": null, "medium": null },
                "samplingParamsByThinkingLevel": { "high": { "temperature": 0.8, "top_k": 64 } },
            }),
        ),
        SimpleStreamOptions {
            reasoning: Some(ThinkingLevel::Low),
            ..SimpleStreamOptions::default()
        },
    )
    .await;

    assert_eq!(payload.get("temperature"), Some(&json!(0.8)));
    assert_eq!(payload.get("top_p"), Some(&json!(0.95)));
    assert_eq!(payload.get("top_k"), Some(&json!(64)));
}

#[tokio::test]
async fn applies_off_sampling_params_when_reasoning_is_disabled() {
    let payload = capture_simple_payload(
        &make_model(
            None,
            &json!({ "samplingParamsByThinkingLevel": { "off": { "temperature": 0.7 } } }),
        ),
        SimpleStreamOptions::default(),
    )
    .await;

    assert_eq!(payload.get("temperature"), Some(&json!(0.7)));
}

#[tokio::test]
async fn merges_stream_option_keys_over_thinking_level_keys() {
    let payload = capture_simple_payload(
        &make_model(
            None,
            &json!({
                "reasoning": true,
                "samplingParamsByThinkingLevel": { "low": { "temperature": 0.6, "top_p": 0.95 } },
            }),
        ),
        SimpleStreamOptions {
            stream: StreamOptions {
                sampling_params: Some(params(&json!({ "top_p": 0.5 }))),
                ..StreamOptions::default()
            },
            reasoning: Some(ThinkingLevel::Low),
            ..SimpleStreamOptions::default()
        },
    )
    .await;

    assert_eq!(payload.get("temperature"), Some(&json!(0.6)));
    assert_eq!(payload.get("top_p"), Some(&json!(0.5)));
}

#[tokio::test]
async fn applies_thinking_level_params_between_model_and_request_params_for_openai_completions() {
    let payload = capture_payload(
        &make_model(
            Some(json!({ "temperature": 1, "top_p": 0.95 })),
            &json!({
                "reasoning": true,
                "samplingParamsByThinkingLevel": { "low": { "temperature": 0.6, "top_k": 64 } },
            }),
        ),
        StreamOptions {
            sampling_params: Some(params(&json!({ "top_p": 0.5 }))),
            ..StreamOptions::default()
        },
        Some("low"),
    )
    .await;

    assert_eq!(payload.get("temperature"), Some(&json!(0.6)));
    assert_eq!(payload.get("top_p"), Some(&json!(0.5)));
    assert_eq!(payload.get("top_k"), Some(&json!(64)));
}

#[tokio::test]
async fn overrides_named_request_fields() {
    let payload = capture_payload(
        &make_model(None, &json!({})),
        StreamOptions {
            temperature: Some(0.0),
            sampling_params: Some(params(&json!({ "temperature": 1 }))),
            ..StreamOptions::default()
        },
        None,
    )
    .await;

    assert_eq!(payload.get("temperature"), Some(&json!(1)));
}
