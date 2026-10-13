//! Port of `test/anthropic-temperature-compat.test.ts`.

mod anthropic_support;

use anthropic_support::{builtin_model, capture_simple_payload, collect, model, ok_fetch};
use eukhe_ai::types::SimpleStreamOptions;
use eukhe_types::pi_ai::{
    AdjustedField, AdjustmentReason, Context, JsonValue, Model, RequestAdjustment, StopReason,
};
use serde_json::json;

fn make_custom_model(compat: &JsonValue) -> Model {
    model(&json!({
        "id": "vendor--claude-opus-4-7",
        "name": "Vendor Proxy Opus 4.7",
        "provider": "vendor-proxy",
        "baseUrl": "http://127.0.0.1:9",
        "reasoning": true,
        "contextWindow": 200_000,
        "maxTokens": 32000,
        "compat": compat,
    }))
}

fn temperature(value: f64) -> SimpleStreamOptions {
    let mut options = SimpleStreamOptions::default();
    options.stream.temperature = Some(value);
    options
}

#[tokio::test]
async fn omits_temperature_for_claude_opus_4_7() {
    let payload = capture_simple_payload(
        &builtin_model("anthropic", "claude-opus-4-7", &json!({})),
        temperature(0.0),
    )
    .await;

    assert_eq!(payload.get("temperature"), None);
}

#[tokio::test]
async fn omits_temperature_for_claude_opus_4_8() {
    let payload = capture_simple_payload(
        &builtin_model("anthropic", "claude-opus-4-8", &json!({})),
        temperature(0.0),
    )
    .await;

    assert_eq!(payload.get("temperature"), None);
}

#[tokio::test]
async fn omits_default_temperature_for_claude_opus_4_7() {
    let payload = capture_simple_payload(
        &builtin_model("anthropic", "claude-opus-4-7", &json!({})),
        temperature(1.0),
    )
    .await;

    assert_eq!(payload.get("temperature"), None);
}

#[tokio::test]
async fn keeps_temperature_for_claude_opus_4_6() {
    let payload = capture_simple_payload(
        &builtin_model("anthropic", "claude-opus-4-6", &json!({})),
        temperature(0.0),
    )
    .await;

    assert_eq!(
        payload.get("temperature").and_then(JsonValue::as_f64),
        Some(0.0)
    );
}

#[tokio::test]
async fn keeps_temperature_for_claude_sonnet_4_6() {
    let payload = capture_simple_payload(
        &builtin_model("anthropic", "claude-sonnet-4-6", &json!({})),
        temperature(0.0),
    )
    .await;

    assert_eq!(
        payload.get("temperature").and_then(JsonValue::as_f64),
        Some(0.0)
    );
}

#[tokio::test]
async fn omits_temperature_for_custom_models_with_supports_temperature_disabled() {
    let payload = capture_simple_payload(
        &make_custom_model(&json!({ "supportsTemperature": false })),
        temperature(0.0),
    )
    .await;

    assert_eq!(payload.get("temperature"), None);
}

#[tokio::test]
async fn records_the_dropped_temperature_on_the_final_message() {
    let (fetch, _) = ok_fetch();
    let mut options = temperature(0.5);
    options.stream.request.api_key = Some("fake-key".into());
    options.stream.request.fetch = Some(fetch);
    let context: Context = serde_json::from_value(json!({
        "messages": [{ "role": "user", "content": "Hello", "timestamp": 1 }],
    }))
    .expect("context");

    let stream = eukhe_ai::compat::stream_simple(
        &make_custom_model(&json!({ "supportsTemperature": false })),
        context,
        options,
    )
    .expect("stream");
    let (_, message) = collect(stream).await;

    assert_eq!(message.stop_reason, StopReason::Stop);
    assert_eq!(
        message.adjustments,
        [RequestAdjustment::dropped(
            AdjustedField::Temperature,
            AdjustmentReason::UnsupportedByModel,
        )]
    );
}
