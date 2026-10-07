//! Port of `test/anthropic-cache-write-1h-cost.test.ts`.

mod anthropic_support;

use anthropic_support::{collect, context, mock_fetch, sse_of, MockResponse};
use eukhe_pi_ai::api::anthropic_messages::{stream_anthropic, AnthropicOptions};
use eukhe_pi_ai::compat::get_model;
use eukhe_types::pi_ai::{AssistantMessage, JsonValue, Model, TranscriptContext};
use serde_json::json;

fn events_with_cache_creation(cache_creation: Option<JsonValue>) -> Vec<JsonValue> {
    let mut start_usage = json!({
        "input_tokens": 100,
        "output_tokens": 0,
        "cache_read_input_tokens": 0,
        "cache_creation_input_tokens": 1_000_000,
    });
    if let Some(cache_creation) = cache_creation {
        start_usage["cache_creation"] = cache_creation;
    }
    vec![
        json!({ "type": "message_start", "message": { "id": "msg_test", "usage": start_usage } }),
        json!({ "type": "content_block_start", "index": 0, "content_block": { "type": "text", "text": "" } }),
        json!({ "type": "content_block_delta", "index": 0, "delta": { "type": "text_delta", "text": "Hi" } }),
        json!({ "type": "content_block_stop", "index": 0 }),
        json!({
            "type": "message_delta",
            "delta": { "stop_reason": "end_turn" },
            "usage": {
                "input_tokens": 100,
                "output_tokens": 5,
                "cache_read_input_tokens": 0,
                "cache_creation_input_tokens": 1_000_000,
            },
        }),
        json!({ "type": "message_stop" }),
    ]
}

// claude-opus-4-8: input 5, cacheWrite (5m) 6.25 per Mtok. 1h write = 2x input = 10.
fn hi_context() -> TranscriptContext {
    context(&json!({ "messages": [{ "role": "user", "content": "hi", "timestamp": 1 }] }))
}

async fn run(model: &Model, events: &[JsonValue]) -> AssistantMessage {
    let (fetch, _) = mock_fetch(MockResponse::sse(sse_of(events)));
    let mut options = AnthropicOptions::default();
    options.stream.request.api_key = Some("sk-test".into());
    options.stream.request.fetch = Some(fetch);
    collect(stream_anthropic(model, &hi_context(), options))
        .await
        .1
}

fn assert_close(actual: f64, expected: f64) {
    assert!((actual - expected).abs() < 5e-11, "{actual} != {expected}");
}

#[tokio::test]
async fn prices_the_1h_portion_at_2x_input_and_the_rest_at_the_5m_rate() {
    let model = get_model("anthropic", "claude-opus-4-8").expect("model");
    let result = run(
        &model,
        &events_with_cache_creation(Some(json!({
            "ephemeral_5m_input_tokens": 600_000,
            "ephemeral_1h_input_tokens": 400_000,
        }))),
    )
    .await;

    assert_eq!(result.usage.cache_write, 1_000_000);
    assert_eq!(result.usage.cache_write_1h, Some(400_000));
    // 600k * 6.25/Mtok + 400k * 10/Mtok = 3.75 + 4.0 = 7.75
    assert_close(result.usage.cost.cache_write, 7.75);
}

// Regression for #9210: Vercel AI Gateway sends cache usage in message_delta, not message_start.
#[tokio::test]
async fn prices_1h_cache_writes_reported_only_in_message_delta() {
    let model = get_model("vercel-ai-gateway", "anthropic/claude-haiku-4.5").expect("model");
    let result = run(
        &model,
        &[
            json!({ "type": "message_start", "message": { "id": "msg_test", "usage": { "input_tokens": 0, "output_tokens": 0 } } }),
            json!({
                "type": "message_delta",
                "delta": { "stop_reason": "end_turn" },
                "usage": {
                    "input_tokens": 3,
                    "output_tokens": 4,
                    "cache_creation_input_tokens": 6535,
                    "cache_creation": { "ephemeral_5m_input_tokens": 0, "ephemeral_1h_input_tokens": 6535 },
                },
            }),
            json!({ "type": "message_stop" }),
        ],
    )
    .await;

    assert_eq!(result.usage.cache_write, 6535);
    assert_eq!(result.usage.cache_write_1h, Some(6535));
    assert_close(
        result.usage.cost.cache_write,
        (6535.0 * model.cost.input * 2.0) / 1_000_000.0,
    );
}

#[tokio::test]
async fn falls_back_to_the_5m_rate_when_no_breakdown_is_reported() {
    let model = get_model("anthropic", "claude-opus-4-8").expect("model");
    let result = run(&model, &events_with_cache_creation(None)).await;

    assert_eq!(result.usage.cache_write, 1_000_000);
    assert_eq!(result.usage.cache_write_1h.unwrap_or(0), 0);
    // 1M * 6.25/Mtok = 6.25
    assert_close(result.usage.cost.cache_write, 6.25);
}
