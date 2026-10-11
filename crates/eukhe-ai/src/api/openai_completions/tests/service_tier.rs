//! eukhe addition: the `service_tier` request field and response-tier
//! pricing of the `openai-completions` module (no TS counterpart).

use serde_json::json;

use super::support::{capture_payload, run_with_chunks, test_model, user_context};
use crate::api::openai_completions::OpenAICompletionsOptions;
use crate::types::{JsonValue, Model, ServiceTier, StopReason, UsageCost};

fn options_with_tier(service_tier: ServiceTier) -> OpenAICompletionsOptions {
    let mut options = OpenAICompletionsOptions::default();
    options.stream.service_tier = Some(service_tier);
    options
}

#[tokio::test]
async fn forwards_service_tier_for_openai() {
    let payload = capture_payload(
        &test_model(json!({ "provider": "openai" })),
        &user_context("hi"),
        options_with_tier(ServiceTier::Flex),
    )
    .await;

    assert_eq!(payload.get("service_tier"), Some(&json!("flex")));
}

#[tokio::test]
async fn forwards_service_tier_for_openrouter() {
    let payload = capture_payload(
        &test_model(json!({
            "provider": "openrouter",
            "baseUrl": "https://openrouter.ai/api/v1",
        })),
        &user_context("hi"),
        options_with_tier(ServiceTier::Priority),
    )
    .await;

    assert_eq!(payload.get("service_tier"), Some(&json!("priority")));
}

#[tokio::test]
async fn does_not_forward_service_tier_for_prime_inference() {
    let payload = capture_payload(
        &test_model(json!({
            "provider": "prime-inference",
            "baseUrl": "https://api.pinference.ai/api/v1",
        })),
        &user_context("hi"),
        options_with_tier(ServiceTier::Flex),
    )
    .await;

    assert_eq!(payload.get("service_tier"), None);
}

#[tokio::test]
async fn omits_service_tier_when_not_requested() {
    let payload = capture_payload(
        &test_model(json!({ "provider": "openai" })),
        &user_context("hi"),
        OpenAICompletionsOptions::default(),
    )
    .await;

    assert_eq!(payload.get("service_tier"), None);
}

fn priced_model(provider: &str, base_url: &str) -> Model {
    test_model(json!({
        "provider": provider,
        "baseUrl": base_url,
        "cost": { "input": 2, "output": 8, "cacheRead": 0.5, "cacheWrite": 0 },
    }))
}

/// The stream's final cost when the server reports `service_tier` (if any)
/// on its chunks.
async fn response_cost(model: &Model, service_tier: Option<&str>) -> UsageCost {
    let mut chunks = vec![
        json!({ "id": "chatcmpl-tier", "choices": [{ "index": 0, "delta": { "content": "hi" } }] }),
        json!({
            "id": "chatcmpl-tier",
            "choices": [{ "index": 0, "delta": {}, "finish_reason": "stop" }],
            "usage": {
                "prompt_tokens": 1200,
                "completion_tokens": 300,
                "prompt_tokens_details": { "cached_tokens": 200 },
            },
        }),
    ];
    if let Some(service_tier) = service_tier {
        for chunk in &mut chunks {
            chunk
                .as_object_mut()
                .expect("chunk object")
                .insert("service_tier".to_owned(), JsonValue::from(service_tier));
        }
    }
    let (_, _, message) = run_with_chunks(
        model,
        &user_context("hi"),
        OpenAICompletionsOptions::default(),
        chunks,
    )
    .await;
    assert_eq!(message.stop_reason, StopReason::Stop);
    message.usage.cost
}

fn scaled(cost: UsageCost, multiplier: f64) -> UsageCost {
    let input = cost.input * multiplier;
    let output = cost.output * multiplier;
    let cache_read = cost.cache_read * multiplier;
    let cache_write = cost.cache_write * multiplier;
    UsageCost {
        input,
        output,
        cache_read,
        cache_write,
        total: input + output + cache_read + cache_write,
    }
}

#[tokio::test]
async fn halves_the_openai_cost_when_the_response_reports_the_flex_tier() {
    let model = priced_model("openai", "https://api.openai.com/v1");
    let baseline = response_cost(&model, None).await;
    let flex = response_cost(&model, Some("flex")).await;

    assert!(baseline.total > 0.0, "{baseline:?}");
    assert_eq!(flex, scaled(baseline, 0.5));
}

#[tokio::test]
async fn keeps_the_openai_cost_for_the_default_tier() {
    let model = priced_model("openai", "https://api.openai.com/v1");
    let baseline = response_cost(&model, None).await;
    let default_tier = response_cost(&model, Some("default")).await;

    assert_eq!(default_tier, baseline);
}

#[tokio::test]
async fn does_not_reprice_gateway_responses_reporting_the_flex_tier() {
    let model = priced_model("openrouter", "https://openrouter.ai/api/v1");
    let baseline = response_cost(&model, None).await;
    let flex = response_cost(&model, Some("flex")).await;

    assert_eq!(flex, baseline);
}
