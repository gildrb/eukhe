//! Port of `test/anthropic-force-adaptive-thinking.test.ts`.

mod anthropic_support;

use anthropic_support::{builtin_model, capture_simple_payload, model};
use eukhe_pi_ai::types::SimpleStreamOptions;
use eukhe_types::pi_ai::{JsonValue, Model, ThinkingLevel};
use serde_json::json;

fn make_custom_model(compat: Option<JsonValue>) -> Model {
    let mut overrides = json!({
        // Id intentionally does not match any built-in adaptive substring. This
        // mirrors corporate proxy schemes such as `anthropic--claude-opus-latest`.
        "id": "vendor--claude-opus-latest",
        "name": "Vendor Proxy Opus Latest",
        "provider": "vendor-proxy",
        "baseUrl": "http://127.0.0.1:9",
        "reasoning": true,
        "contextWindow": 200_000,
        "maxTokens": 32000,
    });
    if let Some(compat) = compat {
        overrides["compat"] = compat;
    }
    model(&overrides)
}

fn reasoning(level: ThinkingLevel) -> SimpleStreamOptions {
    SimpleStreamOptions {
        reasoning: Some(level),
        ..SimpleStreamOptions::default()
    }
}

#[tokio::test]
async fn sends_legacy_thinking_payload_for_custom_model_ids_by_default() {
    let payload =
        capture_simple_payload(&make_custom_model(None), reasoning(ThinkingLevel::Medium)).await;

    assert_eq!(payload["thinking"]["type"], "enabled");
    assert_eq!(payload.get("output_config"), None);
}

#[tokio::test]
async fn sends_adaptive_thinking_payload_when_compat_force_adaptive_thinking_is_true() {
    let payload = capture_simple_payload(
        &make_custom_model(Some(json!({ "forceAdaptiveThinking": true }))),
        reasoning(ThinkingLevel::Medium),
    )
    .await;

    assert_eq!(
        payload.get("thinking"),
        Some(&json!({ "type": "adaptive", "display": "summarized" }))
    );
    assert_eq!(
        payload.get("output_config"),
        Some(&json!({ "effort": "medium" }))
    );
}

#[tokio::test]
async fn uses_adaptive_thinking_with_native_xhigh_effort_for_claude_fable_5() {
    let payload = capture_simple_payload(
        &builtin_model("anthropic", "claude-fable-5", &json!({})),
        reasoning(ThinkingLevel::Xhigh),
    )
    .await;

    assert_eq!(
        payload.get("thinking"),
        Some(&json!({ "type": "adaptive", "display": "summarized" }))
    );
    assert_eq!(
        payload.get("output_config"),
        Some(&json!({ "effort": "xhigh" }))
    );
}

async fn uses_adaptive_thinking_effort_without_a_token_budget_for_kimi_coding(
    model_id: &str,
    level: ThinkingLevel,
    effort: &str,
) {
    let payload = capture_simple_payload(
        &builtin_model("kimi-coding", model_id, &json!({})),
        reasoning(level),
    )
    .await;

    assert_eq!(
        payload.get("thinking"),
        Some(&json!({ "type": "adaptive", "display": "summarized" }))
    );
    assert_eq!(
        payload.get("output_config"),
        Some(&json!({ "effort": effort }))
    );
}

#[tokio::test]
async fn uses_adaptive_thinking_effort_without_a_token_budget_for_kimi_coding_kimi_for_coding() {
    uses_adaptive_thinking_effort_without_a_token_budget_for_kimi_coding(
        "kimi-for-coding",
        ThinkingLevel::Medium,
        "medium",
    )
    .await;
}

#[tokio::test]
async fn uses_adaptive_thinking_effort_without_a_token_budget_for_kimi_coding_k3() {
    uses_adaptive_thinking_effort_without_a_token_budget_for_kimi_coding(
        "k3",
        ThinkingLevel::Max,
        "max",
    )
    .await;
}

#[tokio::test]
async fn uses_adaptive_thinking_effort_without_a_token_budget_for_kimi_coding_kimi_for_coding_highspeed(
) {
    uses_adaptive_thinking_effort_without_a_token_budget_for_kimi_coding(
        "kimi-for-coding-highspeed",
        ThinkingLevel::Medium,
        "medium",
    )
    .await;
}

#[tokio::test]
async fn allows_built_in_adaptive_models_to_opt_out_with_compat_force_adaptive_thinking_false() {
    let model = builtin_model(
        "anthropic",
        "claude-opus-4-8",
        &json!({ "compat": { "forceAdaptiveThinking": false } }),
    );
    let payload = capture_simple_payload(&model, reasoning(ThinkingLevel::Medium)).await;

    assert_eq!(payload["thinking"]["type"], "enabled");
    assert_eq!(payload.get("output_config"), None);
}

#[tokio::test]
async fn preserves_thinking_type_disabled_when_reasoning_is_off_regardless_of_override() {
    let payload = capture_simple_payload(
        &make_custom_model(Some(json!({ "forceAdaptiveThinking": true }))),
        SimpleStreamOptions::default(),
    )
    .await;

    assert_eq!(
        payload.get("thinking"),
        Some(&json!({ "type": "disabled" }))
    );
    assert_eq!(payload.get("output_config"), None);
}
