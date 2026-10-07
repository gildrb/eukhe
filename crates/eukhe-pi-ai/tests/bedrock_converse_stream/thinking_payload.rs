//! Port of `test/bedrock-thinking-payload.test.ts`.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_pi_ai::api::bedrock_converse_stream::stream;
use eukhe_pi_ai::types::ProviderStreamOptions;
use eukhe_pi_ai::utils::transcript::normalize_context;
use eukhe_types::pi_ai::{Context, JsonValue, Model, StopReason};
use serde_json::{json, Value};

use super::support::{capture_payload_hook, get_model, options, user, AfterCapture, EnvGuard};

const THINKING_BINDING_CONTROLS_BETA: &str = "thinking-binding-controls-2026-08-01";

fn adaptive_with_binding() -> Value {
    json!({
        "type": "adaptive",
        "display": "summarized",
        "block_binding": { "prefix_mismatch_behavior": "drop_block" },
    })
}

async fn capture(model: &Model, context: Context, mut options: ProviderStreamOptions) -> JsonValue {
    let _env = EnvGuard::new(&[]).await;
    let slot = Arc::new(Mutex::new(None));
    options.stream.request.on_payload =
        Some(capture_payload_hook(slot.clone(), AfterCapture::Throw));
    let result = stream(model, &normalize_context(context), options)
        .result()
        .await;
    assert_eq!(result.stop_reason, StopReason::Error);
    let payload = slot.lock().unwrap_or_else(PoisonError::into_inner).take();
    payload.expect("Expected Bedrock payload to be captured before request abort")
}

async fn capture_payload(model: &Model, extra: Value) -> Value {
    let mut extra = extra;
    if extra.get("reasoning").is_none() {
        extra["reasoning"] = json!("high");
    }
    let context = Context {
        system_prompt: None,
        messages: vec![user("Hello")],
        tools: None,
    };
    capture(model, context, options(extra)).await
}

fn fields(payload: &Value) -> &Value {
    &payload["additionalModelRequestFields"]
}

fn opus_48() -> Model {
    Model {
        id: "global.anthropic.claude-opus-4-8-v1".into(),
        name: "Claude Opus 4.8 (Global)".into(),
        ..get_model("amazon-bedrock", "global.anthropic.claude-opus-4-6-v1")
    }
}

#[tokio::test]
async fn uses_adaptive_thinking_for_claude_opus_4_8_when_reasoning_is_enabled() {
    let payload = capture_payload(&opus_48(), json!({})).await;
    assert_eq!(fields(&payload)["thinking"], adaptive_with_binding());
    assert_eq!(
        fields(&payload)["output_config"],
        json!({ "effort": "high" })
    );
    assert_eq!(
        fields(&payload)["anthropic_beta"],
        json!([THINKING_BINDING_CONTROLS_BETA])
    );
}

#[tokio::test]
async fn maps_xhigh_reasoning_to_effort_xhigh_for_claude_opus_4_8() {
    let payload = capture_payload(&opus_48(), json!({ "reasoning": "xhigh" })).await;
    assert_eq!(fields(&payload)["thinking"], adaptive_with_binding());
    assert_eq!(
        fields(&payload)["output_config"],
        json!({ "effort": "xhigh" })
    );
    assert_eq!(
        fields(&payload)["anthropic_beta"],
        json!([THINKING_BINDING_CONTROLS_BETA])
    );
}

async fn assert_adaptive_binding(model_id: &str, reasoning: &str, effort: &str) {
    let model = get_model("amazon-bedrock", model_id);
    let payload = capture_payload(&model, json!({ "reasoning": reasoning })).await;
    assert_eq!(
        fields(&payload)["thinking"],
        adaptive_with_binding(),
        "{model_id}"
    );
    assert_eq!(
        fields(&payload)["output_config"],
        json!({ "effort": effort }),
        "{model_id}"
    );
    assert_eq!(
        fields(&payload)["anthropic_beta"],
        json!([THINKING_BINDING_CONTROLS_BETA]),
        "{model_id}"
    );
}

#[tokio::test]
async fn uses_adaptive_thinking_for_claude_fable_5_when_reasoning_is_enabled() {
    assert_adaptive_binding("global.anthropic.claude-fable-5", "high", "high").await;
}

#[tokio::test]
async fn uses_adaptive_thinking_for_claude_sonnet_5_when_reasoning_is_enabled() {
    assert_adaptive_binding("global.anthropic.claude-sonnet-5", "high", "high").await;
}

#[tokio::test]
async fn uses_adaptive_thinking_for_claude_opus_5_when_reasoning_is_enabled() {
    assert_adaptive_binding("global.anthropic.claude-opus-5", "high", "high").await;
}

#[tokio::test]
async fn maps_xhigh_reasoning_to_effort_xhigh_for_claude_opus_5() {
    assert_adaptive_binding("global.anthropic.claude-opus-5", "xhigh", "xhigh").await;
}

#[tokio::test]
async fn maps_xhigh_reasoning_to_effort_xhigh_for_claude_fable_5() {
    assert_adaptive_binding("global.anthropic.claude-fable-5", "xhigh", "xhigh").await;
}

// https://github.com/earendil-works/pi/issues/10324
#[tokio::test]
async fn sends_block_binding_and_the_binding_beta_for_claude_opus_5_5() {
    let model = get_model("amazon-bedrock", "global.anthropic.claude-opus-5-5");
    let payload = capture_payload(&model, json!({})).await;
    assert_eq!(fields(&payload)["thinking"], adaptive_with_binding());
    assert_eq!(
        fields(&payload)["anthropic_beta"],
        json!([THINKING_BINDING_CONTROLS_BETA])
    );
}

// Bedrock rejects block_binding on 4.6 models (#10324).
#[tokio::test]
async fn omits_block_binding_for_4_6_models() {
    for model_id in [
        "global.anthropic.claude-opus-4-6-v1",
        "global.anthropic.claude-sonnet-4-6",
    ] {
        let model = get_model("amazon-bedrock", model_id);
        let payload = capture_payload(&model, json!({})).await;
        assert_eq!(
            fields(&payload)["thinking"],
            json!({ "type": "adaptive", "display": "summarized" }),
            "{model_id}"
        );
        assert!(
            fields(&payload).get("anthropic_beta").is_none(),
            "{model_id}"
        );
    }
}

#[tokio::test]
async fn omits_display_for_govcloud_model_ids_on_non_adaptive_claude_thinking() {
    let model = Model {
        id: "us-gov.anthropic.claude-sonnet-4-5-20250929-v1:0".into(),
        name: "Claude Sonnet 4.5 (GovCloud)".into(),
        ..get_model(
            "amazon-bedrock",
            "us.anthropic.claude-sonnet-4-5-20250929-v1:0",
        )
    };
    let payload = capture_payload(&model, json!({})).await;
    assert_eq!(
        fields(&payload)["thinking"],
        json!({ "type": "enabled", "budget_tokens": 16384 })
    );
    assert_eq!(
        fields(&payload)["anthropic_beta"],
        json!(["interleaved-thinking-2025-05-14"])
    );
}

#[tokio::test]
async fn omits_display_for_govcloud_regions_on_adaptive_claude_thinking() {
    let payload = capture_payload(&opus_48(), json!({ "region": "us-gov-west-1" })).await;
    assert_eq!(fields(&payload)["thinking"], json!({ "type": "adaptive" }));
    assert_eq!(
        fields(&payload)["output_config"],
        json!({ "effort": "high" })
    );
    assert!(fields(&payload).get("anthropic_beta").is_none());
}

#[tokio::test]
#[ignore = "needs AWS credentials (AWS_PROFILE, AWS_ACCESS_KEY_ID+AWS_SECRET_ACCESS_KEY, or AWS_BEARER_TOKEN_BEDROCK); run with --ignored"]
async fn uses_the_model_max_tokens_cap_instead_of_bedrocks_4096_token_default_for_adaptive_claude_models(
) {
    assert!(super::has_bedrock_credentials());
    let model = Model {
        max_tokens: 6000,
        ..get_model("amazon-bedrock", "global.anthropic.claude-sonnet-4-6")
    };
    let context = normalize_context(Context {
        system_prompt: Some(
            "You are a deterministic text generator. Follow the requested output format exactly."
                .into(),
        ),
        messages: vec![user(
            "Output exactly 5200 repetitions of the token alpha, separated by single spaces. Do not number them. Do not use markdown. Do not add any other text.",
        )],
        tools: None,
    });
    let response = stream(&model, &context, options(json!({ "reasoning": "low" })))
        .result()
        .await;
    assert_ne!(
        response.stop_reason,
        StopReason::Error,
        "{:?}",
        response.error_message
    );
    assert!(response.usage.output > 4096);
}

fn profile_model(name: &str, base: &str) -> Model {
    Model {
        id: "arn:aws:bedrock:us-east-1:123456789012:application-inference-profile/my-profile"
            .into(),
        name: name.into(),
        ..get_model("amazon-bedrock", base)
    }
}

#[tokio::test]
async fn uses_adaptive_thinking_when_model_name_contains_the_model_name_but_arn_does_not() {
    let model = profile_model("Claude Opus 4.6", "global.anthropic.claude-opus-4-6-v1");
    let payload = capture_payload(&model, json!({})).await;
    assert_eq!(
        fields(&payload)["thinking"],
        json!({ "type": "adaptive", "display": "summarized" })
    );
    assert_eq!(
        fields(&payload)["output_config"],
        json!({ "effort": "high" })
    );
}

#[tokio::test]
async fn injects_cache_points_when_model_name_identifies_a_supported_claude_model() {
    let model = profile_model("Claude Sonnet 4.6", "global.anthropic.claude-opus-4-6-v1");
    let context = Context {
        system_prompt: Some("You are helpful.".into()),
        messages: vec![user("Hello")],
        tools: None,
    };
    let payload = capture(&model, context, ProviderStreamOptions::default()).await;
    let system = payload["system"].as_array().expect("system");
    assert_eq!(system.len(), 2);
    assert!(system[1].get("cachePoint").is_some());
    let messages = payload["messages"].as_array().expect("messages");
    let last = messages.last().expect("message")["content"]
        .as_array()
        .expect("content")
        .last()
        .cloned()
        .expect("block");
    assert!(last.get("cachePoint").is_some());
}

#[tokio::test]
async fn falls_back_to_fixed_budget_thinking_for_non_adaptive_claude_via_model_name() {
    let model = profile_model(
        "Claude Sonnet 4.5",
        "us.anthropic.claude-sonnet-4-5-20250929-v1:0",
    );
    let payload = capture_payload(&model, json!({})).await;
    assert_eq!(fields(&payload)["thinking"]["type"], json!("enabled"));
    assert!(fields(&payload)["thinking"]["budget_tokens"].is_number());
    assert_eq!(
        fields(&payload)["anthropic_beta"],
        json!(["interleaved-thinking-2025-05-14"])
    );
}
