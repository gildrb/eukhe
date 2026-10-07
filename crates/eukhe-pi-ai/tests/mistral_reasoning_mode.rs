//! Port of `test/mistral-reasoning-mode.test.ts`.

mod mistral_support;

use eukhe_pi_ai::api::mistral_conversations::stream_simple;
use eukhe_pi_ai::types::SimpleStreamOptions;
use eukhe_pi_ai::utils::transcript::normalize_context;
use eukhe_types::pi_ai::{CacheRetention, Context, JsonValue, Model, ThinkingLevel};
use mistral_support::{capture_payload, payload_of};
use serde_json::json;

fn none_high_levels() -> JsonValue {
    json!({
        "off": "none", "minimal": null, "low": null, "medium": null,
        "high": "high", "xhigh": null, "max": null,
    })
}

fn glm_5_2_levels() -> JsonValue {
    let mut levels = none_high_levels();
    levels["max"] = json!("max");
    levels
}

fn glm_5_3_levels() -> JsonValue {
    let mut levels = none_high_levels();
    levels["off"] = JsonValue::Null;
    levels["low"] = json!("low");
    levels["max"] = json!("max");
    levels
}

fn make_model(id: &str, reasoning: bool, thinking_level_map: Option<JsonValue>) -> Model {
    let mut model = json!({
        "id": id,
        "name": id,
        "api": "mistral-conversations",
        "provider": "mistral",
        "baseUrl": "http://127.0.0.1:9",
        "reasoning": reasoning,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 128_000,
        "maxTokens": 16384,
    });
    if let Some(map) = thinking_level_map {
        model["thinkingLevelMap"] = map;
    }
    serde_json::from_value(model).expect("model")
}

fn level(name: &str) -> ThinkingLevel {
    serde_json::from_value(json!(name)).expect("thinking level")
}

/// TS `capturePayload(model, options)`.
async fn capture(model: &Model, mut options: SimpleStreamOptions) -> JsonValue {
    let context = normalize_context(
        serde_json::from_value::<Context>(json!({
            "messages": [{ "role": "user", "content": "Hello", "timestamp": 1 }],
        }))
        .expect("context"),
    );
    let (on_payload, store) = capture_payload(|_| None);
    options.stream.request.api_key = Some("fake-key".into());
    options.stream.request.on_payload = Some(on_payload);
    let _ = stream_simple(model, &context, options).result().await;
    payload_of(&store)
}

fn with_reasoning(name: &str) -> SimpleStreamOptions {
    SimpleStreamOptions {
        reasoning: Some(level(name)),
        ..SimpleStreamOptions::default()
    }
}

#[tokio::test]
async fn uses_prompt_mode_for_reasoning_models_without_a_thinking_level_map() {
    let payload = capture(
        &make_model("magistral-medium-latest", true, None),
        with_reasoning("medium"),
    )
    .await;

    assert_eq!(payload["promptMode"], json!("reasoning"));
    assert!(payload.get("reasoningEffort").is_none());
}

#[tokio::test]
async fn omits_reasoning_controls_for_magistral_when_thinking_is_off() {
    let payload = capture(
        &make_model("magistral-medium-latest", true, None),
        SimpleStreamOptions::default(),
    )
    .await;

    assert!(payload.get("promptMode").is_none());
    assert!(payload.get("reasoningEffort").is_none());
}

/// Regression for #8700 and #9375: Medium and GLM-5.2 ignore Magistral's
/// `prompt_mode`.
const EFFORT_MODELS: [&str; 3] = ["mistral-small-2603", "mistral-medium-latest", "zai-glm-5-2"];

fn effort_map(model_id: &str) -> JsonValue {
    if model_id == "zai-glm-5-2" {
        glm_5_2_levels()
    } else {
        none_high_levels()
    }
}

#[tokio::test]
async fn uses_reasoning_effort_when_thinking_is_enabled() {
    for model_id in EFFORT_MODELS {
        let model = make_model(model_id, true, Some(effort_map(model_id)));
        let payload = capture(&model, with_reasoning("high")).await;

        assert_eq!(payload["reasoningEffort"], json!("high"), "{model_id}");
        assert!(payload.get("promptMode").is_none(), "{model_id}");
    }
}

#[tokio::test]
async fn clamps_unsupported_levels_to_a_supported_effort() {
    for model_id in EFFORT_MODELS {
        let model = make_model(model_id, true, Some(effort_map(model_id)));
        let payload = capture(&model, with_reasoning("low")).await;

        assert_eq!(payload["reasoningEffort"], json!("high"), "{model_id}");
    }
}

#[tokio::test]
async fn sends_reasoning_effort_none_when_thinking_is_off() {
    for model_id in EFFORT_MODELS {
        let model = make_model(model_id, true, Some(effort_map(model_id)));
        let payload = capture(&model, SimpleStreamOptions::default()).await;

        assert_eq!(payload["reasoningEffort"], json!("none"), "{model_id}");
        assert!(payload.get("promptMode").is_none(), "{model_id}");
    }
}

/// Regression for #9678: requested levels must reach Mistral-hosted GLM models.
#[tokio::test]
async fn sends_max_for_glm_5_2() {
    let model = make_model("zai-glm-5-2", true, Some(glm_5_2_levels()));
    let payload = capture(&model, with_reasoning("max")).await;

    assert_eq!(payload["reasoningEffort"], json!("max"));
}

#[tokio::test]
async fn zai_glm_5_3_sends_reasoning_effort() {
    for name in ["low", "high", "max"] {
        let model = make_model("zai-glm-5-3", true, Some(glm_5_3_levels()));
        let payload = capture(&model, with_reasoning(name)).await;

        assert_eq!(payload["reasoningEffort"], json!(name));
        assert!(payload.get("promptMode").is_none());
    }
}

#[tokio::test]
async fn zai_glm_5_3_maps_medium_to_high() {
    let model = make_model("zai-glm-5-3", true, Some(glm_5_3_levels()));
    let payload = capture(&model, with_reasoning("medium")).await;

    assert_eq!(payload["reasoningEffort"], json!("high"));
}

/// Regression for #8700: reasoning controls must respect the model's
/// reasoning capability.
#[tokio::test]
async fn omits_reasoning_controls_for_non_reasoning_models() {
    let payload = capture(
        &make_model("mistral-medium-2505", false, None),
        with_reasoning("medium"),
    )
    .await;

    assert!(payload.get("reasoningEffort").is_none());
    assert!(payload.get("promptMode").is_none());
}

#[tokio::test]
async fn uses_the_session_id_as_prompt_cache_key() {
    let mut options = SimpleStreamOptions::default();
    options.stream.session_id = Some("session-123".into());
    let payload = capture(&make_model("mistral-large-latest", false, None), options).await;

    assert_eq!(payload["promptCacheKey"], json!("session-123"));
}

#[tokio::test]
async fn omits_prompt_cache_key_when_cache_retention_is_disabled() {
    let mut options = SimpleStreamOptions::default();
    options.stream.session_id = Some("session-123".into());
    options.stream.cache_retention = Some(CacheRetention::None);
    let payload = capture(&make_model("mistral-large-latest", false, None), options).await;

    assert!(payload.get("promptCacheKey").is_none());
}
