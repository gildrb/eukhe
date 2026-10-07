//! Port of `test/anthropic-thinking-binding-e2e.test.ts` (real API; `#[ignore]`d).

mod anthropic_support;

use std::sync::Arc;

use anthropic_support::{builtin_model, context};
use eukhe_pi_ai::api::anthropic_messages::stream;
use eukhe_pi_ai::types::{OnPayload, ProviderStreamOptions};
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, CacheRetention, JsonValue, Model, StopReason,
};
use serde_json::json;

fn model() -> Model {
    builtin_model("anthropic", "claude-fable-5-1", &json!({}))
}

fn user(content: &str, timestamp: u64) -> JsonValue {
    json!({ "role": "user", "content": content, "timestamp": timestamp })
}

/// TS `strictBinding`: turn `drop_block` into `error`.
fn strict_binding() -> OnPayload<Model> {
    Arc::new(|payload, _model| {
        let mut params = payload;
        if let Some(binding) = params
            .get_mut("thinking")
            .and_then(|thinking| thinking.get_mut("block_binding"))
            .filter(|binding| binding.is_object())
        {
            binding["prefix_mismatch_behavior"] = json!("error");
        }
        Box::pin(async move { Ok(Some(params)) })
    })
}

async fn request(ctx: &JsonValue, effort: &str) -> AssistantMessage {
    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = std::env::var("ANTHROPIC_API_KEY").ok();
    options.stream.cache_retention = Some(CacheRetention::None);
    options.stream.max_tokens = Some(1536);
    options.stream.request.on_payload = Some(strict_binding());
    options.extra.insert("thinkingEnabled".into(), json!(true));
    options
        .extra
        .insert("thinkingDisplay".into(), json!("summarized"));
    options.extra.insert("effort".into(), json!(effort));
    stream(&model(), &context(ctx), options).result().await
}

#[tokio::test]
#[ignore = "needs ANTHROPIC_API_KEY; run with --ignored"]
async fn replays_managed_effort_markers_required_by_signed_fable_thinking() {
    let first_user = user(
        "Compute 982451653 multiplied by 961748941. Return only the integer.",
        1,
    );
    let first = request(&json!({ "messages": [first_user] }), "low").await;
    assert_eq!(
        first.stop_reason,
        StopReason::Stop,
        "{:?}",
        first.error_message
    );
    assert!(first.content.iter().any(|block| matches!(
        block,
        AssistantContentBlock::Thinking(thinking)
            if thinking.thinking_signature.as_deref().is_some_and(|signature| !signature.is_empty())
    )));
    assert_eq!(first.provider_thinking_level.as_deref(), Some("low"));

    let second_user = user("Reply with exactly: ok", 2);
    let first_json = serde_json::to_value(&first).expect("assistant");
    let exact = request(
        &json!({ "messages": [first_user, first_json, second_user] }),
        "high",
    )
    .await;
    assert_eq!(
        exact.stop_reason,
        StopReason::Stop,
        "{:?}",
        exact.error_message
    );

    let mut unmanaged_history = first.clone();
    unmanaged_history.provider_thinking_level = None;
    let unmanaged_json = serde_json::to_value(&unmanaged_history).expect("assistant");
    let missing_marker = request(
        &json!({ "messages": [first_user, unmanaged_json, second_user] }),
        "high",
    )
    .await;
    assert_eq!(missing_marker.stop_reason, StopReason::Error);
    let error_message = missing_marker.error_message.unwrap_or_default();
    assert!(
        error_message.contains("Invalid `signature`"),
        "{error_message}"
    );
}
