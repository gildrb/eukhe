//! `OpenRouter` chat models ride `OpenRouter`'s Responses API (the
//! provider routes them to `openai-responses`), the Anthropic
//! models included: the reasoning summary, `reasoning: {enabled: false}`
//! for thinking off, and the top-level `cache_control` of the Anthropic
//! models.

mod openai_responses_support;

use eukhe_ai::providers::openrouter::openrouter_provider;
use eukhe_ai::providers::openrouter_models::OPENROUTER_MODELS;
use eukhe_ai::types::SimpleStreamOptions;
use eukhe_ai::utils::transcript::normalize_context;
use eukhe_types::pi_ai::{Context, ThinkingLevel};
use openai_responses_support::{mock_fetch, CapturedRequest, MockResponse};
use serde_json::json;

async fn capture(id: &str, reasoning: Option<ThinkingLevel>) -> CapturedRequest {
    let model = OPENROUTER_MODELS.get(id).expect("catalog model").clone();
    let (fetch, captured) = mock_fetch(vec![MockResponse::sse("data: [DONE]\n\n")]);
    let mut options = SimpleStreamOptions {
        reasoning,
        ..SimpleStreamOptions::default()
    };
    options.stream.request.api_key = Some("or-key".to_owned());
    options.stream.request.fetch = Some(fetch);
    let context: Context = serde_json::from_value(json!({
        "systemPrompt": "sys",
        "messages": [{ "role": "user", "content": "hi", "timestamp": 1 }],
    }))
    .expect("context");
    let _ = (openrouter_provider().stream_simple)(&model, &normalize_context(context), options)
        .result()
        .await;
    let requests = captured.lock().expect("captured");
    requests.first().cloned().expect("captured request")
}

#[tokio::test]
async fn sends_chat_models_to_responses_with_the_reasoning_summary() {
    for (id, level, effort, cache_control) in [
        (
            "anthropic/claude-haiku-4.5",
            ThinkingLevel::Low,
            "low",
            Some(json!({ "type": "ephemeral" })),
        ),
        (
            "~anthropic/claude-haiku-latest",
            ThinkingLevel::High,
            "high",
            Some(json!({ "type": "ephemeral" })),
        ),
        ("openai/gpt-5.4", ThinkingLevel::Medium, "medium", None),
        (
            "moonshotai/kimi-k2-thinking",
            ThinkingLevel::Low,
            "low",
            None,
        ),
    ] {
        let request = capture(id, Some(level)).await;
        assert_eq!(
            request.url, "https://openrouter.ai/api/v1/responses",
            "{id}"
        );
        let body = &request.body;
        assert_eq!(body["model"], json!(id), "{id}");
        assert_eq!(
            body["reasoning"],
            json!({ "effort": effort, "summary": "auto" }),
            "{id}"
        );
        assert_eq!(body.get("cache_control").cloned(), cache_control, "{id}");
        for field in [
            "thinking",
            "output_config",
            "max_tokens",
            "max_completion_tokens",
        ] {
            assert!(body.get(field).is_none(), "{id} {field}");
        }
    }
}

#[tokio::test]
async fn turns_reasoning_off_with_enabled_false() {
    for id in ["openai/gpt-5.4", "~anthropic/claude-haiku-latest"] {
        let request = capture(id, None).await;
        assert_eq!(
            request.url, "https://openrouter.ai/api/v1/responses",
            "{id}"
        );
        assert_eq!(
            request.body["reasoning"],
            json!({ "enabled": false }),
            "{id}"
        );
    }
}
