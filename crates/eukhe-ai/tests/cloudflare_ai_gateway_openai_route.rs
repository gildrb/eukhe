//! Cloudflare AI Gateway's `OpenAI` models ride chat completions like omp's
//! `api-routes provider="cloudflare-ai-gateway"` (`route "openai-completions"
//! prefix="openai/"`, `catalog/src/compat/rules/runtime/behavior.kdl:137-141`;
//! `ai/src/registry/cloudflare-ai-gateway.ts:57-82`).

mod openai_responses_support;

use eukhe_ai::providers::cloudflare_ai_gateway::cloudflare_ai_gateway_provider;
use eukhe_ai::providers::cloudflare_ai_gateway_models::CLOUDFLARE_AI_GATEWAY_MODELS;
use eukhe_ai::types::{ProviderEnv, SimpleStreamOptions};
use eukhe_ai::utils::transcript::normalize_context;
use eukhe_types::pi_ai::{Context, ThinkingLevel};
use openai_responses_support::{mock_fetch, MockResponse};
use serde_json::json;

#[tokio::test]
async fn sends_openai_models_as_chat_completions_with_reasoning_effort() {
    for (id, level, effort) in [
        ("gpt-5.4", ThinkingLevel::Low, "low"),
        ("gpt-5", ThinkingLevel::Minimal, "minimal"),
        ("gpt-5.5", ThinkingLevel::High, "high"),
    ] {
        let model = CLOUDFLARE_AI_GATEWAY_MODELS
            .get(id)
            .expect("catalog model")
            .clone();
        assert_eq!(model.api, "openai-responses", "{id}");
        let (fetch, captured) = mock_fetch(vec![MockResponse::sse("data: [DONE]\n\n")]);
        let mut options = SimpleStreamOptions {
            reasoning: Some(level),
            ..SimpleStreamOptions::default()
        };
        options.stream.request.api_key = Some("cf-token".to_owned());
        options.stream.request.fetch = Some(fetch);
        options.stream.request.env = Some(ProviderEnv::from([
            ("CLOUDFLARE_ACCOUNT_ID".to_owned(), "acct".to_owned()),
            ("CLOUDFLARE_GATEWAY_ID".to_owned(), "gw".to_owned()),
        ]));
        let context: Context = serde_json::from_value(json!({
            "systemPrompt": "sys",
            "messages": [{ "role": "user", "content": "hi", "timestamp": 1 }],
        }))
        .expect("context");

        let _ = (cloudflare_ai_gateway_provider().stream_simple)(
            &model,
            &normalize_context(context),
            options,
        )
        .result()
        .await;

        let request = captured
            .lock()
            .expect("captured")
            .first()
            .cloned()
            .expect("captured request");
        assert_eq!(
            request.url, "https://gateway.ai.cloudflare.com/v1/acct/gw/openai/chat/completions",
            "{id}"
        );
        let body = &request.body;
        assert_eq!(body["model"], json!(id), "{id}");
        assert_eq!(body["reasoning_effort"], json!(effort), "{id}");
        assert_eq!(body["store"], json!(false), "{id}");
        assert!(body.get("reasoning").is_none(), "{id}");
        assert!(body.get("max_tokens").is_none(), "{id}");
        assert_eq!(body["messages"][0]["role"], json!("system"), "{id}");
    }
}
