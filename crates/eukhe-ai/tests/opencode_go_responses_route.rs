//! `OpenCode` Go's `DeepSeek` V4 Flash rides the gateway's Responses endpoint
//! like omp's `api-routes provider="opencode-go"` (`route "openai-responses"
//! exact="deepseek-v4-flash"`, `catalog/src/compat/rules/runtime/behavior.kdl:294-304`).

mod openai_responses_support;

use eukhe_ai::providers::opencode_go::opencode_go_provider;
use eukhe_ai::providers::opencode_go_models::OPENCODE_GO_MODELS;
use eukhe_ai::types::SimpleStreamOptions;
use eukhe_ai::utils::transcript::normalize_context;
use eukhe_types::pi_ai::{Context, ThinkingLevel};
use openai_responses_support::{mock_fetch, CapturedRequest, MockResponse};
use serde_json::json;

async fn capture(id: &str, reasoning: Option<ThinkingLevel>) -> CapturedRequest {
    let model = OPENCODE_GO_MODELS.get(id).expect("catalog model").clone();
    let (fetch, captured) = mock_fetch(vec![MockResponse::sse("data: [DONE]\n\n")]);
    let mut options = SimpleStreamOptions {
        reasoning,
        ..SimpleStreamOptions::default()
    };
    options.stream.request.api_key = Some("oc-key".to_owned());
    options.stream.request.fetch = Some(fetch);
    let context: Context = serde_json::from_value(json!({
        "messages": [{ "role": "user", "content": "hi", "timestamp": 1 }],
    }))
    .expect("context");
    let _ = (opencode_go_provider().stream_simple)(&model, &normalize_context(context), options)
        .result()
        .await;
    let requests = captured.lock().expect("captured");
    requests.first().cloned().expect("captured request")
}

#[tokio::test]
async fn sends_deepseek_v4_flash_to_responses() {
    let request = capture("deepseek-v4-flash", Some(ThinkingLevel::Low)).await;
    assert_eq!(request.url, "https://opencode.ai/zen/go/v1/responses");
    assert_eq!(
        request.body["reasoning"],
        json!({ "effort": "low", "summary": "auto" })
    );
    assert!(request.body.get("reasoning_effort").is_none());
    assert!(request.body.get("thinking").is_none());

    let off = capture("deepseek-v4-flash", None).await;
    assert_eq!(off.body["reasoning"], json!({ "effort": "low" }));
}

#[tokio::test]
async fn keeps_the_other_chat_models_on_chat_completions() {
    let request = capture("deepseek-v4-pro", Some(ThinkingLevel::Low)).await;
    assert_eq!(
        request.url,
        "https://opencode.ai/zen/go/v1/chat/completions"
    );
}
