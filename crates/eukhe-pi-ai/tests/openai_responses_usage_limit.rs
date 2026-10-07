//! Port of `test/openai-responses-usage-limit.test.ts`.

mod openai_responses_support;

use eukhe_pi_ai::api::openai_responses::stream as stream_openai_responses;
use eukhe_pi_ai::types::ProviderStreamOptions;
use eukhe_pi_ai::utils::transcript::normalize_context;
use eukhe_types::pi_ai::{Context, JsonValue, Model, StopReason};
use openai_responses_support::{mock_fetch, MockResponse};
use serde_json::json;

fn usage_limit_error() -> JsonValue {
    json!({
        "code": "subscription_sharing_usage_limit_exceeded",
        "message": "Usage limit reached.",
    })
}

fn model() -> Model {
    serde_json::from_value(json!({
        "id": "gpt-5-mini",
        "name": "GPT-5 Mini",
        "api": "openai-responses",
        "provider": "openai",
        "baseUrl": "https://api.openai.com/v1",
        "reasoning": true,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 400_000,
        "maxTokens": 128_000,
    }))
    .expect("model")
}

async fn get_error_message(response: MockResponse) -> Option<String> {
    let context = normalize_context(
        serde_json::from_value::<Context>(json!({
            "systemPrompt": "",
            "messages": [{ "role": "user", "content": [{ "type": "text", "text": "hi" }], "timestamp": 0 }],
            "tools": [],
        }))
        .expect("context"),
    );
    let (fetch, _) = mock_fetch(vec![response]);
    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = Some("test".to_owned());
    options.stream.request.fetch = Some(fetch);
    let result = stream_openai_responses(&model(), &context, options)
        .result()
        .await;
    assert_eq!(result.stop_reason, StopReason::Error);
    result.error_message
}

#[tokio::test]
async fn links_to_chatgpt_usage_when_the_request_is_rejected() {
    let mut error = usage_limit_error();
    error["type"] = json!("rate_limit_error");
    let response = MockResponse::json(429, json!({ "error": error }).to_string());

    let error_message = get_error_message(response).await.expect("error message");

    assert!(
        error_message.contains("subscription_sharing_usage_limit_exceeded"),
        "{error_message}"
    );
    assert!(
        error_message.contains("Check your ChatGPT usage: https://chatgpt.com/settings/usage"),
        "{error_message}"
    );
}

#[tokio::test]
async fn links_to_chatgpt_usage_when_the_stream_fails() {
    let event = json!({
        "type": "response.failed",
        "sequence_number": 0,
        "response": { "id": "resp_failed", "status": "failed", "error": usage_limit_error() },
    });
    let response = MockResponse::sse(format!("event: response.failed\ndata: {event}\n\n"));

    let error_message = get_error_message(response).await.expect("error message");

    assert!(
        error_message.contains("subscription_sharing_usage_limit_exceeded: Usage limit reached."),
        "{error_message}"
    );
    assert!(
        error_message.contains("Check your ChatGPT usage: https://chatgpt.com/settings/usage"),
        "{error_message}"
    );
}
