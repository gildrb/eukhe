//! Port of `test/openai-responses-chatgpt-sign-in.test.ts`.

mod openai_responses_support;

use eukhe_pi_ai::api::openai_responses::stream as stream_openai_responses;
use eukhe_pi_ai::types::ProviderStreamOptions;
use eukhe_pi_ai::utils::transcript::normalize_context;
use eukhe_types::pi_ai::{CacheRetention, Context, JsonValue, Model, TranscriptContext};
use openai_responses_support::{mock_fetch, MockResponse};
use serde_json::json;

fn model_json() -> JsonValue {
    json!({
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
    })
}

fn model_with(patch: &JsonValue) -> Model {
    let mut value = model_json();
    for (key, field) in patch.as_object().expect("patch object") {
        value[key] = field.clone();
    }
    serde_json::from_value(value).expect("model")
}

fn model() -> Model {
    model_with(&json!({}))
}

fn context() -> TranscriptContext {
    normalize_context(
        serde_json::from_value::<Context>(json!({
            "systemPrompt": "",
            "messages": [{ "role": "user", "content": [{ "type": "text", "text": "hi" }], "timestamp": 0 }],
            "tools": [],
        }))
        .expect("context"),
    )
}

async fn capture_payload(api_key: &str, request_model: &Model) -> JsonValue {
    let (fetch, captured) = mock_fetch(vec![MockResponse {
        status: 500,
        content_type: "text/plain;charset=UTF-8".to_owned(),
        body: String::new(),
    }]);
    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = Some(api_key.to_owned());
    options.stream.max_tokens = Some(1000);
    options.stream.temperature = Some(0.5);
    options.stream.cache_retention = Some(CacheRetention::Long);
    options.stream.request.fetch = Some(fetch);
    stream_openai_responses(request_model, &context(), options)
        .result()
        .await;
    let requests = captured
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    requests
        .first()
        .map(|request| request.body.clone())
        .expect("Request payload was not captured")
}

#[tokio::test]
async fn omits_request_fields_that_token_sharing_rejects() {
    let payload = capture_payload("chatgpt-access-token", &model()).await;

    assert_eq!(payload.get("max_output_tokens"), None);
    assert_eq!(payload.get("temperature"), None);
    assert_eq!(payload.get("prompt_cache_retention"), None);
}

#[tokio::test]
async fn omits_prompt_cache_options_on_models_with_explicit_prompt_cache_mode() {
    let explicit_cache_model =
        model_with(&json!({ "compat": { "supportsExplicitPromptCacheMode": true } }));

    let sign_in_payload = capture_payload("chatgpt-access-token", &explicit_cache_model).await;
    let api_key_payload = capture_payload("sk-proj-test", &explicit_cache_model).await;

    assert_eq!(sign_in_payload.get("prompt_cache_options"), None);
    assert_eq!(
        api_key_payload["prompt_cache_options"],
        json!({ "ttl": "30m" })
    );
}

#[tokio::test]
async fn keeps_those_fields() {
    for (name, api_key, request_model) in [
        ("OpenAI API keys", "sk-proj-test", model()),
        (
            "other OpenAI-compatible endpoints",
            "gateway-key",
            model_with(&json!({ "baseUrl": "https://gateway.example.com/v1" })),
        ),
    ] {
        let payload = capture_payload(api_key, &request_model).await;

        assert_eq!(payload["max_output_tokens"], json!(1000), "{name}");
        assert_eq!(payload["temperature"], json!(0.5), "{name}");
        assert_eq!(payload["prompt_cache_retention"], json!("24h"), "{name}");
    }
}
