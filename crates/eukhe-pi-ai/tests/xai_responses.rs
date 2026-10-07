//! Port of `test/xai-responses.test.ts`.

mod openai_responses_support;

use eukhe_pi_ai::api::{openai_completions, openai_responses};
use eukhe_pi_ai::models::get_supported_thinking_levels;
use eukhe_pi_ai::providers::xai::xai_provider;
use eukhe_pi_ai::providers::xai_models::XAI_MODELS;
use eukhe_pi_ai::types::ProviderStreamOptions;
use eukhe_pi_ai::utils::pi_user_agent::get_pi_user_agent;
use eukhe_pi_ai::utils::transcript::normalize_context;
use eukhe_types::pi_ai::{CacheRetention, Context, JsonValue, Model, StopReason};
use openai_responses_support::{mock_fetch, sse_events, CapturedRequest, MockResponse};
use serde_json::json;

fn completed_response() -> MockResponse {
    let event = json!({
        "type": "response.completed",
        "sequence_number": 0,
        "response": {
            "id": "resp_xai_test",
            "status": "completed",
            "output": [],
            "usage": {
                "input_tokens": 1,
                "output_tokens": 1,
                "total_tokens": 2,
                "input_tokens_details": { "cached_tokens": 0 },
            },
        },
    });
    MockResponse::sse(format!("{}data: [DONE]\n\n", sse_events(&[event])))
}

fn custom_completions_model() -> Model {
    serde_json::from_value(json!({
        "id": "grok-custom",
        "name": "Grok Custom",
        "api": "openai-completions",
        "provider": "xai",
        "baseUrl": "https://api.x.ai/v1",
        "reasoning": false,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 128_000,
        "maxTokens": 16384,
    }))
    .expect("model")
}

fn hello_context() -> Context {
    serde_json::from_value(
        json!({ "messages": [{ "role": "user", "content": "hello", "timestamp": 1 }] }),
    )
    .expect("context")
}

fn xai(id: &str) -> Model {
    XAI_MODELS.get(id).expect("xai model").clone()
}

fn user_agent_headers(user_agent: Option<&str>) -> Option<eukhe_types::pi_ai::ProviderHeaders> {
    user_agent.map(|value| {
        [("User-Agent".to_owned(), Some(value.to_owned()))]
            .into_iter()
            .collect()
    })
}

async fn capture_completions_user_agent(user_agent: Option<&str>) -> Option<String> {
    let chunks = [
        json!({ "id": "chatcmpl-ua", "choices": [{ "delta": { "content": "ok" }, "finish_reason": null, "index": 0 }] }),
        json!({
            "id": "chatcmpl-ua",
            "choices": [{ "delta": {}, "finish_reason": "stop", "index": 0 }],
            "usage": {
                "prompt_tokens": 1,
                "completion_tokens": 1,
                "prompt_tokens_details": { "cached_tokens": 0 },
                "completion_tokens_details": { "reasoning_tokens": 0 },
            },
        }),
    ];
    let (fetch, captured) = mock_fetch(vec![MockResponse::sse(format!(
        "{}data: [DONE]\n\n",
        sse_events(&chunks)
    ))]);
    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = Some("xai-test-token".to_owned());
    options.stream.request.headers = user_agent_headers(user_agent);
    options.stream.request.fetch = Some(fetch);

    let result = openai_completions::stream(
        &custom_completions_model(),
        &normalize_context(hello_context()),
        options,
    )
    .result()
    .await;

    assert_eq!(
        result.stop_reason,
        StopReason::Stop,
        "{:?}",
        result.error_message
    );
    let requests = captured.lock().expect("captured");
    requests
        .last()
        .and_then(|request| request.header("user-agent"))
}

/// Options of the TS `OpenAIResponsesOptions` literals.
struct ResponsesOptions {
    session_id: Option<&'static str>,
    cache_retention: Option<CacheRetention>,
    reasoning_effort: Option<&'static str>,
    user_agent: Option<&'static str>,
}

impl ResponsesOptions {
    const NONE: Self = Self {
        session_id: None,
        cache_retention: None,
        reasoning_effort: None,
        user_agent: None,
    };
}

async fn capture_request(
    model: &Model,
    context: Context,
    options: ResponsesOptions,
) -> CapturedRequest {
    let (fetch, captured) = mock_fetch(vec![completed_response()]);
    let mut provider_options = ProviderStreamOptions::default();
    provider_options.stream.request.api_key = Some("xai-test-token".to_owned());
    provider_options.stream.request.fetch = Some(fetch);
    provider_options.stream.request.headers = user_agent_headers(options.user_agent);
    provider_options.stream.session_id = options.session_id.map(str::to_owned);
    provider_options.stream.cache_retention = options.cache_retention;
    if let Some(effort) = options.reasoning_effort {
        provider_options
            .extra
            .insert("reasoningEffort".to_owned(), json!(effort));
    }

    let result = (xai_provider().stream)(model, &normalize_context(context), provider_options)
        .result()
        .await;
    assert_eq!(
        result.stop_reason,
        StopReason::Stop,
        "{:?}",
        result.error_message
    );
    let requests = captured.lock().expect("captured");
    requests.last().cloned().expect("captured request")
}

/// Vitest `toMatchObject`: objects match recursively by subset, arrays
/// element-wise with equal length, other values by equality.
fn assert_match_object(actual: &JsonValue, expected: &JsonValue) {
    assert!(
        matches_object(actual, expected),
        "expected {actual:#} to match {expected:#}"
    );
}

fn matches_object(actual: &JsonValue, expected: &JsonValue) -> bool {
    match (actual, expected) {
        (JsonValue::Object(actual), JsonValue::Object(expected)) => {
            expected.iter().all(|(key, value)| {
                actual
                    .get(key)
                    .is_some_and(|actual| matches_object(actual, value))
            })
        }
        (JsonValue::Array(actual), JsonValue::Array(expected)) => {
            actual.len() == expected.len()
                && actual
                    .iter()
                    .zip(expected)
                    .all(|(actual, expected)| matches_object(actual, expected))
        }
        _ => actual == expected,
    }
}

#[test]
fn excludes_retired_and_redundant_models_from_the_built_in_catalog() {
    for model_id in [
        "grok-3",
        "grok-3-fast",
        "grok-4.20-0309-non-reasoning",
        "grok-4.20-0309-reasoning",
        "grok-build-0.1",
        "grok-code-fast-1",
    ] {
        assert!(!XAI_MODELS.contains_key(model_id), "{model_id}");
    }
}

#[test]
fn routes_every_built_in_xai_model_through_responses() {
    for model in XAI_MODELS.values() {
        assert_eq!(model.api, "openai-responses", "{}", model.id);
    }
    let levels =
        |id: &str| serde_json::to_value(get_supported_thinking_levels(&xai(id))).expect("levels");
    assert_eq!(levels("grok-4.5"), json!(["low", "medium", "high"]));
    assert_eq!(
        levels("grok-4.6"),
        json!(["low", "medium", "high", "xhigh"])
    );
    assert_eq!(
        levels("grok-4.7"),
        json!(["low", "medium", "high", "xhigh"])
    );
    assert_eq!(levels("grok-4.3"), json!(["off", "low", "medium", "high"]));
}

#[test]
fn includes_grok_4_7_capabilities_and_long_context_pricing() {
    assert_match_object(
        &serde_json::to_value(xai("grok-4.7")).expect("model"),
        &json!({
            "api": "openai-responses",
            "reasoning": true,
            "input": ["text", "image"],
            "contextWindow": 500_000,
            "maxTokens": 500_000,
            "cost": {
                "input": 2,
                "output": 6,
                "cacheRead": 0.5,
                "cacheWrite": 0,
                "tiers": [{
                    "inputTokensAbove": 200_000,
                    "input": 4,
                    "output": 12,
                    "cacheRead": 1,
                    "cacheWrite": 0,
                }],
            },
        }),
    );
}

#[tokio::test]
async fn uses_responses_with_bearer_auth_and_xai_compatible_request_fields() {
    let context: Context = serde_json::from_value(json!({
        "systemPrompt": "You are a careful coding assistant.",
        "messages": [{ "role": "user", "content": "hello", "timestamp": 1 }],
    }))
    .expect("context");
    let captured = capture_request(
        &xai("grok-4.5"),
        context,
        ResponsesOptions {
            session_id: Some("pi-session-123"),
            cache_retention: Some(CacheRetention::Long),
            reasoning_effort: Some("medium"),
            ..ResponsesOptions::NONE
        },
    )
    .await;

    assert_eq!(captured.url, "https://api.x.ai/v1/responses");
    assert_eq!(
        captured.header("authorization").as_deref(),
        Some("Bearer xai-test-token")
    );
    assert_eq!(
        captured.header("user-agent").as_deref(),
        Some(get_pi_user_agent())
    );
    assert_eq!(
        captured.header("session_id").as_deref(),
        Some("pi-session-123")
    );
    assert_match_object(
        &captured.body,
        &json!({
            "model": "grok-4.5",
            "store": false,
            "stream": true,
            "prompt_cache_key": "pi-session-123",
            "reasoning": { "effort": "medium" },
            "include": ["reasoning.encrypted_content"],
        }),
    );
    assert!(captured.body.get("prompt_cache_retention").is_none());
    let input = captured.body["input"].as_array().expect("input");
    assert!(input.iter().any(|item| matches_object(
        item,
        &json!({ "role": "developer", "content": "You are a careful coding assistant." })
    )));
}

#[tokio::test]
async fn requests_encrypted_reasoning_without_an_effort_override() {
    let captured = capture_request(&xai("grok-4.5"), hello_context(), ResponsesOptions::NONE).await;

    assert_match_object(
        &captured.body,
        &json!({
            "model": "grok-4.5",
            "store": false,
            "include": ["reasoning.encrypted_content"],
        }),
    );
    assert!(captured.body.get("reasoning").is_none());
}

#[tokio::test]
async fn uses_responses_for_grok_4_7_with_xhigh_effort_and_encrypted_reasoning() {
    let context: Context = serde_json::from_value(json!({
        "systemPrompt": "You are a careful coding assistant.",
        "messages": [{ "role": "user", "content": "hello", "timestamp": 1 }],
    }))
    .expect("context");
    let captured = capture_request(
        &xai("grok-4.7"),
        context,
        ResponsesOptions {
            reasoning_effort: Some("xhigh"),
            ..ResponsesOptions::NONE
        },
    )
    .await;

    assert_eq!(captured.url, "https://api.x.ai/v1/responses");
    assert_match_object(
        &captured.body,
        &json!({
            "model": "grok-4.7",
            "store": false,
            "stream": true,
            "reasoning": { "effort": "xhigh" },
            "include": ["reasoning.encrypted_content"],
        }),
    );
}

#[tokio::test]
async fn uses_responses_for_grok_4_3() {
    let captured = capture_request(
        &xai("grok-4.3"),
        hello_context(),
        ResponsesOptions {
            reasoning_effort: Some("low"),
            ..ResponsesOptions::NONE
        },
    )
    .await;

    assert_eq!(captured.url, "https://api.x.ai/v1/responses");
    assert_match_object(
        &captured.body,
        &json!({
            "model": "grok-4.3",
            "store": false,
            "include": ["reasoning.encrypted_content"],
            "reasoning": { "effort": "low" },
        }),
    );
}

#[tokio::test]
async fn uses_pis_user_agent_by_default_for_responses_requests() {
    let (fetch, captured) = mock_fetch(vec![completed_response()]);
    let mut openai_model = xai("grok-4.5");
    openai_model.provider = "openai".to_owned();
    openai_model.base_url = "https://api.openai.com/v1".to_owned();
    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = Some("test-token".to_owned());
    options.stream.request.fetch = Some(fetch);

    let result =
        openai_responses::stream(&openai_model, &normalize_context(hello_context()), options)
            .result()
            .await;

    assert_eq!(
        result.stop_reason,
        StopReason::Stop,
        "{:?}",
        result.error_message
    );
    let user_agent = captured
        .lock()
        .expect("captured")
        .last()
        .and_then(|request| request.header("user-agent"));
    assert_eq!(user_agent.as_deref(), Some(get_pi_user_agent()));
}

#[tokio::test]
async fn lets_explicit_headers_override_the_default_responses_user_agent() {
    let captured = capture_request(
        &xai("grok-4.5"),
        hello_context(),
        ResponsesOptions {
            user_agent: Some("custom-agent"),
            ..ResponsesOptions::NONE
        },
    )
    .await;

    assert_eq!(
        captured.header("user-agent").as_deref(),
        Some("custom-agent")
    );
}

#[tokio::test]
async fn uses_pis_user_agent_by_default_for_completions_requests() {
    assert_eq!(
        capture_completions_user_agent(None).await.as_deref(),
        Some(get_pi_user_agent())
    );
}

#[tokio::test]
async fn lets_explicit_headers_override_the_default_completions_user_agent() {
    assert_eq!(
        capture_completions_user_agent(Some("custom-agent"))
            .await
            .as_deref(),
        Some("custom-agent")
    );
}
