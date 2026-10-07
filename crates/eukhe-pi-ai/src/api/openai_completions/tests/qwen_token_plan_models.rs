//! Payload cases of `qwen-token-plan-models.test.ts` (the catalog assertions
//! live in the model-catalog port). The TS `vi.mock("openai")` fake that
//! answers with one stop chunk is the `fetch` option here.

use std::sync::PoisonError;

use serde_json::json;

use super::support::{payload_recorder, sse_fetch};
use crate::compat::{get_models, stream_simple};
use crate::types::{
    Context, JsonValue, Model, ProviderRequestOptions, SimpleStreamOptions, StreamOptions,
    ThinkingLevel,
};

const QWEN_THINKING_MODELS: [&str; 15] = [
    "deepseek-v3.2",
    "deepseek-v4-flash",
    "deepseek-v4-pro",
    "glm-5",
    "glm-5.1",
    "glm-5.2",
    "kimi-k2.5",
    "kimi-k2.6",
    "kimi-k2.7-code",
    "qwen3.6-flash",
    "qwen3.6-plus",
    "qwen3.7-max",
    "qwen3.7-plus",
    "qwen3.8-flash",
    "qwen3.8-max",
];

const INDIVIDUAL_TEXT_MODELS: [&str; 9] = [
    "deepseek-v4-flash-0731",
    "deepseek-v4-pro",
    "deepseek-v4-pro-0813",
    "glm-5.2",
    "qwen3.6-flash",
    "qwen3.7-max",
    "qwen3.7-plus",
    "qwen3.8-flash",
    "qwen3.8-max",
];

const QWEN_REASONING_EFFORT_MODELS: [&str; 5] = [
    "deepseek-v4-flash",
    "deepseek-v4-pro",
    "glm-5",
    "glm-5.1",
    "glm-5.2",
];

const QWEN38_MODELS: [&str; 2] = ["qwen3.8-flash", "qwen3.8-max"];

const SHARED_PROVIDERS: [&str; 2] = ["qwen-token-plan", "qwen-token-plan-cn"];
const ALL_PROVIDERS: [&str; 3] = [
    "qwen-token-plan",
    "qwen-token-plan-cn",
    "qwen-token-plan-individual",
];

fn cross(providers: &[&'static str], models: &[&'static str]) -> Vec<(&'static str, &'static str)> {
    providers
        .iter()
        .flat_map(|&provider| models.iter().map(move |&model_id| (provider, model_id)))
        .collect()
}

fn qwen_thinking_model_cases() -> Vec<(&'static str, &'static str)> {
    let mut cases = cross(&SHARED_PROVIDERS, &QWEN_THINKING_MODELS);
    cases.extend(cross(
        &["qwen-token-plan-individual"],
        &INDIVIDUAL_TEXT_MODELS,
    ));
    cases
}

fn qwen_reasoning_effort_model_cases() -> Vec<(&'static str, &'static str)> {
    let mut cases = cross(&SHARED_PROVIDERS, &QWEN_REASONING_EFFORT_MODELS);
    cases.extend(cross(
        &["qwen-token-plan-individual"],
        &[
            "deepseek-v4-flash-0731",
            "deepseek-v4-pro",
            "deepseek-v4-pro-0813",
            "glm-5.2",
        ],
    ));
    cases
}

fn qwen38_model_cases() -> Vec<(&'static str, &'static str)> {
    cross(&ALL_PROVIDERS, &QWEN38_MODELS)
}

fn find_model(provider: &str, model_id: &str) -> Model {
    get_models(provider)
        .into_iter()
        .find(|candidate| candidate.id == model_id)
        .unwrap_or_else(|| panic!("Missing model: {provider}/{model_id}"))
}

/// The TS fake's single chunk: `finish_reason: "stop"` with usage.
fn fake_chunks() -> Vec<JsonValue> {
    vec![json!({
        "choices": [{ "delta": {}, "finish_reason": "stop" }],
        "usage": {
            "prompt_tokens": 1,
            "completion_tokens": 1,
            "prompt_tokens_details": { "cached_tokens": 0 },
            "completion_tokens_details": { "reasoning_tokens": 0 },
        },
    })]
}

/// `streamSimple(model, { messages: [user "Hi"] }, { apiKey: "test",
/// reasoning, onPayload })`; returns the payload.
async fn simple_payload(model: &Model, reasoning: ThinkingLevel) -> JsonValue {
    let (fetch, _requests) = sse_fetch(fake_chunks());
    let (hook, seen) = payload_recorder();
    let options = SimpleStreamOptions {
        stream: StreamOptions {
            request: ProviderRequestOptions {
                api_key: Some("test".to_owned()),
                fetch: Some(fetch),
                on_payload: Some(hook),
                ..ProviderRequestOptions::default()
            },
            ..StreamOptions::default()
        },
        reasoning: Some(reasoning),
        ..SimpleStreamOptions::default()
    };
    let context: Context = serde_json::from_value(json!({
        "messages": [{ "role": "user", "content": "Hi", "timestamp": 1 }],
    }))
    .expect("valid context JSON");
    let message = stream_simple(model, context, options)
        .expect("stream starts")
        .result()
        .await;
    let payloads = seen.lock().unwrap_or_else(PoisonError::into_inner);
    payloads
        .first()
        .cloned()
        .unwrap_or_else(|| panic!("no payload captured: {:?}", message.error_message))
}

#[tokio::test]
async fn sends_qwen_thinking_fields() {
    for (provider, model_id) in qwen_thinking_model_cases() {
        let payload = simple_payload(&find_model(provider, model_id), ThinkingLevel::High).await;

        assert_eq!(
            payload.get("enable_thinking"),
            Some(&json!(true)),
            "{provider}/{model_id}"
        );
        assert_eq!(payload.get("thinking"), None, "{provider}/{model_id}");
    }
}

#[tokio::test]
async fn sends_qwen_reasoning_effort() {
    for (provider, model_id) in qwen_reasoning_effort_model_cases() {
        let payload = simple_payload(&find_model(provider, model_id), ThinkingLevel::High).await;

        assert_eq!(
            payload.get("reasoning_effort"),
            Some(&json!("high")),
            "{provider}/{model_id}"
        );
    }
}

#[tokio::test]
async fn sends_qwen3_8_xhigh_reasoning_effort() {
    for (provider, model_id) in qwen38_model_cases() {
        let payload = simple_payload(&find_model(provider, model_id), ThinkingLevel::Xhigh).await;

        assert_eq!(
            payload.get("enable_thinking"),
            Some(&json!(true)),
            "{provider}/{model_id}"
        );
        assert_eq!(
            payload.get("reasoning_effort"),
            Some(&json!("xhigh")),
            "{provider}/{model_id}"
        );
        assert_eq!(payload.get("thinking"), None, "{provider}/{model_id}");
    }
}
