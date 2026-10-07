//! Port of `azure-openai-completions.test.ts`: the `azure` provider routes
//! its `openai-completions` catalog models through this module (wrapped by
//! `providers::azure` for endpoint and deployment resolution).
//!
//! TS sets `process.env` in `beforeEach`; here the same values go through
//! the scoped `env` request option (which takes precedence over the process
//! environment). The fake SDK's captured `params` / constructor `baseURL`
//! become the recorded HTTP request body / URL.

use std::sync::{Arc, Mutex, PoisonError};

use serde_json::json;

use super::support::{collect, context, sse_fetch};
use crate::api::system_one_shared::test_fetch::{recorded, Recorded, Requests};
use crate::models::Provider;
use crate::providers::azure::azure_provider;
use crate::providers::azure_models::AZURE_MODELS;
use crate::types::{
    AssistantMessage, JsonValue, Model, OnPayload, ProviderEnv, ProviderRequestOptions,
    ProviderStreamOptions, SimpleStreamOptions, StreamOptions, ThinkingLevel, TranscriptContext,
};

const AZURE_BASE_URL: &str = "https://my-resource.services.ai.azure.com";

fn azure_model(id: &str) -> Model {
    AZURE_MODELS
        .get(id)
        .unwrap_or_else(|| panic!("{id} in the azure catalog"))
        .clone()
}

fn deep_seek_model() -> Model {
    azure_model("deepseek-v4-pro")
}

fn sys_context() -> TranscriptContext {
    context(json!({
        "systemPrompt": "sys",
        "messages": [{ "role": "user", "content": "hi", "timestamp": 1 }],
    }))
}

/// The `beforeEach` environment (`AZURE_OPENAI_BASE_URL` set) plus `extra`.
fn azure_env(extra: &[(&str, &str)]) -> ProviderEnv {
    let mut env = ProviderEnv::new();
    env.insert(
        "AZURE_OPENAI_BASE_URL".to_owned(),
        AZURE_BASE_URL.to_owned(),
    );
    for (name, value) in extra {
        env.insert((*name).to_owned(), (*value).to_owned());
    }
    env
}

fn request_options(env: ProviderEnv) -> (ProviderRequestOptions, Requests) {
    let (fetch, requests) = sse_fetch(vec![json!({
        "choices": [{ "delta": {}, "finish_reason": "stop" }],
        "usage": {
            "prompt_tokens": 1,
            "completion_tokens": 1,
            "prompt_tokens_details": { "cached_tokens": 0 },
        },
    })]);
    let request = ProviderRequestOptions {
        api_key: Some("test-key".to_owned()),
        fetch: Some(fetch),
        env: Some(env),
        ..ProviderRequestOptions::default()
    };
    (request, requests)
}

/// `azure.stream(model, context, options).result()`: the last request sent
/// (if any) and the final message.
async fn azure_stream(
    provider: &Provider,
    model: &Model,
    context: &TranscriptContext,
    env: ProviderEnv,
    configure: impl FnOnce(&mut ProviderStreamOptions),
) -> (Option<Recorded>, AssistantMessage) {
    let (request, requests) = request_options(env);
    let mut options = ProviderStreamOptions {
        stream: StreamOptions {
            request,
            ..StreamOptions::default()
        },
        ..ProviderStreamOptions::default()
    };
    configure(&mut options);
    let (_, message) = collect((provider.stream)(model, context, options)).await;
    (recorded(&requests).pop(), message)
}

/// `azure.streamSimple(model, context, options).result()`.
async fn azure_stream_simple(
    provider: &Provider,
    model: &Model,
    env: ProviderEnv,
    reasoning: Option<ThinkingLevel>,
) -> (Option<Recorded>, AssistantMessage) {
    let (request, requests) = request_options(env);
    let options = SimpleStreamOptions {
        stream: StreamOptions {
            request,
            ..StreamOptions::default()
        },
        reasoning,
        ..SimpleStreamOptions::default()
    };
    let (_, message) = collect((provider.stream_simple)(model, &sys_context(), options)).await;
    (recorded(&requests).pop(), message)
}

fn params(request: Option<Recorded>) -> JsonValue {
    request.expect("a request was sent").json()
}

// Regression for #9645: Azure Foundry rejects DeepSeek's thinking field and every prompt cache parameter here.

#[tokio::test]
async fn turns_thinking_on_with_reasoning_effort_instead_of_deepseeks_thinking_field() {
    let azure = azure_provider();
    let (request, _) = azure_stream_simple(
        &azure,
        &deep_seek_model(),
        azure_env(&[]),
        Some(ThinkingLevel::High),
    )
    .await;
    let params = params(request);

    assert_eq!(params.get("reasoning_effort"), Some(&json!("high")));
    assert_eq!(params.get("thinking"), None);
}

#[tokio::test]
async fn clamps_thinking_levels_the_deployment_does_not_accept() {
    let azure = azure_provider();
    let (request, _) = azure_stream_simple(
        &azure,
        &deep_seek_model(),
        azure_env(&[]),
        Some(ThinkingLevel::Max),
    )
    .await;

    assert_eq!(
        params(request).get("reasoning_effort"),
        Some(&json!("high"))
    );
}

#[tokio::test]
async fn sends_no_reasoning_effort_when_no_thinking_level_is_requested() {
    let azure = azure_provider();
    let (request, _) = azure_stream_simple(&azure, &deep_seek_model(), azure_env(&[]), None).await;
    let params = params(request);

    assert_eq!(params.get("reasoning_effort"), None);
    assert_eq!(params.get("thinking"), None);
}

#[tokio::test]
async fn omits_prompt_cache_parameters_when_long_retention_comes_from_pi_cache_retention() {
    let azure = azure_provider();
    let (request, _) = azure_stream(
        &azure,
        &deep_seek_model(),
        &sys_context(),
        azure_env(&[("PI_CACHE_RETENTION", "long")]),
        |options| options.stream.session_id = Some("session-env".to_owned()),
    )
    .await;
    let params = params(request);

    assert_eq!(params.get("prompt_cache_key"), None);
    assert_eq!(params.get("prompt_cache_retention"), None);
}

// The deployment discards a `developer` system message once reasoning_effort is set, without
// billing it, so the system prompt has to go out under the system role.
#[tokio::test]
async fn sends_the_system_prompt_under_the_system_role() {
    let azure = azure_provider();
    let (request, _) = azure_stream(
        &azure,
        &deep_seek_model(),
        &sys_context(),
        azure_env(&[]),
        |options| {
            options
                .extra
                .insert("reasoningEffort".to_owned(), json!("low"));
        },
    )
    .await;
    let params = params(request);

    // `toMatchObject({ role: "system", content: "sys" })`.
    assert_eq!(params["messages"][0]["role"], json!("system"));
    assert_eq!(params["messages"][0]["content"], json!("sys"));
}

// The deployment honours system messages sent mid-conversation, so pi must not collapse them.
#[tokio::test]
async fn keeps_mid_conversation_system_messages_in_place() {
    let azure = azure_provider();
    let resumed = context(json!({
        "systemPrompt": "first",
        "messages": [
            { "role": "user", "content": "hi", "timestamp": 1 },
            { "role": "system", "content": "second", "timestamp": 1 },
            { "role": "user", "content": "again", "timestamp": 1 },
        ],
    }));
    let (request, _) =
        azure_stream(&azure, &deep_seek_model(), &resumed, azure_env(&[]), |_| {}).await;
    let params = params(request);

    let roles: Vec<&JsonValue> = params["messages"]
        .as_array()
        .expect("messages array")
        .iter()
        .map(|message| &message["role"])
        .collect();
    assert_eq!(
        roles,
        vec![
            &json!("system"),
            &json!("user"),
            &json!("system"),
            &json!("user"),
        ]
    );
}

#[tokio::test]
async fn omits_prompt_cache_parameters_even_when_long_retention_is_requested() {
    let azure = azure_provider();
    let (request, _) = azure_stream(
        &azure,
        &deep_seek_model(),
        &sys_context(),
        azure_env(&[]),
        |options| {
            options.stream.cache_retention = Some(crate::types::CacheRetention::Long);
            options.stream.session_id = Some("session-1".to_owned());
        },
    )
    .await;
    let params = params(request);

    assert_eq!(params.get("prompt_cache_key"), None);
    assert_eq!(params.get("prompt_cache_retention"), None);
}

#[tokio::test]
async fn replays_reasoning_content_on_assistant_turns_so_the_cached_prefix_is_unchanged() {
    let azure = azure_provider();
    let resumed = context(json!({
        "systemPrompt": "sys",
        "messages": [
            { "role": "user", "content": "first", "timestamp": 1 },
            {
                "role": "assistant",
                "content": [
                    { "type": "thinking", "thinking": "internal reasoning", "thinkingSignature": "reasoning_content" },
                    { "type": "text", "text": "answer" },
                ],
                "provider": "azure",
                "api": "openai-completions",
                "model": "deepseek-v4-pro",
                "timestamp": 1,
                "usage": {
                    "input": 0,
                    "output": 0,
                    "cacheRead": 0,
                    "cacheWrite": 0,
                    "totalTokens": 0,
                    "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
                },
                "stopReason": "stop",
            },
            { "role": "user", "content": "second", "timestamp": 1 },
        ],
    }));
    let (request, _) =
        azure_stream(&azure, &deep_seek_model(), &resumed, azure_env(&[]), |_| {}).await;
    let params = params(request);

    let assistant = params["messages"]
        .as_array()
        .expect("messages array")
        .iter()
        .find(|message| message["role"] == json!("assistant"))
        .expect("an assistant message");
    assert_eq!(assistant["reasoning_content"], json!("internal reasoning"));
}

// azure Chat Completions endpoint resolution

#[tokio::test]
async fn normalizes_the_azure_endpoint_the_completions_client_is_built_with() {
    let azure = azure_provider();
    let (request, _) = azure_stream(
        &azure,
        &deep_seek_model(),
        &sys_context(),
        azure_env(&[]),
        |_| {},
    )
    .await;

    assert_eq!(
        request.expect("a request was sent").url,
        format!("{AZURE_BASE_URL}/openai/v1/chat/completions")
    );
}

/// Requires `AZURE_OPENAI_BASE_URL` and `AZURE_OPENAI_RESOURCE_NAME` unset in
/// the process environment (TS deletes the former in the test).
#[tokio::test]
async fn surfaces_an_unconfigured_endpoint_as_an_error_event_rather_than_throwing_out_of_stream() {
    let azure = azure_provider();
    let (_, result) = azure_stream(
        &azure,
        &deep_seek_model(),
        &sys_context(),
        ProviderEnv::new(),
        |_| {},
    )
    .await;

    assert_eq!(result.stop_reason, crate::types::StopReason::Error);
    let error_message = result.error_message.unwrap_or_default();
    assert!(
        error_message.contains("Azure OpenAI base URL is required"),
        "{error_message}"
    );
}

// The id is persisted on the assistant message and read back by name, so it has to stay a catalog id.
#[tokio::test]
async fn sends_the_model_id_as_the_request_model() {
    let azure = azure_provider();
    let (request, result) = azure_stream(
        &azure,
        &deep_seek_model(),
        &sys_context(),
        azure_env(&[]),
        |_| {},
    )
    .await;

    assert_eq!(
        params(request).get("model"),
        Some(&json!("deepseek-v4-pro"))
    );
    assert_eq!(result.model, "deepseek-v4-pro");
}

#[tokio::test]
async fn sends_the_mapped_deployment_name_while_keeping_the_catalog_id_on_the_message() {
    let azure = azure_provider();
    let (request, result) = azure_stream_simple(
        &azure,
        &deep_seek_model(),
        azure_env(&[(
            "AZURE_OPENAI_DEPLOYMENT_NAME_MAP",
            "deepseek-v4-pro=my-deepseek",
        )]),
        None,
    )
    .await;

    assert_eq!(params(request).get("model"), Some(&json!("my-deepseek")));
    assert_eq!(result.model, "deepseek-v4-pro");
}

#[tokio::test]
async fn passes_the_deployment_name_through_a_callers_on_payload() {
    let azure = azure_provider();
    let seen_model: Arc<Mutex<Option<JsonValue>>> = Arc::default();
    let sink = Arc::clone(&seen_model);
    let on_payload: OnPayload<Model> = Arc::new(move |payload: JsonValue, _model: &Model| {
        *sink.lock().unwrap_or_else(PoisonError::into_inner) = payload.get("model").cloned();
        let mut replaced = payload.as_object().cloned().unwrap_or_default();
        replaced.insert("temperature".to_owned(), json!(0.1));
        Box::pin(async move { Ok(Some(JsonValue::Object(replaced))) })
    });
    let (request, _) = azure_stream(
        &azure,
        &deep_seek_model(),
        &sys_context(),
        azure_env(&[(
            "AZURE_OPENAI_DEPLOYMENT_NAME_MAP",
            "deepseek-v4-pro=my-deepseek",
        )]),
        |options| options.stream.request.on_payload = Some(on_payload),
    )
    .await;
    let params = params(request);

    assert_eq!(
        *seen_model.lock().unwrap_or_else(PoisonError::into_inner),
        Some(json!("my-deepseek"))
    );
    // `toMatchObject({ model: "my-deepseek", temperature: 0.1 })`.
    assert_eq!(params.get("model"), Some(&json!("my-deepseek")));
    assert_eq!(params.get("temperature"), Some(&json!(0.1)));
}

// azure api map

#[tokio::test]
async fn still_routes_responses_models_to_the_responses_api() {
    let azure = azure_provider();
    let (request, _) = azure_stream(
        &azure,
        &azure_model("gpt-4o-mini"),
        &sys_context(),
        azure_env(&[]),
        |_| {},
    )
    .await;

    let url = url::Url::parse(&request.expect("a request was sent").url).expect("request URL");
    assert!(url.path().ends_with("/responses"), "{url}");
}

#[tokio::test]
async fn routes_openai_completions_models_to_chat_completions() {
    let azure = azure_provider();
    let (request, _) = azure_stream(
        &azure,
        &deep_seek_model(),
        &sys_context(),
        azure_env(&[]),
        |_| {},
    )
    .await;

    let url = url::Url::parse(&request.expect("a request was sent").url).expect("request URL");
    assert!(url.path().ends_with("/chat/completions"), "{url}");
}
