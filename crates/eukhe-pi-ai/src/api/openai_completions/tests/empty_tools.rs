//! Port of `openai-completions-empty-tools.test.ts`.
//!
//! Empty tools arrays must NOT be serialized as `tools: []`: some
//! `OpenAI`-compatible backends (e.g. `DashScope` / Aliyun Qwen via
//! compatible-mode) reject the request with `"[] is too short - 'tools'"`
//! (HTTP 400). The TS fake `OpenAI` client captured `params` and the client
//! constructor options; here the recorded HTTP request plays both roles
//! (body = `params`, url = `baseURL`, headers = `defaultHeaders`).

use serde_json::{json, Value as JsonValue};

use super::support::{context, model, sse_fetch, stop_chunks};
use crate::api::openai_completions::stream_simple;
use crate::api::system_one_shared::test_fetch::{recorded, Recorded};
use crate::providers::all::get_builtin_model;
use crate::types::{
    Context, Model, ProviderEnv, ProviderHeaders, ProviderRequestOptions, SimpleStreamOptions,
    StreamOptions, ThinkingLevel, TranscriptContext,
};

/// `{ ...getModel("openai", "gpt-4o-mini") minus compat, api: "openai-completions", ...overrides }`.
fn gpt_4o_mini_completions(overrides: &JsonValue) -> Model {
    let base = get_builtin_model("openai", "gpt-4o-mini").expect("openai/gpt-4o-mini in catalog");
    let mut value = serde_json::to_value(&base).expect("serialize model");
    let object = value.as_object_mut().expect("model JSON object");
    object.remove("compat");
    object.insert("api".to_owned(), json!("openai-completions"));
    for (key, value) in overrides.as_object().into_iter().flatten() {
        object.insert(key.clone(), value.clone());
    }
    model(value)
}

fn model_json(model: &Model) -> JsonValue {
    serde_json::to_value(model).expect("serialize model")
}

/// `streamSimple(model, context, { apiKey: "test", maxTokens? }).result()`;
/// returns the request body the SDK sent.
async fn simple_payload(
    model: &Model,
    context: &TranscriptContext,
    max_tokens: Option<u64>,
) -> JsonValue {
    let (fetch, requests) = sse_fetch(stop_chunks());
    let options = SimpleStreamOptions {
        stream: StreamOptions {
            request: ProviderRequestOptions {
                api_key: Some("test".to_owned()),
                fetch: Some(fetch),
                ..ProviderRequestOptions::default()
            },
            max_tokens,
            ..StreamOptions::default()
        },
        ..SimpleStreamOptions::default()
    };
    let message = stream_simple(model, context, options).result().await;
    recorded(&requests)
        .into_iter()
        .next()
        .unwrap_or_else(|| panic!("no request was sent: {:?}", message.error_message))
        .json()
}

fn hi_context() -> TranscriptContext {
    context(json!({ "messages": [{ "role": "user", "content": "hi", "timestamp": 1 }] }))
}

/// TS sets `process.env.CLOUDFLARE_*`; here the same values go through the
/// request `env` option.
fn cloudflare_env() -> ProviderEnv {
    ProviderEnv::from([
        ("CLOUDFLARE_API_KEY".to_owned(), "cf-token".to_owned()),
        ("CLOUDFLARE_ACCOUNT_ID".to_owned(), "account-id".to_owned()),
        ("CLOUDFLARE_GATEWAY_ID".to_owned(), "gateway-id".to_owned()),
    ])
}

fn cloudflare_model(id: &str) -> Model {
    get_builtin_model("cloudflare-ai-gateway", id)
        .unwrap_or_else(|| panic!("cloudflare-ai-gateway/{id} in catalog"))
}

/// The top-level `streamSimple` (provider auth resolution included) with
/// `options` plus the cloudflare env and a recording `fetch`.
async fn cloudflare_request(
    model: &Model,
    context: JsonValue,
    mut options: SimpleStreamOptions,
) -> Recorded {
    let (fetch, requests) = sse_fetch(stop_chunks());
    options.stream.request.fetch = Some(fetch);
    options.stream.request.env = Some(cloudflare_env());
    let context: Context = serde_json::from_value(context).expect("valid context JSON");
    let message = crate::compat::stream_simple(model, context, options)
        .expect("stream_simple")
        .result()
        .await;
    recorded(&requests)
        .into_iter()
        .next()
        .unwrap_or_else(|| panic!("no request was sent: {:?}", message.error_message))
}

const CLOUDFLARE_COMPAT_BASE_URL: &str =
    "https://gateway.ai.cloudflare.com/v1/account-id/gateway-id/compat";

#[tokio::test]
async fn omits_tools_field_when_context_tools_is_an_empty_array() {
    let model = gpt_4o_mini_completions(&json!({}));
    let params = simple_payload(
        &model,
        &context(json!({
            "messages": [{ "role": "user", "content": "hi", "timestamp": 1 }],
            "tools": [],
        })),
        None,
    )
    .await;

    assert!(params.get("tools").is_none(), "params: {params}");
}

#[tokio::test]
async fn omits_tools_field_when_context_tools_is_undefined() {
    let model = gpt_4o_mini_completions(&json!({}));
    let params = simple_payload(&model, &hi_context(), None).await;

    assert!(params.get("tools").is_none(), "params: {params}");
}

#[tokio::test]
async fn sends_default_max_tokens() {
    let model = gpt_4o_mini_completions(&json!({}));
    let params = simple_payload(&model, &hi_context(), None).await;

    assert_eq!(params.get("max_tokens"), None);
    assert_eq!(
        params.get("max_completion_tokens"),
        Some(&model_json(&model)["maxTokens"])
    );
}

#[tokio::test]
async fn sends_explicit_max_tokens() {
    let model = gpt_4o_mini_completions(&json!({}));
    let params = simple_payload(&model, &hi_context(), Some(1234)).await;

    assert_eq!(params.get("max_tokens"), None);
    assert_eq!(params.get("max_completion_tokens"), Some(&json!(1234)));
}

#[tokio::test]
async fn clamps_default_max_tokens_to_remaining_context() {
    let model = gpt_4o_mini_completions(&json!({ "contextWindow": 10000, "maxTokens": 8000 }));
    let ctx = context(json!({
        "messages": [{ "role": "user", "content": "x".repeat(8000), "timestamp": 1 }],
    }));
    let params = simple_payload(&model, &ctx, None).await;

    assert_eq!(params.get("max_tokens"), None);
    assert_eq!(params.get("max_completion_tokens"), Some(&json!(3618)));
}

#[tokio::test]
async fn clamps_explicit_max_tokens_to_remaining_context() {
    let model = gpt_4o_mini_completions(&json!({ "contextWindow": 10000, "maxTokens": 8000 }));
    let ctx = context(json!({
        "messages": [{ "role": "user", "content": "x".repeat(8000), "timestamp": 1 }],
    }));
    let params = simple_payload(&model, &ctx, Some(7000)).await;

    assert_eq!(params.get("max_tokens"), None);
    assert_eq!(params.get("max_completion_tokens"), Some(&json!(3618)));
}

/// eukhe addition: a custom model on a loopback OpenAI-compatible server
/// (`llama.cpp`, vLLM, `SGLang`) must not receive `store` — those servers reject
/// unknown fields with a 400 ("Unsupported chat request field: store").
#[tokio::test]
async fn loopback_custom_models_omit_the_store_field() {
    let model = gpt_4o_mini_completions(&json!({
        "provider": "elpis-fast",
        "baseUrl": "http://127.0.0.1:18020/v1",
    }));
    let params = simple_payload(&model, &hi_context(), None).await;
    assert_eq!(params.get("store"), None);

    let localhost = gpt_4o_mini_completions(&json!({
        "provider": "elpis-fast",
        "baseUrl": "http://localhost:18020/v1",
    }));
    let params = simple_payload(&localhost, &hi_context(), None).await;
    assert_eq!(params.get("store"), None);

    // A non-loopback custom endpoint keeps the detected default.
    let remote = gpt_4o_mini_completions(&json!({
        "provider": "elpis-fast",
        "baseUrl": "http://10.0.0.7:18020/v1",
    }));
    let params = simple_payload(&remote, &hi_context(), None).await;
    assert_eq!(params.get("store"), Some(&json!(false)));
}

#[tokio::test]
async fn uses_conservative_openai_compatible_fields_for_cloudflare_ai_gateway_compat_models() {
    let model = cloudflare_model("workers-ai/@cf/moonshotai/kimi-k2.6");
    let request = cloudflare_request(
        &model,
        json!({
            "systemPrompt": "You are helpful.",
            "messages": [{ "role": "user", "content": "hi", "timestamp": 1 }],
        }),
        SimpleStreamOptions {
            stream: StreamOptions {
                max_tokens: Some(1234),
                ..StreamOptions::default()
            },
            reasoning: Some(ThinkingLevel::High),
            ..SimpleStreamOptions::default()
        },
    )
    .await;

    let params = request.json();
    assert_eq!(params["messages"][0]["role"], json!("system"));
    assert_eq!(params.get("max_tokens"), Some(&json!(1234)));
    assert_eq!(params.get("max_completion_tokens"), None);
    assert_eq!(params.get("reasoning_effort"), None);
    assert_eq!(params.get("store"), None);

    assert_eq!(
        request.url,
        format!("{CLOUDFLARE_COMPAT_BASE_URL}/chat/completions")
    );
    // TS: `defaultHeaders.Authorization === null` suppresses the SDK header.
    assert_eq!(request.header("authorization"), None);
    assert_eq!(
        request.header("cf-aig-authorization"),
        Some("Bearer cf-token")
    );
}

#[tokio::test]
async fn resolves_cloudflare_ai_gateway_base_url_through_provider_auth() {
    let model = cloudflare_model("workers-ai/@cf/moonshotai/kimi-k2.6");
    let request = cloudflare_request(
        &model,
        json!({ "messages": [{ "role": "user", "content": "hi", "timestamp": 1 }] }),
        SimpleStreamOptions::default(),
    )
    .await;

    assert_eq!(
        request.url,
        format!("{CLOUDFLARE_COMPAT_BASE_URL}/chat/completions")
    );
}

#[tokio::test]
async fn preserves_inline_upstream_authorization_for_cloudflare_ai_gateway_byok_requests() {
    let model = cloudflare_model("gpt-5.1");
    let request = cloudflare_request(
        &model,
        json!({ "messages": [{ "role": "user", "content": "hi", "timestamp": 1 }] }),
        SimpleStreamOptions {
            stream: StreamOptions {
                request: ProviderRequestOptions {
                    headers: Some(ProviderHeaders::from([(
                        "Authorization".to_owned(),
                        Some("Bearer upstream-token".to_owned()),
                    )])),
                    ..ProviderRequestOptions::default()
                },
                ..StreamOptions::default()
            },
            ..SimpleStreamOptions::default()
        },
    )
    .await;

    assert_eq!(
        request.header("authorization"),
        Some("Bearer upstream-token")
    );
    assert_eq!(
        request.header("cf-aig-authorization"),
        Some("Bearer cf-token")
    );
}

#[tokio::test]
async fn sends_session_affinity_headers_for_workers_ai_through_cloudflare_ai_gateway() {
    let model = cloudflare_model("workers-ai/@cf/moonshotai/kimi-k2.6");
    let request = cloudflare_request(
        &model,
        json!({ "messages": [{ "role": "user", "content": "hi", "timestamp": 1 }] }),
        SimpleStreamOptions {
            stream: StreamOptions {
                session_id: Some("session-1".to_owned()),
                ..StreamOptions::default()
            },
            ..SimpleStreamOptions::default()
        },
    )
    .await;

    assert_eq!(request.header("session_id"), Some("session-1"));
    assert_eq!(request.header("x-client-request-id"), Some("session-1"));
    assert_eq!(request.header("x-session-affinity"), Some("session-1"));
}

#[tokio::test]
async fn still_emits_tools_for_anthropic_litellm_proxy_when_conversation_has_tool_history() {
    let model = gpt_4o_mini_completions(&json!({}));
    let ctx = context(json!({
        "messages": [
            { "role": "user", "content": "use the tool", "timestamp": 1 },
            {
                "role": "assistant",
                "content": [{ "type": "toolCall", "id": "t1", "name": "noop", "arguments": {} }],
                "stopReason": "toolUse",
                "usage": {
                    "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
                    "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
                },
                "api": "openai-completions",
                "provider": "openai",
                "model": "gpt-4o-mini",
                "timestamp": 2,
            },
            {
                "role": "toolResult",
                "toolCallId": "t1",
                "toolName": "noop",
                "content": [{ "type": "text", "text": "done" }],
                "isError": false,
                "timestamp": 3,
            },
        ],
        "tools": [],
    }));
    let params = simple_payload(&model, &ctx, None).await;

    assert_eq!(params.get("tools"), Some(&json!([])));
}
