//! Port of the `anthropic-messages` halves of `test/fireworks-models.test.ts`
//! (the catalog halves live in `fireworks_models.rs`): the native-effort and
//! toggle-only payload assertions and the "Anthropic-compatible session
//! affinity and tool compat" suite.
//!
//! The TS `onPayload` throws "payload captured" to stop before the request;
//! here it records the payload and the fetch mock answers instead. The TS
//! local HTTP server that captures the request (and answers an empty SSE
//! body) is the fetch mock.

mod anthropic_support;

use std::sync::{Arc, Mutex, PoisonError};

use anthropic_support::{
    context, minimal_sse, mock_fetch, requests, CapturedRequest, MockResponse,
};
use eukhe_pi_ai::api::anthropic_messages::{stream, stream_simple};
use eukhe_pi_ai::compat::get_model;
use eukhe_pi_ai::types::{OnPayload, ProviderStreamOptions, SimpleStreamOptions};
use eukhe_types::pi_ai::{CacheRetention, JsonValue, Model, ThinkingLevel};
use serde_json::{json, Value};

// --- Fireworks models (payload halves) ---

/// The `onPayload` params of one `streamSimple` call.
async fn simple_payload(model: &Model, reasoning: Option<&str>) -> Value {
    let captured: Arc<Mutex<Option<JsonValue>>> = Arc::default();
    let sink = Arc::clone(&captured);
    let on_payload: OnPayload<Model> = Arc::new(move |payload, _model| {
        *sink.lock().unwrap_or_else(PoisonError::into_inner) = Some(payload);
        Box::pin(async { Ok(None) })
    });
    let (fetch, _) = mock_fetch(minimal_sse());
    let mut options = SimpleStreamOptions::default();
    options.stream.request.api_key = Some("test-fireworks-key".into());
    options.stream.request.fetch = Some(fetch);
    options.stream.request.on_payload = Some(on_payload);
    options.reasoning = reasoning.map(|level| {
        serde_json::from_value::<ThinkingLevel>(json!(level)).expect("thinking level")
    });
    let context =
        context(&json!({ "messages": [{ "role": "user", "content": "test", "timestamp": 0 }] }));
    stream_simple(model, &context, &options).result().await;
    let payload = captured
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone();
    payload.expect("payload captured")
}

/// Regression for #9323: native effort must reach Messages without
/// budget-based fallback.
async fn sends_native_messages_effort_levels_for(model_id: &str, levels: &[&str]) {
    let model = get_model("fireworks", model_id).expect("fireworks model");
    for level in levels {
        let payload = simple_payload(&model, (*level != "off").then_some(*level)).await;
        let (thinking, output_config) = if *level == "off" {
            (json!({ "type": "disabled" }), None)
        } else {
            (
                json!({ "type": "adaptive", "display": "summarized" }),
                Some(json!({ "effort": level })),
            )
        };
        assert_eq!(payload["thinking"], thinking, "{model_id} {level}");
        assert_eq!(
            payload.get("output_config").cloned(),
            output_config,
            "{model_id} {level}"
        );
    }
}

#[tokio::test]
async fn sends_native_messages_effort_levels_for_deepseek_v4p1_flash() {
    sends_native_messages_effort_levels_for(
        "accounts/fireworks/models/deepseek-v4p1-flash",
        &["off", "low", "high", "max"],
    )
    .await;
}

#[tokio::test]
async fn sends_native_messages_effort_levels_for_qwen3p8_max() {
    sends_native_messages_effort_levels_for(
        "accounts/fireworks/models/qwen3p8-max",
        &["off", "low", "medium", "xhigh"],
    )
    .await;
}

#[tokio::test]
async fn sends_native_messages_effort_levels_for_qwen3p8_2p4t_a95b() {
    sends_native_messages_effort_levels_for(
        "accounts/fireworks/models/qwen3p8-2p4t-a95b",
        &["off", "low", "medium", "xhigh"],
    )
    .await;
}

#[tokio::test]
async fn keeps_toggle_only_messages_models_without_a_verified_fallback_on_budget_based_thinking() {
    let model = get_model(
        "fireworks",
        "accounts/fireworks/models/nemotron-3-ultra-nvfp4",
    )
    .expect("fireworks model");
    let payload = simple_payload(&model, Some("high")).await;

    assert_eq!(
        payload["thinking"],
        json!({ "type": "enabled", "budget_tokens": 16384, "display": "summarized" })
    );
    assert_eq!(payload.get("output_config"), None);
}

// --- Anthropic-compatible session affinity and tool compat ---

/// TS `FIREWORKS_ANTHROPIC_COMPAT`.
fn fireworks_anthropic_compat() -> Value {
    json!({
        "allowEmptySignature": true,
        "sendSessionAffinityHeaders": true,
        "supportsEagerToolInputStreaming": false,
        "supportsCacheControlOnTools": false,
        "supportsLongCacheRetention": false,
    })
}

fn create_fireworks_model() -> Model {
    serde_json::from_value(json!({
        "id": "accounts/fireworks/models/kimi-k2p6",
        "name": "Kimi K2.6",
        "api": "anthropic-messages",
        "provider": "fireworks",
        "baseUrl": "http://127.0.0.1:0",
        "reasoning": true,
        "input": ["text", "image"],
        "cost": { "input": 0.95, "output": 4, "cacheRead": 0.16, "cacheWrite": 0 },
        "contextWindow": 262_000,
        "maxTokens": 262_000,
        "compat": fireworks_anthropic_compat(),
    }))
    .expect("model")
}

fn create_anthropic_model_json() -> Value {
    json!({
        "id": "claude-opus-4-8",
        "name": "Claude Opus 4.8",
        "api": "anthropic-messages",
        "provider": "anthropic",
        "baseUrl": "http://127.0.0.1:0",
        "reasoning": true,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 200_000,
        "maxTokens": 32_000,
    })
}

fn create_anthropic_model() -> Model {
    serde_json::from_value(create_anthropic_model_json()).expect("model")
}

fn create_open_router_model_json() -> Value {
    let mut model = create_anthropic_model_json();
    model["id"] = json!("anthropic/claude-opus-4.8");
    model["provider"] = json!("openrouter");
    model["baseUrl"] = json!("https://openrouter.ai/api");
    model
}

fn create_open_router_model() -> Model {
    serde_json::from_value(create_open_router_model_json()).expect("model")
}

/// TS `createContext()` with the `lookup` tool.
fn create_context() -> Value {
    json!({
        "messages": [{ "role": "user", "content": "Use the tool", "timestamp": 1 }],
        "tools": [{
            "name": "lookup",
            "description": "Look up a value",
            "parameters": {
                "type": "object",
                "properties": { "value": { "type": "string" } },
                "required": ["value"],
            },
        }],
    })
}

/// TS `captureAnthropicRequest`.
async fn capture_anthropic_request(
    model: &Model,
    context_json: &Value,
    session_id: Option<&str>,
    cache_retention: Option<CacheRetention>,
) -> CapturedRequest {
    let (fetch, captured) = mock_fetch(MockResponse::sse(""));
    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = Some("test-key".into());
    options.stream.request.fetch = Some(fetch);
    options.stream.cache_retention = Some(cache_retention.unwrap_or(CacheRetention::Short));
    options.stream.session_id = session_id.map(str::to_owned);
    stream(model, &context(context_json), options)
        .result()
        .await;
    requests(&captured)
        .into_iter()
        .next()
        .expect("Anthropic request was not captured")
}

/// TS `getTools`.
fn get_tools(body: &Value) -> &Vec<Value> {
    body["tools"]
        .as_array()
        .expect("Expected tools in request body")
}

#[tokio::test]
async fn sends_x_session_affinity_header_for_fireworks_models() {
    let request = capture_anthropic_request(
        &create_fireworks_model(),
        &create_context(),
        Some("fireworks-session-1"),
        None,
    )
    .await;

    assert_eq!(
        request.header("x-session-affinity").as_deref(),
        Some("fireworks-session-1")
    );
}

#[tokio::test]
async fn omits_x_session_affinity_header_for_native_anthropic_models() {
    let request = capture_anthropic_request(
        &create_anthropic_model(),
        &create_context(),
        Some("anthropic-session-1"),
        None,
    )
    .await;

    assert_eq!(request.header("x-session-affinity"), None);
}

#[tokio::test]
async fn omits_x_session_affinity_header_when_cache_retention_is_none() {
    let request = capture_anthropic_request(
        &create_fireworks_model(),
        &create_context(),
        Some("fireworks-session-2"),
        Some(CacheRetention::None),
    )
    .await;

    assert_eq!(request.header("x-session-affinity"), None);
}

// Regression test for https://github.com/earendil-works/pi/issues/9102
#[tokio::test]
async fn sends_only_x_session_id_for_openrouter_models() {
    let request = capture_anthropic_request(
        &create_open_router_model(),
        &create_context(),
        Some("openrouter-session-1"),
        None,
    )
    .await;

    assert_eq!(
        request.header("x-session-id").as_deref(),
        Some("openrouter-session-1")
    );
    assert_eq!(request.header("x-session-affinity"), None);
}

#[tokio::test]
async fn omits_openrouter_session_headers_when_cache_retention_is_none() {
    let request = capture_anthropic_request(
        &create_open_router_model(),
        &create_context(),
        Some("openrouter-session-2"),
        Some(CacheRetention::None),
    )
    .await;

    assert_eq!(request.header("x-session-id"), None);
    assert_eq!(request.header("x-session-affinity"), None);
}

#[tokio::test]
async fn allows_openrouter_session_headers_to_be_disabled() {
    let mut model = create_open_router_model_json();
    model["compat"] = json!({ "sendSessionAffinityHeaders": false });
    let model: Model = serde_json::from_value(model).expect("model");
    let request = capture_anthropic_request(
        &model,
        &create_context(),
        Some("openrouter-session-3"),
        None,
    )
    .await;

    assert_eq!(request.header("x-session-id"), None);
}

#[tokio::test]
async fn omits_cache_control_on_tools_for_fireworks_models() {
    let request =
        capture_anthropic_request(&create_fireworks_model(), &create_context(), None, None).await;

    let tools = get_tools(&request.body);
    let last_tool = tools.last().expect("a tool");
    assert_eq!(last_tool.get("cache_control"), None);
}

#[tokio::test]
async fn omits_eager_input_streaming_on_tools_for_fireworks_models() {
    let request =
        capture_anthropic_request(&create_fireworks_model(), &create_context(), None, None).await;

    for tool in get_tools(&request.body) {
        assert_eq!(tool.get("eager_input_streaming"), None);
    }
}

#[tokio::test]
async fn sends_cache_control_on_tools_for_native_anthropic_models() {
    let request =
        capture_anthropic_request(&create_anthropic_model(), &create_context(), None, None).await;

    let tools = get_tools(&request.body);
    let last_tool = tools.last().expect("a tool");
    assert_eq!(last_tool["cache_control"]["type"], json!("ephemeral"));
}

#[tokio::test]
async fn sends_eager_input_streaming_on_tools_for_native_anthropic_models() {
    let request =
        capture_anthropic_request(&create_anthropic_model(), &create_context(), None, None).await;

    let tools = get_tools(&request.body);
    assert_eq!(tools[0]["eager_input_streaming"], json!(true));
}
