//! Port of `test/openai-responses-compat.test.ts`.

mod openai_responses_support;

use eukhe_pi_ai::api::openai_responses::stream as stream_openai_responses;
use eukhe_pi_ai::compat::get_model;
use eukhe_pi_ai::types::ProviderStreamOptions;
use eukhe_pi_ai::utils::transcript::normalize_context;
use eukhe_types::pi_ai::{
    AssistantMessage, CacheRetention, Context, JsonValue, Model, ProviderHeaders, TranscriptContext,
};
use openai_responses_support::{mock_fetch, CapturedRequest, MockResponse};
use serde_json::json;

fn model(provider: &str, id: &str) -> Model {
    get_model(provider, id).expect("model")
}

/// `{ ...base, ...patch }` on the model's JSON shape.
fn with_fields(base: &Model, patch: &JsonValue) -> Model {
    let mut value = serde_json::to_value(base).expect("model json");
    let object = value.as_object_mut().expect("model object");
    for (key, field) in patch.as_object().expect("patch object") {
        object.insert(key.clone(), field.clone());
    }
    serde_json::from_value(value).expect("patched model")
}

fn compat_field(model: &Model, key: &str) -> JsonValue {
    serde_json::to_value(model).expect("model json")["compat"][key].clone()
}

fn context(value: JsonValue) -> TranscriptContext {
    normalize_context(serde_json::from_value::<Context>(value).expect("context"))
}

fn sys_hi_context() -> TranscriptContext {
    context(json!({
        "systemPrompt": "sys",
        "messages": [{ "role": "user", "content": "hi", "timestamp": 0 }],
    }))
}

fn done_response() -> MockResponse {
    MockResponse::sse("data: [DONE]\n\n")
}

/// Streams `model` with `options` (api key and fetch filled in) against
/// `response`; returns the single captured request and the final message.
async fn run(
    model: &Model,
    context: &TranscriptContext,
    mut options: ProviderStreamOptions,
    response: MockResponse,
) -> (CapturedRequest, AssistantMessage) {
    let (fetch, captured) = mock_fetch(vec![response]);
    options.stream.request.api_key = Some("sk-test-key".to_owned());
    options.stream.request.fetch = Some(fetch);
    let result = stream_openai_responses(model, context, options)
        .result()
        .await;
    let request = captured
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .first()
        .cloned()
        .expect("captured request");
    (request, result)
}

#[allow(clippy::struct_field_names)] // Field names mirror the TS `captured` object.
struct CapturedHeaders {
    session_id: Option<String>,
    client_request_id: Option<String>,
    x_session_id: Option<String>,
}

async fn capture_openai_response_headers(
    options: ProviderStreamOptions,
    model: &Model,
) -> (CapturedHeaders, JsonValue) {
    let (request, _) = run(
        model,
        &context(json!({ "messages": [{ "role": "user", "content": "hi", "timestamp": 0 }] })),
        options,
        done_response(),
    )
    .await;
    let headers = CapturedHeaders {
        session_id: request.header("session_id"),
        client_request_id: request.header("x-client-request-id"),
        x_session_id: request.header("x-session-id"),
    };
    (headers, request.body)
}

fn session_options(session_id: &str) -> ProviderStreamOptions {
    let mut options = ProviderStreamOptions::default();
    options.stream.session_id = Some(session_id.to_owned());
    options
}

fn extra_options(extra: &JsonValue) -> ProviderStreamOptions {
    ProviderStreamOptions {
        extra: extra.as_object().cloned().expect("extra object"),
        ..ProviderStreamOptions::default()
    }
}

fn gpt_5_4() -> Model {
    model("openai", "gpt-5.4")
}

// openai-responses provider defaults

#[tokio::test]
async fn omits_reasoning_when_no_reasoning_is_requested() {
    let model = model("github-copilot", "gpt-5-mini");
    let (request, _) = run(
        &model,
        &sys_hi_context(),
        ProviderStreamOptions::default(),
        done_response(),
    )
    .await;

    assert!(!request.body.is_null());
    assert!(request.body.get("reasoning").is_none_or(JsonValue::is_null));
}

#[tokio::test]
async fn forwards_required_tool_choice() {
    let context = context(json!({
        "messages": [{
            "role": "user",
            "content": "Do not call ping. Respond with text instead.",
            "timestamp": 0,
        }],
        "tools": [{
            "name": "ping",
            "description": "Ping",
            "parameters": {
                "type": "object",
                "properties": { "value": { "type": "string" } },
                "required": ["value"],
            },
        }],
    }));
    let (request, _) = run(
        &gpt_5_4(),
        &context,
        extra_options(&json!({ "toolChoice": "required" })),
        done_response(),
    )
    .await;

    assert_eq!(request.body["tool_choice"], json!("required"));
    let tools = request.body["tools"].as_array().expect("tools");
    assert_eq!(tools.len(), 1);
    assert_eq!(tools[0]["name"], json!("ping"));
}

#[tokio::test]
async fn sets_strict_mode_explicitly_for_cloudflare_openai_responses_tools() {
    let model = model("cloudflare-ai-gateway", "gpt-5.6-sol");
    let context = context(json!({
        "messages": [{ "role": "user", "content": "Use a tool.", "timestamp": 0 }],
        "tools": [
            {
                "name": "ordinary",
                "description": "An ordinary tool",
                "parameters": {
                    "type": "object",
                    "properties": {
                        "path": { "type": "string" },
                        "offset": { "type": "number" },
                    },
                    "required": ["path"],
                },
            },
            {
                "name": "constrained",
                "description": "A constrained tool",
                "parameters": {
                    "type": "object",
                    "properties": { "value": { "type": "string" } },
                    "required": ["value"],
                },
                "constrainedSampling": { "type": "json_schema", "strict": "prefer" },
            },
        ],
    }));
    let (request, _) = run(
        &model,
        &context,
        ProviderStreamOptions::default(),
        done_response(),
    )
    .await;

    assert_eq!(compat_field(&model, "supportsStrictMode"), json!(true));
    let tools = request.body["tools"].as_array().expect("tools");
    assert_eq!(tools.len(), 2);
    assert_eq!(
        (&tools[0]["name"], &tools[0]["strict"]),
        (&json!("ordinary"), &json!(false))
    );
    assert_eq!(
        (&tools[1]["name"], &tools[1]["strict"]),
        (&json!("constrained"), &json!(true))
    );
}

#[tokio::test]
async fn sends_none_reasoning_effort_for_openai_when_no_reasoning_is_requested() {
    for model_id in [
        "gpt-5.1",
        "gpt-5.2",
        "gpt-5.3-codex",
        "gpt-5.4",
        "gpt-5.4-mini",
        "gpt-5.4-nano",
        "gpt-5.5",
        "gpt-5.6-sol",
        "gpt-5.6-terra",
        "gpt-5.6-luna",
        "gpt-6-sol",
        "gpt-6-luna",
    ] {
        let model = model("openai", model_id);
        let (request, _) = run(
            &model,
            &sys_hi_context(),
            ProviderStreamOptions::default(),
            done_response(),
        )
        .await;

        assert_eq!(
            request.body["reasoning"]["effort"],
            json!("none"),
            "{model_id}"
        );
    }
}

#[tokio::test]
async fn omits_reasoning_effort_for_openai_when_off_is_unsupported() {
    for model_id in [
        "gpt-5",
        "gpt-5-mini",
        "gpt-5-nano",
        "gpt-5-pro",
        "gpt-5.2-pro",
        "gpt-5.4-pro",
        "gpt-5.5-pro",
    ] {
        let model = model("openai", model_id);
        let (request, _) = run(
            &model,
            &sys_hi_context(),
            ProviderStreamOptions::default(),
            done_response(),
        )
        .await;

        assert!(
            request.body.get("reasoning").is_none_or(JsonValue::is_null),
            "{model_id}"
        );
    }
}

#[tokio::test]
async fn sets_cache_affinity_headers_for_official_openai_responses_requests_with_a_session_id() {
    let (captured, _) =
        capture_openai_response_headers(session_options("session-123"), &gpt_5_4()).await;

    assert_eq!(captured.session_id.as_deref(), Some("session-123"));
    assert_eq!(captured.client_request_id.as_deref(), Some("session-123"));
}

#[tokio::test]
async fn clamps_prompt_cache_key_to_openais_64_character_limit() {
    let session_id = "x".repeat(67);
    let (request, _) = run(
        &gpt_5_4(),
        &sys_hi_context(),
        session_options(&session_id),
        done_response(),
    )
    .await;

    assert_eq!(request.body["prompt_cache_key"], json!("x".repeat(64)));
}

#[tokio::test]
async fn sets_cache_affinity_headers_for_proxy_openai_responses_requests_with_a_session_id() {
    let proxy_model = with_fields(
        &gpt_5_4(),
        &json!({ "provider": "opencode", "baseUrl": "https://proxy.example.com/v1" }),
    );
    let (captured, _) =
        capture_openai_response_headers(session_options("session-123"), &proxy_model).await;

    assert_eq!(captured.session_id.as_deref(), Some("session-123"));
    assert_eq!(captured.client_request_id.as_deref(), Some("session-123"));
}

#[tokio::test]
async fn uses_openrouter_session_affinity_header_when_configured() {
    let proxy_model = with_fields(
        &gpt_5_4(),
        &json!({
            "provider": "proxy",
            "baseUrl": "https://proxy.example.com/v1",
            "compat": { "sessionAffinityFormat": "openrouter" },
        }),
    );
    let (captured, payload) =
        capture_openai_response_headers(session_options("session-proxy"), &proxy_model).await;

    assert_eq!(captured.session_id, None);
    assert_eq!(captured.client_request_id, None);
    assert_eq!(captured.x_session_id.as_deref(), Some("session-proxy"));
    assert_eq!(payload.get("session_id"), None);
    assert_eq!(payload["prompt_cache_key"], json!("session-proxy"));
}

#[tokio::test]
async fn auto_detects_openrouter_session_affinity_header_for_openrouter_responses_endpoints() {
    let open_router_model = with_fields(
        &gpt_5_4(),
        &json!({ "provider": "openrouter", "baseUrl": "https://openrouter.ai/api/v1" }),
    );
    let (captured, payload) =
        capture_openai_response_headers(session_options("session-openrouter"), &open_router_model)
            .await;

    assert_eq!(captured.session_id, None);
    assert_eq!(captured.client_request_id, None);
    assert_eq!(captured.x_session_id.as_deref(), Some("session-openrouter"));
    assert_eq!(payload.get("session_id"), None);
    assert_eq!(payload["prompt_cache_key"], json!("session-openrouter"));
}

#[tokio::test]
async fn uses_openai_no_session_format_when_configured() {
    let proxy_model = with_fields(
        &gpt_5_4(),
        &json!({
            "provider": "proxy",
            "baseUrl": "https://proxy.example.com/v1",
            "compat": { "sessionAffinityFormat": "openai-nosession" },
        }),
    );
    let (captured, payload) =
        capture_openai_response_headers(session_options("session-proxy"), &proxy_model).await;

    assert_eq!(captured.session_id, None);
    assert_eq!(captured.client_request_id.as_deref(), Some("session-proxy"));
    assert_eq!(captured.x_session_id, None);
    assert_eq!(payload.get("session_id"), None);
    assert_eq!(payload["prompt_cache_key"], json!("session-proxy"));
}

#[tokio::test]
async fn uses_openai_no_session_format_for_opencode_responses_models() {
    let model = model("opencode", "gpt-5.4");
    let (captured, payload) =
        capture_openai_response_headers(session_options("session-opencode"), &model).await;

    assert_eq!(
        compat_field(&model, "sessionAffinityFormat"),
        json!("openai-nosession")
    );
    assert_eq!(captured.session_id, None);
    assert_eq!(
        captured.client_request_id.as_deref(),
        Some("session-opencode")
    );
    assert_eq!(captured.x_session_id, None);
    assert_eq!(payload["prompt_cache_key"], json!("session-opencode"));
}

#[tokio::test]
async fn can_omit_openai_session_id_header_while_preserving_other_affinity_data() {
    let proxy_model = with_fields(
        &gpt_5_4(),
        &json!({
            "provider": "opencode",
            "baseUrl": "https://proxy.example.com/v1",
            "compat": { "sessionAffinityFormat": "openai-nosession" },
        }),
    );
    let (captured, payload) =
        capture_openai_response_headers(session_options("session-123"), &proxy_model).await;

    assert_eq!(captured.session_id, None);
    assert_eq!(captured.client_request_id.as_deref(), Some("session-123"));
    assert_eq!(payload["prompt_cache_key"], json!("session-123"));
}

#[tokio::test]
async fn lets_explicit_headers_override_the_default_openai_cache_affinity_headers() {
    let mut options = session_options("session-123");
    options.stream.request.headers = Some(
        serde_json::from_value::<ProviderHeaders>(json!({
            "session_id": "override-session",
            "x-client-request-id": "override-request",
        }))
        .expect("headers"),
    );
    let (captured, _) = capture_openai_response_headers(options, &gpt_5_4()).await;

    assert_eq!(captured.session_id.as_deref(), Some("override-session"));
    assert_eq!(
        captured.client_request_id.as_deref(),
        Some("override-request")
    );
}

#[tokio::test]
async fn omits_openai_cache_affinity_headers_when_cache_retention_is_none() {
    let mut options = session_options("session-123");
    options.stream.cache_retention = Some(CacheRetention::None);
    let (captured, _) = capture_openai_response_headers(options, &gpt_5_4()).await;

    assert_eq!(captured.session_id, None);
    assert_eq!(captured.client_request_id, None);
}

/// `expect(actual).toBeCloseTo(expected, 12)`.
fn assert_close(actual: f64, expected: f64) {
    assert!(
        (actual - expected).abs() < 0.5e-12,
        "{actual} is not close to {expected}"
    );
}

#[tokio::test]
async fn applies_cost_multiplier_for_requested_and_returned_service_tier() {
    for (model_id, service_tier, response_service_tier, multiplier) in [
        ("gpt-5.4", "priority", "priority", 2.0),
        ("gpt-5.5", "priority", "priority", 2.5),
        ("gpt-5.5", "flex", "flex", 0.5),
        // GPT-6 models report Fast mode as "fast" even when "priority" is requested (#10034)
        ("gpt-6-luna", "priority", "fast", 2.0),
        ("gpt-6-luna", "fast", "fast", 2.0),
    ] {
        let model = model("openai", model_id);
        let token_count = 100_000_u32;
        let token_scale = f64::from(token_count) / 1_000_000.0;
        let event = json!({
            "type": "response.completed",
            "response": {
                "status": "completed",
                "service_tier": response_service_tier,
                "usage": {
                    "input_tokens": token_count,
                    "output_tokens": token_count,
                    "total_tokens": token_count * 2,
                    "input_tokens_details": { "cached_tokens": 0 },
                },
            },
        });
        let sse = format!("data: {event}\n\n");

        let (_, result) = run(
            &model,
            &sys_hi_context(),
            extra_options(&json!({ "serviceTier": service_tier })),
            MockResponse::sse(sse),
        )
        .await;

        assert_close(
            result.usage.cost.input,
            model.cost.input * multiplier * token_scale,
        );
        assert_close(
            result.usage.cost.output,
            model.cost.output * multiplier * token_scale,
        );
        assert_close(
            result.usage.cost.total,
            (model.cost.input + model.cost.output) * multiplier * token_scale,
        );
    }
}

// openai-responses max_output_tokens compat

#[tokio::test]
async fn sends_max_output_tokens_by_default() {
    let mut options = ProviderStreamOptions::default();
    options.stream.max_tokens = Some(1024);
    let (request, _) = run(&gpt_5_4(), &sys_hi_context(), options, done_response()).await;

    assert_eq!(request.body["max_output_tokens"], json!(1024));
}

#[tokio::test]
async fn omits_max_output_tokens_when_supports_max_output_tokens_is_false() {
    let base_model = gpt_5_4();
    let mut compat = serde_json::to_value(&base_model).expect("model json")["compat"].clone();
    if compat.is_null() {
        compat = json!({});
    }
    compat["supportsMaxOutputTokens"] = json!(false);
    let model = with_fields(&base_model, &json!({ "compat": compat }));
    let mut options = ProviderStreamOptions::default();
    options.stream.max_tokens = Some(1024);
    let (request, _) = run(&model, &sys_hi_context(), options, done_response()).await;

    assert_eq!(request.body.get("max_output_tokens"), None);
}
