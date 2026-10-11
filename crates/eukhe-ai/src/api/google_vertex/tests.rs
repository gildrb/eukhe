//! Ports of `google-vertex-api-key-resolution`, the `google-vertex` cases of
//! `google-raw-stop-reason`, `google-thinking-level-map`, and
//! `google-thinking-disable`, plus a wire check of express mode against a
//! local HTTP server.

use std::sync::PoisonError;

use eukhe_types::pi_ai::{
    AssistantContentBlock, JsonObject, JsonValue, Model, StopReason, ThinkingBudgets, ThinkingLevel,
};
use serde_json::json;

use super::*;
use crate::api::google_generative_ai::tests::{event_chunks, recording_observer};
use crate::api::google_shared::genai::mock;
use crate::api::google_shared::test_support::{
    builtin_model, capture_simple_payload, hello_context, model, serve_once,
};
use crate::utils::pi_user_agent::get_pi_user_agent;

fn vertex_model() -> Model {
    builtin_model("google-vertex", "gemini-3-flash-preview")
}

fn options(fields: &JsonValue) -> ProviderStreamOptions {
    let mut options = ProviderStreamOptions::default();
    let mut extra = JsonObject::new();
    for (key, value) in fields.as_object().into_iter().flatten() {
        match key.as_str() {
            "apiKey" => options.stream.request.api_key = value.as_str().map(str::to_owned),
            "headers" => {
                options.stream.request.headers =
                    Some(serde_json::from_value(value.clone()).unwrap());
            }
            _ => {
                extra.insert(key.clone(), value.clone());
            }
        }
    }
    options.extra = extra;
    options
}

fn adc_options() -> ProviderStreamOptions {
    options(&json!({ "project": "test-project", "location": "us-central1" }))
}

fn ok_chunk() -> JsonValue {
    json!({
        "responseId": "vertex-response-id",
        "candidates": [{ "content": { "parts": [{ "text": "ok" }] }, "finishReason": "STOP" }],
        "usageMetadata": { "promptTokenCount": 1, "candidatesTokenCount": 1, "totalTokenCount": 2 }
    })
}

/// `expect(actual).toMatchObject(expected)` for JSON objects.
fn assert_matches_object(actual: &JsonValue, expected: &JsonValue) {
    match (actual, expected) {
        (JsonValue::Object(actual_object), JsonValue::Object(expected_object)) => {
            for (key, value) in expected_object {
                let Some(actual_value) = actual_object.get(key) else {
                    panic!("missing key {key} in {actual}");
                };
                assert_matches_object(actual_value, value);
            }
        }
        _ => assert_eq!(actual, expected),
    }
}

async fn constructor_call(model: &Model, options: ProviderStreamOptions) -> JsonValue {
    let mock = mock::install(vec![ok_chunk()]).await;
    stream(model, &hello_context(), options).result().await;
    let calls = mock.constructor_calls();
    assert_eq!(calls.len(), 1);
    calls[0].clone()
}

// ---------------------------------------------------------------------------
// google-vertex-api-key-resolution.test.ts
// ---------------------------------------------------------------------------

#[tokio::test]
async fn falls_back_to_adc_when_options_api_key_is_a_placeholder_marker() {
    let call = constructor_call(
        &vertex_model(),
        options(&json!({ "apiKey": "<authenticated>", "project": "test-project", "location": "us-central1" })),
    )
    .await;
    assert_matches_object(
        &call,
        &json!({ "vertexai": true, "project": "test-project", "location": "us-central1", "apiVersion": "v1" }),
    );
    assert!(call.get("apiKey").is_none());
}

#[tokio::test]
async fn falls_back_to_adc_when_options_api_key_is_the_gcp_vertex_credentials_marker() {
    let call = constructor_call(
        &vertex_model(),
        options(&json!({ "apiKey": "gcp-vertex-credentials", "project": "test-project", "location": "us-central1" })),
    )
    .await;
    assert_matches_object(
        &call,
        &json!({ "vertexai": true, "project": "test-project", "location": "us-central1", "apiVersion": "v1" }),
    );
    assert!(call.get("apiKey").is_none());
}

/// TS sets `process.env.GOOGLE_CLOUD_API_KEY = "<authenticated>"`; the
/// adapter never reads that variable, so the provider env carries it here
/// (the process environment is shared by parallel tests).
#[tokio::test]
async fn falls_back_to_adc_when_google_cloud_api_key_is_a_placeholder_marker() {
    let mut options = adc_options();
    let mut env = eukhe_types::pi_ai::ProviderEnv::new();
    env.insert(
        "GOOGLE_CLOUD_API_KEY".to_owned(),
        "<authenticated>".to_owned(),
    );
    options.stream.request.env = Some(env);
    let call = constructor_call(&vertex_model(), options).await;
    assert_matches_object(
        &call,
        &json!({ "vertexai": true, "project": "test-project", "location": "us-central1", "apiVersion": "v1" }),
    );
    assert!(call.get("apiKey").is_none());
}

#[tokio::test]
async fn still_uses_the_api_key_client_for_real_api_keys() {
    let call = constructor_call(
        &vertex_model(),
        options(&json!({ "apiKey": "AIzaSyExampleRealisticLookingApiKey123456" })),
    )
    .await;
    assert_matches_object(
        &call,
        &json!({ "vertexai": true, "apiKey": "AIzaSyExampleRealisticLookingApiKey123456", "apiVersion": "v1" }),
    );
    assert!(call.get("project").is_none());
    assert!(call.get("location").is_none());
}

#[tokio::test]
async fn does_not_forward_generated_vertex_base_url_placeholders() {
    let call = constructor_call(&vertex_model(), adc_options()).await;
    assert_eq!(
        call["httpOptions"],
        json!({ "headers": { "User-Agent": get_pi_user_agent() } })
    );
}

#[tokio::test]
async fn lets_explicit_headers_override_the_default_user_agent() {
    let call = constructor_call(
        &vertex_model(),
        options(&json!({
            "project": "test-project",
            "location": "us-central1",
            "headers": { "User-Agent": "custom-agent" }
        })),
    )
    .await;
    assert_eq!(
        call["httpOptions"],
        json!({ "headers": { "User-Agent": "custom-agent" } })
    );
}

fn proxied_model(base_url: &str) -> Model {
    let mut model = vertex_model();
    model.base_url = base_url.to_owned();
    model
}

#[tokio::test]
async fn forwards_custom_base_url_to_the_adc_client() {
    let call = constructor_call(&proxied_model("https://proxy.example.com"), adc_options()).await;
    assert_matches_object(
        &call,
        &json!({
            "vertexai": true,
            "project": "test-project",
            "location": "us-central1",
            "apiVersion": "v1",
            "httpOptions": { "baseUrl": "https://proxy.example.com", "baseUrlResourceScope": "COLLECTION" }
        }),
    );
}

#[tokio::test]
async fn forwards_custom_base_url_to_the_api_key_client() {
    let call = constructor_call(
        &proxied_model("https://proxy.example.com"),
        options(&json!({ "apiKey": "AIzaSyExampleRealisticLookingApiKey123456" })),
    )
    .await;
    assert_matches_object(
        &call,
        &json!({
            "vertexai": true,
            "apiKey": "AIzaSyExampleRealisticLookingApiKey123456",
            "apiVersion": "v1",
            "httpOptions": { "baseUrl": "https://proxy.example.com", "baseUrlResourceScope": "COLLECTION" }
        }),
    );
}

#[tokio::test]
async fn does_not_append_api_version_when_custom_base_url_already_includes_one() {
    let base_url = "https://proxy.example.com/v1/projects/test-project/locations/global";
    let call = constructor_call(&proxied_model(base_url), adc_options()).await;
    assert_matches_object(
        &call,
        &json!({
            "httpOptions": { "baseUrl": base_url, "baseUrlResourceScope": "COLLECTION", "apiVersion": "" }
        }),
    );
}

// ---------------------------------------------------------------------------
// google-raw-stop-reason.test.ts (Google Vertex)
// ---------------------------------------------------------------------------

fn finish_chunk(finish_reason: &str, include_function_call: bool) -> JsonValue {
    let mut candidate = json!({ "finishReason": finish_reason });
    if include_function_call {
        candidate["content"] = json!({ "parts": [{
            "functionCall": { "id": "call-1", "name": "echo", "args": { "value": "truncated" } }
        }] });
    }
    json!({
        "responseId": "google-response-id",
        "candidates": [candidate],
        "usageMetadata": { "promptTokenCount": 1, "candidatesTokenCount": 0, "totalTokenCount": 1 }
    })
}

#[tokio::test]
async fn preserves_raw_gemini_finish_reasons_for_google_vertex_errors() {
    let _mock = mock::install(vec![finish_chunk("SAFETY", false)]).await;
    let message = stream(&vertex_model(), &hello_context(), adc_options())
        .result()
        .await;
    assert_eq!(message.stop_reason, StopReason::Error);
    assert_eq!(message.raw_stop_reason.as_deref(), Some("SAFETY"));
    assert_eq!(
        message.error_message.as_deref(),
        Some("Provider stopped with: SAFETY")
    );
}

#[tokio::test]
async fn preserves_max_tokens_with_a_tool_call_as_length() {
    let _mock = mock::install(vec![finish_chunk("MAX_TOKENS", true)]).await;
    let message = stream(&vertex_model(), &hello_context(), adc_options())
        .result()
        .await;
    assert_eq!(message.stop_reason, StopReason::Length);
    assert_eq!(message.raw_stop_reason.as_deref(), Some("MAX_TOKENS"));
    assert!(message
        .content
        .iter()
        .any(|block| matches!(block, AssistantContentBlock::ToolCall(_))));
}

#[tokio::test]
async fn maps_stop_with_a_tool_call_to_tool_use() {
    let _mock = mock::install(vec![finish_chunk("STOP", true)]).await;
    let message = stream(&vertex_model(), &hello_context(), adc_options())
        .result()
        .await;
    assert_eq!(message.stop_reason, StopReason::ToolUse);
    assert_eq!(message.raw_stop_reason.as_deref(), Some("STOP"));
}

#[tokio::test]
async fn forwards_each_sdk_chunk_in_order_before_normalizing_it() {
    let chunks = event_chunks();
    let _mock = mock::install(chunks.clone()).await;
    let model = vertex_model();
    let (observer, received) = recording_observer();
    let mut options = adc_options();
    options.stream.on_provider_stream_event = Some(observer);
    let result = stream(&model, &hello_context(), options).result().await;
    let received = received
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone();
    assert_eq!(
        received
            .iter()
            .map(|(chunk, _)| chunk.clone())
            .collect::<Vec<_>>(),
        chunks
    );
    assert!(received
        .iter()
        .all(|(_, event_model)| *event_model == model));
    assert_eq!(result.stop_reason, StopReason::Stop);
    assert_eq!(result.response_id.as_deref(), Some("resp_google"));
    assert_eq!(
        serde_json::to_value(&result.content).unwrap(),
        json!([{ "type": "text", "text": "hello" }])
    );
}

// ---------------------------------------------------------------------------
// google-thinking-level-map.test.ts (Google Vertex)
// ---------------------------------------------------------------------------

fn level_map_model(id: &str, map: &JsonValue) -> Model {
    model(&json!({
        "id": id,
        "api": "google-vertex",
        "provider": "test-vertex",
        "baseUrl": "https://example.invalid/v1",
        "thinkingLevelMap": map,
        "maxTokens": 4096
    }))
}

async fn capture(
    id: &str,
    map: &JsonValue,
    reasoning: Option<ThinkingLevel>,
    budgets: Option<ThinkingBudgets>,
) -> JsonValue {
    capture_simple_payload(stream_simple, &level_map_model(id, map), reasoning, budgets).await
}

const NATIVE_LEVELS: &str = r#"{"off":null,"minimal":null,"low":"low","medium":"medium","high":"high","xhigh":null,"max":null}"#;

#[tokio::test]
async fn uses_the_lowest_supported_level_when_reasoning_is_omitted() {
    let map: JsonValue = serde_json::from_str(NATIVE_LEVELS).unwrap();
    let payload = capture("gemini-3.8-flash", &map, None, None).await;
    assert_eq!(
        payload["config"]["thinkingConfig"],
        json!({ "thinkingLevel": "LOW" })
    );
}

#[tokio::test]
async fn preserves_native_medium_effort_for_gemini_3_1_pro() {
    let map: JsonValue = serde_json::from_str(NATIVE_LEVELS).unwrap();
    let payload = capture(
        "gemini-3.1-pro-preview",
        &map,
        Some(ThinkingLevel::Medium),
        None,
    )
    .await;
    assert_eq!(
        payload["config"]["thinkingConfig"],
        json!({ "includeThoughts": true, "thinkingLevel": "MEDIUM" })
    );
}

#[tokio::test]
async fn disables_gemini_2_5_thinking_when_reasoning_is_omitted() {
    let payload = capture("gemini-2.5-flash", &json!({}), None, None).await;
    assert_eq!(
        payload["config"]["thinkingConfig"],
        json!({ "thinkingBudget": 0 })
    );
}

#[tokio::test]
async fn maps_google_vertex_extended_levels() {
    let payload = capture(
        "gemini-3.7-flash",
        &json!({ "xhigh": "high" }),
        Some(ThinkingLevel::Xhigh),
        None,
    )
    .await;
    assert_eq!(
        payload["config"]["thinkingConfig"],
        json!({ "includeThoughts": true, "thinkingLevel": "HIGH" })
    );
}

#[tokio::test]
async fn uses_mapped_google_vertex_levels_for_token_budgets() {
    let payload = capture(
        "gemini-2.5-flash",
        &json!({ "max": "high" }),
        Some(ThinkingLevel::Max),
        Some(ThinkingBudgets {
            high: Some(4321),
            ..ThinkingBudgets::default()
        }),
    )
    .await;
    assert_eq!(
        payload["config"]["thinkingConfig"]["thinkingBudget"],
        json!(4321)
    );
}

// ---------------------------------------------------------------------------
// google-thinking-disable.test.ts (Google Vertex, live)
// ---------------------------------------------------------------------------

async fn expect_vertex_thinking_disabled(model: &Model) {
    let context = crate::api::google_shared::test_support::context(&json!({
        "systemPrompt": "You are a precise assistant. Follow the requested output format exactly.",
        "messages": [{
            "role": "user",
            "content": "Before replying, carefully solve 36863 * 5279 internally. Then reply with the word pong repeated exactly 40 times, separated by single spaces. Do not add any other text.",
            "timestamp": 0
        }]
    }));
    let mut options = SimpleStreamOptions::default();
    options.stream.max_tokens = Some(160);
    options.stream.temperature = Some(0.0);
    options.stream.request.api_key = std::env::var("GOOGLE_CLOUD_API_KEY").ok();
    let response = stream_simple(model, &context, options).result().await;
    assert_eq!(
        response.stop_reason,
        StopReason::Stop,
        "{:?}",
        response.error_message
    );
    assert!(response
        .content
        .iter()
        .all(|block| !matches!(block, AssistantContentBlock::Thinking(_))));
    let pongs = response
        .content
        .iter()
        .filter_map(|block| match block {
            AssistantContentBlock::Text(text) => Some(text.text.clone()),
            AssistantContentBlock::Thinking(_) | AssistantContentBlock::ToolCall(_) => None,
        })
        .collect::<String>()
        .split(|c: char| !c.is_alphanumeric())
        .filter(|word| word.eq_ignore_ascii_case("pong"))
        .count();
    assert!(pongs >= 35);
}

#[tokio::test]
#[ignore = "needs GOOGLE_CLOUD_API_KEY; run with --ignored"]
async fn vertex_disables_thinking_for_gemini_2_5() {
    expect_vertex_thinking_disabled(&builtin_model("google-vertex", "gemini-2.5-flash")).await;
}

#[tokio::test]
#[ignore = "needs GOOGLE_CLOUD_API_KEY; run with --ignored"]
async fn vertex_disables_thinking_for_gemini_3_x() {
    expect_vertex_thinking_disabled(&vertex_model()).await;
}

// ---------------------------------------------------------------------------
// SDK wire format (express mode) against a local server
// ---------------------------------------------------------------------------

#[tokio::test]
async fn express_mode_posts_to_the_collection_base_url() {
    let _serial = mock::serial().await;
    let body = "data: {\"candidates\":[{\"content\":{\"parts\":[{\"text\":\"ok\"}],\"role\":\"model\"},\"finishReason\":\"STOP\"}]}\n\n".to_owned();
    let (base_url, server) = serve_once("200 OK", "text/event-stream", body).await;
    let model = proxied_model(&base_url);
    let message = stream(
        &model,
        &hello_context(),
        options(&json!({ "apiKey": "AIzaSyExampleRealisticLookingApiKey123456" })),
    )
    .result()
    .await;
    let request = server.await.unwrap();
    assert_eq!(
        message.stop_reason,
        StopReason::Stop,
        "{:?}",
        message.error_message
    );
    assert_eq!(
        request.request_line,
        "POST /v1/publishers/google/models/gemini-3-flash-preview:streamGenerateContent?alt=sse HTTP/1.1"
    );
    assert_eq!(
        request.header("x-goog-api-key"),
        Some("AIzaSyExampleRealisticLookingApiKey123456")
    );
    assert_eq!(
        request.body,
        r#"{"contents":[{"parts":[{"text":"hello"}],"role":"user"}],"generationConfig":{}}"#
    );
}

#[tokio::test]
async fn reports_a_missing_project() {
    let mut options = ProviderStreamOptions::default();
    options.stream.request.env = Some(eukhe_types::pi_ai::ProviderEnv::new());
    let model = vertex_model();
    if std::env::var("GOOGLE_CLOUD_PROJECT").is_ok() || std::env::var("GCLOUD_PROJECT").is_ok() {
        return;
    }
    let message = stream(&model, &hello_context(), options).result().await;
    assert_eq!(
        message.error_message.as_deref(),
        Some("Vertex AI requires a project ID. Set GOOGLE_CLOUD_PROJECT/GCLOUD_PROJECT or pass project in options.")
    );
}
