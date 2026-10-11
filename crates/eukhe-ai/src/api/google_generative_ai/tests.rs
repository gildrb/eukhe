//! Ports of the `google-generative-ai` cases of `google-raw-stop-reason`,
//! `google-thinking-level-map`, and `google-thinking-disable`, plus wire
//! checks of the SDK port against a local HTTP server.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_types::pi_ai::{
    AssistantContentBlock, JsonValue, Model, StopReason, ThinkingBudgets, ThinkingLevel,
};
use serde_json::json;

use super::*;
use crate::api::google_shared::genai::mock;
use crate::api::google_shared::test_support::{
    builtin_model, capture_simple_payload, hello_context, model, serve_once,
};
use crate::types::OnProviderStreamEvent;
use crate::utils::pi_user_agent::get_pi_user_agent;

fn api_key_options() -> ProviderStreamOptions {
    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = Some("test-api-key".to_owned());
    options
}

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

fn gemini_flash() -> Model {
    builtin_model("google", "gemini-2.5-flash")
}

#[tokio::test]
async fn preserves_raw_gemini_finish_reasons_for_google_generative_ai_errors() {
    let _mock = mock::install(vec![finish_chunk("MALFORMED_FUNCTION_CALL", false)]).await;
    let message = stream(&gemini_flash(), &hello_context(), api_key_options())
        .result()
        .await;
    assert_eq!(message.stop_reason, StopReason::Error);
    assert_eq!(
        message.raw_stop_reason.as_deref(),
        Some("MALFORMED_FUNCTION_CALL")
    );
    assert_eq!(
        message.error_message.as_deref(),
        Some("Provider stopped with: MALFORMED_FUNCTION_CALL")
    );
    // eukhe addition: the stream-failure diagnostic.
    let diagnostics = message.diagnostics.expect("diagnostics");
    assert_eq!(diagnostics[0].kind, "provider_stream_failure");
}

#[tokio::test]
async fn preserves_max_tokens_with_a_tool_call_as_length() {
    let _mock = mock::install(vec![finish_chunk("MAX_TOKENS", true)]).await;
    let message = stream(&gemini_flash(), &hello_context(), api_key_options())
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
    let message = stream(&gemini_flash(), &hello_context(), api_key_options())
        .result()
        .await;
    assert_eq!(message.stop_reason, StopReason::ToolUse);
    assert_eq!(message.raw_stop_reason.as_deref(), Some("STOP"));
    assert!(message
        .content
        .iter()
        .any(|block| matches!(block, AssistantContentBlock::ToolCall(_))));
}

/// Chunks and models an `onProviderStreamEvent` observer received.
pub(crate) type ReceivedEvents = Arc<Mutex<Vec<(JsonValue, Model)>>>;

/// `onProviderStreamEvent` recording each chunk and model.
pub(crate) fn recording_observer() -> (OnProviderStreamEvent, ReceivedEvents) {
    let received = Arc::new(Mutex::new(Vec::new()));
    let sink = Arc::clone(&received);
    let observer: OnProviderStreamEvent = Arc::new(move |chunk, model| {
        let sink = Arc::clone(&sink);
        let entry = (chunk.clone(), model.clone());
        Box::pin(async move {
            tokio::task::yield_now().await;
            sink.lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(entry);
            Ok(())
        })
    });
    (observer, received)
}

pub(crate) fn event_chunks() -> Vec<JsonValue> {
    vec![
        json!({ "responseId": "resp_google", "candidates": [{ "content": { "parts": [{ "text": "hello" }] } }] }),
        json!({
            "candidates": [{ "finishReason": "STOP" }],
            "usageMetadata": { "promptTokenCount": 2, "candidatesTokenCount": 1, "totalTokenCount": 3 }
        }),
    ]
}

#[tokio::test]
async fn forwards_each_sdk_chunk_in_order_before_normalizing_it() {
    let chunks = event_chunks();
    let _mock = mock::install(chunks.clone()).await;
    let model = gemini_flash();
    let (observer, received) = recording_observer();
    let mut options = api_key_options();
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

async fn capture_google_headers(headers: Option<ProviderHeaders>) -> JsonValue {
    let mock = mock::install(vec![finish_chunk("STOP", false)]).await;
    let mut options = api_key_options();
    options.stream.request.headers = headers;
    stream(&gemini_flash(), &hello_context(), options)
        .result()
        .await;
    let calls = mock.constructor_calls();
    assert_eq!(calls.len(), 1);
    calls[0]["httpOptions"]["headers"].clone()
}

#[tokio::test]
async fn uses_pis_user_agent_by_default() {
    assert_eq!(
        capture_google_headers(None).await["User-Agent"],
        json!(get_pi_user_agent())
    );
}

#[tokio::test]
async fn lets_explicit_headers_override_the_default_user_agent() {
    let mut headers = ProviderHeaders::new();
    headers.insert("User-Agent".to_owned(), Some("custom-agent".to_owned()));
    assert_eq!(
        capture_google_headers(Some(headers)).await["User-Agent"],
        json!("custom-agent")
    );
}

// ---------------------------------------------------------------------------
// google-thinking-level-map.test.ts (Google Generative AI)
// ---------------------------------------------------------------------------

fn level_map_model(id: &str, map: &JsonValue) -> Model {
    model(&json!({
        "id": id,
        "api": "google-generative-ai",
        "provider": "test-google",
        "baseUrl": "https://example.invalid/v1beta",
        "thinkingLevelMap": map,
        "maxTokens": 4096
    }))
}

async fn capture(id: &str, map: &JsonValue, reasoning: Option<ThinkingLevel>) -> JsonValue {
    capture_budget(id, map, reasoning, None).await
}

async fn capture_budget(
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
    let payload = capture("gemini-3.8-flash", &map, None).await;
    assert_eq!(
        payload["config"]["thinkingConfig"],
        json!({ "thinkingLevel": "LOW" })
    );
}

#[tokio::test]
async fn preserves_native_medium_effort_for_gemini_3_1_pro() {
    let map: JsonValue = serde_json::from_str(NATIVE_LEVELS).unwrap();
    let payload = capture("gemini-3.1-pro-preview", &map, Some(ThinkingLevel::Medium)).await;
    assert_eq!(
        payload["config"]["thinkingConfig"],
        json!({ "includeThoughts": true, "thinkingLevel": "MEDIUM" })
    );
}

#[tokio::test]
async fn disables_gemini_2_5_thinking_when_reasoning_is_omitted() {
    let payload = capture("gemini-2.5-flash", &json!({}), None).await;
    assert_eq!(
        payload["config"]["thinkingConfig"],
        json!({ "thinkingBudget": 0 })
    );
}

#[tokio::test]
async fn maps_xhigh_and_max_to_a_supported_level() {
    for reasoning in [ThinkingLevel::Xhigh, ThinkingLevel::Max] {
        let payload = capture(
            "gemini-3.7-flash",
            &json!({ "xhigh": "high", "max": "high" }),
            Some(reasoning),
        )
        .await;
        assert_eq!(
            payload["config"]["thinkingConfig"],
            json!({ "includeThoughts": true, "thinkingLevel": "HIGH" })
        );
    }
}

#[tokio::test]
async fn honors_uppercase_provider_values_for_standard_levels() {
    let payload = capture(
        "gemini-3.7-flash",
        &json!({ "high": "LOW" }),
        Some(ThinkingLevel::High),
    )
    .await;
    assert_eq!(
        payload["config"]["thinkingConfig"]["thinkingLevel"],
        json!("LOW")
    );
}

#[tokio::test]
async fn uses_mapped_levels_for_token_budgets() {
    let payload = capture_budget(
        "gemini-2.5-flash",
        &json!({ "xhigh": "high" }),
        Some(ThinkingLevel::Xhigh),
        Some(ThinkingBudgets {
            high: Some(1234),
            ..ThinkingBudgets::default()
        }),
    )
    .await;
    assert_eq!(
        payload["config"]["thinkingConfig"]["thinkingBudget"],
        json!(1234)
    );
}

// ---------------------------------------------------------------------------
// google-thinking-disable.test.ts (Google Generative AI, live)
// ---------------------------------------------------------------------------

async fn expect_thinking_disabled(model: &Model, max_tokens: u64, min_pongs: usize) {
    let context = crate::api::google_shared::test_support::context(&json!({
        "systemPrompt": "You are a precise assistant. Follow the requested output format exactly.",
        "messages": [{
            "role": "user",
            "content": "Before replying, carefully solve 36863 * 5279 internally. Then reply with the word pong repeated exactly 40 times, separated by single spaces. Do not add any other text.",
            "timestamp": 0
        }]
    }));
    let mut options = SimpleStreamOptions::default();
    options.stream.max_tokens = Some(max_tokens);
    options.stream.temperature = Some(0.0);
    options.stream.request.api_key = std::env::var("GEMINI_API_KEY").ok();
    let events = stream_simple(model, &context, options);
    let mut thinking_events = 0;
    let mut iterator = events.events();
    while let Some(event) = futures::StreamExt::next(&mut iterator).await {
        if event.type_name().starts_with("thinking_") {
            thinking_events += 1;
        }
    }
    let response = events.result().await;
    assert_eq!(
        response.stop_reason,
        StopReason::Stop,
        "{:?}",
        response.error_message
    );
    assert_eq!(thinking_events, 0);
    let text: String = response
        .content
        .iter()
        .filter_map(|block| match block {
            AssistantContentBlock::Text(text) => Some(text.text.as_str()),
            AssistantContentBlock::Thinking(_) | AssistantContentBlock::ToolCall(_) => None,
        })
        .collect();
    assert!(response
        .content
        .iter()
        .all(|block| !matches!(block, AssistantContentBlock::Thinking(_))));
    let pongs = text
        .split(|c: char| !c.is_alphanumeric())
        .filter(|word| word.eq_ignore_ascii_case("pong"))
        .count();
    assert!(pongs >= min_pongs, "{text}");
}

#[tokio::test]
#[ignore = "needs GEMINI_API_KEY; run with --ignored"]
async fn disables_thinking_for_gemini_2_5() {
    expect_thinking_disabled(&gemini_flash(), 160, 35).await;
}

#[tokio::test]
#[ignore = "needs GEMINI_API_KEY; run with --ignored"]
async fn disables_thinking_for_gemini_3_x() {
    expect_thinking_disabled(&builtin_model("google", "gemini-3-flash-preview"), 160, 35).await;
}

#[tokio::test]
#[ignore = "needs GEMINI_API_KEY; run with --ignored"]
async fn does_not_error_when_thinking_is_off_for_gemini_3_1_pro() {
    expect_thinking_disabled(&builtin_model("google", "gemini-3.1-pro-preview"), 512, 20).await;
}

// ---------------------------------------------------------------------------
// SDK wire format against a local server
// ---------------------------------------------------------------------------

fn local_model(base_url: &str) -> Model {
    model(&json!({
        "id": "gemini-2.5-flash",
        "api": "google-generative-ai",
        "provider": "google",
        "baseUrl": base_url,
        "reasoning": false
    }))
}

#[tokio::test]
async fn sends_the_sdk_request_and_parses_sse_chunks() {
    let _serial = mock::serial().await;
    let body = [
        r#"data: {"candidates":[{"content":{"parts":[{"text":"Hel"}],"role":"model"}}],"responseId":"r1"}"#,
        r#"data: {"candidates":[{"content":{"parts":[{"text":"lo"}],"role":"model"},"finishReason":"STOP"}],"usageMetadata":{"promptTokenCount":5,"candidatesTokenCount":2,"totalTokenCount":7}}"#,
    ]
    .map(|event| format!("{event}\r\n\r\n"))
    .concat();
    let (base_url, server) = serve_once("200 OK", "text/event-stream", body).await;
    let model = local_model(&format!("{base_url}/v1beta"));
    let context = crate::api::google_shared::test_support::context(&json!({
        "systemPrompt": "Be brief.",
        "messages": [{ "role": "user", "content": "hi", "timestamp": 0 }]
    }));
    let mut options = api_key_options();
    options.stream.temperature = Some(1.0);
    let message = stream(&model, &context, options).result().await;
    let request = server.await.unwrap();

    assert_eq!(
        message.stop_reason,
        StopReason::Stop,
        "{:?}",
        message.error_message
    );
    assert_eq!(
        serde_json::to_value(&message.content).unwrap(),
        json!([{ "type": "text", "text": "Hello" }])
    );
    assert_eq!(message.response_id.as_deref(), Some("r1"));
    assert_eq!(message.usage.input, 5);
    assert_eq!(message.usage.output, 2);
    assert_eq!(message.usage.total_tokens, 7);

    assert_eq!(
        request.request_line,
        "POST /v1beta/models/gemini-2.5-flash:streamGenerateContent?alt=sse HTTP/1.1"
    );
    assert_eq!(request.header("user-agent"), Some(get_pi_user_agent()));
    assert_eq!(
        request.header("x-goog-api-client"),
        Some("google-genai-sdk/2.21.0 gl-node/v26.10.0")
    );
    assert_eq!(request.header("content-type"), Some("application/json"));
    assert_eq!(request.header("x-goog-api-key"), Some("test-api-key"));
    assert_eq!(
        request.body,
        r#"{"contents":[{"parts":[{"text":"hi"}],"role":"user"}],"systemInstruction":{"parts":[{"text":"Be brief."}],"role":"user"},"generationConfig":{"temperature":1}}"#
    );
}

#[tokio::test]
async fn reports_sdk_api_errors_with_the_json_body() {
    let _serial = mock::serial().await;
    let body =
        r#"{"error":{"code":400,"message":"API key not valid.","status":"INVALID_ARGUMENT"}}"#;
    let (base_url, server) =
        serve_once("400 Bad Request", "application/json", body.to_owned()).await;
    let model = local_model(&format!("{base_url}/v1beta"));
    let message = stream(&model, &hello_context(), api_key_options())
        .result()
        .await;
    server.await.unwrap();
    assert_eq!(message.stop_reason, StopReason::Error);
    assert_eq!(message.error_message.as_deref(), Some(body));
}

#[tokio::test]
async fn reports_a_missing_api_key() {
    let message = stream(
        &gemini_flash(),
        &hello_context(),
        ProviderStreamOptions::default(),
    )
    .result()
    .await;
    assert_eq!(
        message.error_message.as_deref(),
        Some("No API key for provider: google")
    );
    let simple = stream_simple(
        &gemini_flash(),
        &hello_context(),
        SimpleStreamOptions::default(),
    )
    .result()
    .await;
    assert_eq!(
        simple.error_message.as_deref(),
        Some("No API key for provider: google")
    );
}
