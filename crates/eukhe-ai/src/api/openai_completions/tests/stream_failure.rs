//! eukhe additions (no TS counterpart): the `provider_stream_failure`
//! diagnostic on failed streams and the `prime-inference` compat detection.

use serde_json::json;

use super::super::compat::{detect_compat, get_compat, ResolvedCompat};
use super::support::{
    capture_payload, collect, options_with_fetch, run_with_chunks, test_model, user_context,
};
use crate::api::openai_completions::{stream_with_options, OpenAICompletionsOptions};
use crate::api::system_one_shared::test_fetch::{mock_fetch, recorded, response};
use crate::types::{
    AssistantMessageDiagnostic, CacheControlFormat, IndexMap, JsonValue, MaxTokensField,
    SessionAffinityFormat, StopReason, ThinkingFormat,
};

fn details(diagnostic: &AssistantMessageDiagnostic) -> JsonValue {
    JsonValue::Object(diagnostic.details.clone().expect("diagnostic details"))
}

#[tokio::test]
async fn http_429_appends_one_provider_stream_failure_diagnostic() {
    let (fetch, requests) = mock_fetch(|_| {
        response(
            429,
            &[
                ("content-type", "application/json"),
                ("x-request-id", "req_123"),
                ("retry-after", "7"),
            ],
            json!({ "error": { "message": "Rate limit reached", "type": "rate_limit_error" } })
                .to_string(),
        )
    });

    let (_, message) = collect(stream_with_options(
        &test_model(json!({})),
        &user_context("hi"),
        options_with_fetch(fetch),
    ))
    .await;

    assert_eq!(recorded(&requests).len(), 1);
    assert_eq!(message.stop_reason, StopReason::Error);
    let diagnostics = message.diagnostics.expect("diagnostics");
    assert_eq!(diagnostics.len(), 1);
    let diagnostic = &diagnostics[0];
    assert_eq!(diagnostic.kind, "provider_stream_failure");
    assert_eq!(
        diagnostic
            .error
            .as_ref()
            .and_then(|error| error.name.as_deref()),
        Some("Error")
    );
    assert_eq!(
        details(diagnostic),
        json!({
            "kind": "rate_limit",
            "providerErrorType": "rate_limit_error",
            "status": 429,
            "requestId": "req_123",
            "retryAfterMs": 7000,
        })
    );
}

#[tokio::test]
async fn a_stream_without_finish_reason_ends_with_a_stream_drop_failure() {
    let (_, _, message) = run_with_chunks(
        &test_model(json!({})),
        &user_context("hi"),
        OpenAICompletionsOptions::default(),
        vec![json!({
            "id": "chatcmpl-drop",
            "choices": [{ "index": 0, "delta": { "content": "partial" } }],
        })],
    )
    .await;

    assert_eq!(message.stop_reason, StopReason::Error);
    assert_eq!(
        message.error_message.as_deref(),
        Some("Stream ended without finish_reason")
    );
    let diagnostics = message.diagnostics.expect("diagnostics");
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].kind, "provider_stream_failure");
    assert_eq!(
        details(&diagnostics[0]),
        json!({ "kind": "stream_drop", "providerErrorType": "stream_drop" })
    );
}

#[tokio::test]
async fn a_successful_stream_records_no_diagnostic() {
    let (_, _, message) = run_with_chunks(
        &test_model(json!({})),
        &user_context("hi"),
        OpenAICompletionsOptions::default(),
        super::support::stop_chunks(),
    )
    .await;

    assert_eq!(message.stop_reason, StopReason::Stop);
    assert_eq!(message.diagnostics, None);
}

/// The compat the `prime-inference` gateway resolves to; only the cache
/// format depends on the model id.
fn prime_inference_compat(cache_control_format: Option<CacheControlFormat>) -> ResolvedCompat {
    ResolvedCompat {
        supports_store: false,
        supports_developer_role: false,
        supports_reasoning_effort: true,
        supports_usage_in_streaming: true,
        supports_finish_reason: true,
        max_tokens_field: MaxTokensField::MaxTokens,
        requires_tool_result_name: false,
        requires_assistant_after_tool_result: false,
        requires_thinking_as_text: false,
        requires_reasoning_content_on_assistant_messages: false,
        thinking_format: ThinkingFormat::OpenAI,
        chat_template_kwargs: IndexMap::new(),
        chat_template_args: IndexMap::new(),
        zai_tool_stream: false,
        supports_thinking_token_budget: Some(false),
        thinking_token_budget_field: None,
        supports_strict_mode: false,
        supports_openai_grammar_tools: false,
        supports_mid_convo_system_messages: Some(false),
        supports_mid_convo_tool_additions: Some(false),
        cache_control_format,
        send_session_affinity_headers: false,
        session_affinity_format: SessionAffinityFormat::OpenAI,
        supports_long_cache_retention: true,
        vllm_priority: None,
    }
}

#[test]
fn detects_prime_inference_by_provider() {
    let model = test_model(json!({
        "id": "anthropic/claude-sonnet-4.5",
        "provider": "prime-inference",
        "baseUrl": "https://example.invalid/v1",
    }));

    assert_eq!(
        detect_compat(&model),
        prime_inference_compat(Some(CacheControlFormat::Anthropic))
    );
    assert_eq!(get_compat(&model), detect_compat(&model));
}

#[test]
fn detects_prime_inference_by_base_url() {
    let model = test_model(json!({
        "id": "anthropic/claude-sonnet-4.5",
        "provider": "custom",
        "baseUrl": "https://api.pinference.ai/api/v1",
    }));

    assert_eq!(
        detect_compat(&model),
        prime_inference_compat(Some(CacheControlFormat::Anthropic))
    );
}

#[test]
fn uses_no_cache_format_for_non_anthropic_prime_inference_models() {
    let model = test_model(json!({
        "id": "openai/gpt-5",
        "provider": "prime-inference",
        "baseUrl": "https://api.pinference.ai/api/v1",
    }));

    assert_eq!(detect_compat(&model), prime_inference_compat(None));
}

#[tokio::test]
async fn prime_inference_payload_uses_max_tokens_and_no_store() {
    let mut options = OpenAICompletionsOptions::default();
    options.stream.max_tokens = Some(1000);
    let payload = capture_payload(
        &test_model(json!({
            "id": "anthropic/claude-sonnet-4.5",
            "provider": "prime-inference",
            "baseUrl": "https://api.pinference.ai/api/v1",
        })),
        &user_context("hi"),
        options,
    )
    .await;

    assert_eq!(payload.get("max_tokens"), Some(&json!(1000)));
    assert_eq!(payload.get("max_completion_tokens"), None);
    assert_eq!(payload.get("store"), None);
}
