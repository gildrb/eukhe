//! diagnostic on failed streams.

use eukhe_types::pi_ai::DiagnosticKind;
use serde_json::json;

use super::support::{collect, options_with_fetch, run_with_chunks, test_model, user_context};
use crate::api::openai_completions::{stream_with_options, OpenAICompletionsOptions};
use crate::api::system_one_shared::test_fetch::{mock_fetch, recorded, response};
use crate::types::{AssistantMessageDiagnostic, JsonValue, StopReason};

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
    assert_eq!(diagnostic.kind, DiagnosticKind::ProviderStreamFailure);
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
    assert_eq!(diagnostics[0].kind, DiagnosticKind::ProviderStreamFailure);
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
