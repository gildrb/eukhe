//! Port of `test/mistral-raw-stop-reason.test.ts`.

mod mistral_support;

use eukhe_pi_ai::api::mistral_conversations::stream as stream_mistral;
use eukhe_pi_ai::compat::get_model;
use eukhe_pi_ai::types::ProviderStreamOptions;
use eukhe_pi_ai::utils::retry::is_retryable_assistant_error;
use eukhe_pi_ai::utils::transcript::normalize_context;
use eukhe_types::pi_ai::{AssistantMessage, Context, StopReason};
use mistral_support::{mock_fetch, MockResponse};
use serde_json::json;

/// TS `createFetch(finishReason)` + `streamMistral(...).result()`.
async fn run(finish_reason: &str) -> AssistantMessage {
    let model = get_model("mistral", "devstral-medium-latest").expect("model");
    let context = normalize_context(
        serde_json::from_value::<Context>(json!({
            "messages": [{ "role": "user", "content": "hello", "timestamp": 1 }],
        }))
        .expect("context"),
    );
    let event = json!({
        "id": "mistral-response-id",
        "model": model.id,
        "choices": [{ "index": 0, "finish_reason": finish_reason, "delta": {} }],
        "usage": { "prompt_tokens": 1, "completion_tokens": 0, "total_tokens": 1 },
    });
    let (fetch, _) = mock_fetch(MockResponse::sse(
        format!("data: {event}\n\ndata: [DONE]\n\n"),
        &[],
    ))
    .await;
    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = Some("test".into());
    options.stream.request.fetch = Some(fetch);
    stream_mistral(&model, &context, options).result().await
}

#[tokio::test]
async fn preserves_raw_mistral_finish_reasons_for_successful_stops() {
    let message = run("stop").await;

    assert_eq!(message.stop_reason, StopReason::Stop);
    assert_eq!(message.raw_stop_reason.as_deref(), Some("stop"));
    assert_eq!(message.error_message, None);
}

#[tokio::test]
async fn preserves_raw_mistral_finish_reasons_for_provider_error_stops() {
    let message = run("error").await;

    assert_eq!(message.stop_reason, StopReason::Error);
    assert_eq!(message.raw_stop_reason.as_deref(), Some("error"));
    assert_eq!(
        message.error_message.as_deref(),
        Some("Provider stopped with: error (server error)")
    );
    // #10487
    assert!(is_retryable_assistant_error(&message));
}

#[tokio::test]
async fn treats_unknown_mistral_finish_reasons_as_provider_error_stops() {
    let message = run("unmapped_error").await;

    assert_eq!(message.stop_reason, StopReason::Error);
    assert_eq!(message.raw_stop_reason.as_deref(), Some("unmapped_error"));
    assert_eq!(
        message.error_message.as_deref(),
        Some("Provider stopped with: unmapped_error")
    );
    assert!(!is_retryable_assistant_error(&message));
}
