//! Port of `openai-completions-raw-stop-reason.test.ts`.

use serde_json::json;

use super::support::{run_with_chunks, test_model, user_context};
use crate::api::openai_completions::OpenAICompletionsOptions;
use crate::types::StopReason;

#[tokio::test]
async fn preserves_raw_finish_reasons_for_successful_stops() {
    let (_, _, message) = run_with_chunks(
        &test_model(json!({})),
        &user_context("hello"),
        OpenAICompletionsOptions::default(),
        vec![json!({ "id": "chatcmpl-1", "choices": [{ "index": 0, "delta": {}, "finish_reason": "stop" }] })],
    )
    .await;

    assert_eq!(message.stop_reason, StopReason::Stop);
    assert_eq!(message.raw_stop_reason.as_deref(), Some("stop"));
    assert_eq!(message.error_message, None);
}

#[tokio::test]
async fn preserves_raw_finish_reasons_for_provider_error_stops() {
    let (_, _, message) = run_with_chunks(
        &test_model(json!({})),
        &user_context("hello"),
        OpenAICompletionsOptions::default(),
        vec![json!({ "id": "chatcmpl-2", "choices": [{ "index": 0, "delta": {}, "finish_reason": "content_filter" }] })],
    )
    .await;

    assert_eq!(message.stop_reason, StopReason::Error);
    assert_eq!(message.raw_stop_reason.as_deref(), Some("content_filter"));
    assert_eq!(
        message.error_message.as_deref(),
        Some("Provider finish_reason: content_filter")
    );
}
