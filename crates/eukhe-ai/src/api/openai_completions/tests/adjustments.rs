//! eukhe addition: requested fields the `openai-completions` request drops
//! are recorded on the response (no TS counterpart).

use serde_json::json;

use super::support::{
    collect, context, run_with_chunks, sse_fetch, stop_chunks, test_model, user_context,
};
use crate::api::openai_completions::{stream_simple, OpenAICompletionsOptions};
use crate::api::system_one_shared::test_fetch::recorded;
use crate::types::{
    AdjustedField, AdjustmentReason, AssistantMessageEvent, JsonValue, RequestAdjustment,
    ServiceTier, SimpleStreamOptions, StopReason, ThinkingLevel,
};

#[tokio::test]
async fn records_a_service_tier_the_host_does_not_take() {
    let model = test_model(json!({
        "provider": "prime-inference",
        "baseUrl": "https://api.pinference.ai/api/v1",
    }));
    let mut options = OpenAICompletionsOptions::default();
    options.stream.service_tier = Some(ServiceTier::Flex);

    let (request, events, message) =
        run_with_chunks(&model, &user_context("hi"), options, stop_chunks()).await;

    assert_eq!(request.expect("request").json().get("service_tier"), None);
    let expected = [RequestAdjustment::dropped(
        AdjustedField::ServiceTier,
        AdjustmentReason::UnsupportedByModel,
    )];
    let Some(AssistantMessageEvent::Start { partial }) = events.first() else {
        panic!("expected a start event, got {events:?}");
    };
    assert_eq!(partial.adjustments, expected);
    assert_eq!(message.stop_reason, StopReason::Stop);
    assert_eq!(message.adjustments, expected);
}

#[tokio::test]
async fn records_a_declined_strict_tool_preference_with_its_tool_name() {
    let model = test_model(json!({ "compat": { "supportsStrictMode": false } }));
    let transcript = context(json!({
        "messages": [{ "role": "user", "content": "hi", "timestamp": 1 }],
        "tools": [{
            "name": "sample_tool",
            "description": "Sample tool",
            "parameters": {
                "type": "object",
                "properties": { "payload": { "type": "string" } },
                "required": ["payload"],
            },
            "constrainedSampling": { "type": "json_schema", "strict": "prefer" },
        }],
    }));

    let (request, _, message) = run_with_chunks(
        &model,
        &transcript,
        OpenAICompletionsOptions::default(),
        stop_chunks(),
    )
    .await;

    let body = request.expect("request").json();
    assert_eq!(body["tools"][0]["function"].get("strict"), None);
    assert_eq!(message.stop_reason, StopReason::Stop);
    assert_eq!(
        message.adjustments,
        [RequestAdjustment::dropped(
            AdjustedField::StrictTool,
            AdjustmentReason::UnsupportedByModel,
        )
        .for_subject("sample_tool")]
    );
}

#[tokio::test]
async fn records_a_reasoning_effort_the_host_does_not_take() {
    let model = test_model(json!({
        "reasoning": true,
        "compat": { "supportsReasoningEffort": false },
    }));
    let options = OpenAICompletionsOptions {
        reasoning_effort: Some(ThinkingLevel::High),
        ..OpenAICompletionsOptions::default()
    };

    let (request, _, message) =
        run_with_chunks(&model, &user_context("hi"), options, stop_chunks()).await;

    assert_eq!(
        request.expect("request").json().get("reasoning_effort"),
        None
    );
    assert_eq!(
        message.adjustments,
        [RequestAdjustment::dropped(
            AdjustedField::ReasoningEffort,
            AdjustmentReason::UnsupportedByModel,
        )]
    );
}

#[tokio::test]
async fn stream_simple_records_max_tokens_clamped_to_the_context_window() {
    let model = test_model(json!({}));
    let (fetch, requests) = sse_fetch(stop_chunks());
    let mut options = SimpleStreamOptions::default();
    options.stream.max_tokens = Some(200_000);
    options.stream.request.api_key = Some("test".to_owned());
    options.stream.request.fetch = Some(fetch);

    let (_, message) = collect(stream_simple(&model, &user_context("hi"), options)).await;

    let body = recorded(&requests)
        .into_iter()
        .next()
        .expect("request")
        .json();
    let sent = body
        .get("max_completion_tokens")
        .or_else(|| body.get("max_tokens"))
        .and_then(JsonValue::as_u64)
        .expect("max tokens");
    assert!(sent < 128_000, "{sent}");
    assert_eq!(message.stop_reason, StopReason::Stop);
    assert_eq!(
        message.adjustments,
        [RequestAdjustment::clamped(
            AdjustedField::MaxTokens,
            200_000,
            sent,
            AdjustmentReason::ContextWindow,
        )]
    );
}
