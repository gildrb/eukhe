//! Port of `test/anthropic-eager-tool-input-compat.test.ts`. The TS local
//! HTTP server answering an empty SSE body becomes the `fetch` option.

mod anthropic_support;

use anthropic_support::{
    collect, context, mock_fetch, model, requests, CapturedRequest, MockResponse,
};
use eukhe_pi_ai::api::anthropic_messages::stream;
use eukhe_pi_ai::types::ProviderStreamOptions;
use eukhe_types::pi_ai::{CacheRetention, JsonValue};
use serde_json::json;

fn create_model(compat: &JsonValue) -> eukhe_types::pi_ai::Model {
    let mut merged = json!({ "forceAdaptiveThinking": true });
    if let (Some(merged), Some(compat)) = (merged.as_object_mut(), compat.as_object()) {
        for (key, value) in compat {
            merged.insert(key.clone(), value.clone());
        }
    }
    model(&json!({
        "id": "claude-opus-4-8",
        "name": "Claude Opus 4.8",
        "provider": "test-anthropic",
        "baseUrl": "http://127.0.0.1:9",
        "reasoning": true,
        "contextWindow": 200_000,
        "maxTokens": 32000,
        "compat": merged,
    }))
}

fn create_context(with_tool: bool) -> JsonValue {
    let mut value = json!({
        "messages": [{ "role": "user", "content": "Use the tool", "timestamp": 1 }],
    });
    if with_tool {
        value["tools"] = json!([{
            "name": "lookup",
            "description": "Look up a value",
            "parameters": {
                "type": "object",
                "properties": { "value": { "type": "string" } },
                "required": ["value"],
            },
        }]);
    }
    value
}

async fn capture_anthropic_request(
    compat: &JsonValue,
    context_value: &JsonValue,
) -> CapturedRequest {
    let (fetch, captured) = mock_fetch(MockResponse::sse(""));
    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = Some("test-key".into());
    options.stream.request.fetch = Some(fetch);
    options.stream.cache_retention = Some(CacheRetention::None);
    let _ = collect(stream(
        &create_model(compat),
        &context(context_value),
        options,
    ))
    .await;
    requests(&captured)
        .into_iter()
        .next()
        .expect("Anthropic request was not captured")
}

fn first_tool(body: &JsonValue) -> &JsonValue {
    body["tools"]
        .get(0)
        .filter(|tool| tool.is_object())
        .expect("Expected first tool in request body")
}

#[tokio::test]
async fn sends_per_tool_eager_input_streaming_by_default() {
    let request = capture_anthropic_request(&json!({}), &create_context(true)).await;

    assert_eq!(
        first_tool(&request.body).get("eager_input_streaming"),
        Some(&json!(true))
    );
    assert_eq!(request.header("anthropic-beta"), None);
}

#[tokio::test]
async fn uses_the_legacy_fine_grained_tool_streaming_beta_when_eager_tool_input_streaming_is_disabled(
) {
    let request = capture_anthropic_request(
        &json!({ "supportsEagerToolInputStreaming": false }),
        &create_context(true),
    )
    .await;

    assert_eq!(first_tool(&request.body).get("eager_input_streaming"), None);
    assert_eq!(
        request.header("anthropic-beta").as_deref(),
        Some("fine-grained-tool-streaming-2025-05-14")
    );
}

#[tokio::test]
async fn does_not_send_the_legacy_fine_grained_tool_streaming_beta_when_there_are_no_tools() {
    let request = capture_anthropic_request(
        &json!({ "supportsEagerToolInputStreaming": false }),
        &create_context(false),
    )
    .await;

    assert_eq!(request.body.get("tools"), None);
    assert_eq!(request.header("anthropic-beta"), None);
}
