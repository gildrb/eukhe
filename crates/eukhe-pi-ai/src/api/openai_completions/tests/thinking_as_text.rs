//! Port of `openai-completions-thinking-as-text.test.ts`.
//!
//! The TS endpoint test runs a local `http` server; here a recording mock
//! `fetch` answers with the same SSE chunks (deterministic, no sockets).

use serde_json::{json, Value as JsonValue};

use super::super::compat::get_compat;
use super::super::convert::{convert_messages, ConvertCompletionsMessagesOptions};
use super::support::{collect, context, model, sse_fetch};
use crate::api::openai_completions::stream;
use crate::api::system_one_shared::test_fetch::recorded;
use crate::types::{
    AssistantMessageEvent, Model, ProviderRequestOptions, ProviderStreamOptions, StreamOptions,
    TranscriptContext,
};

fn build_model(base_url: &str) -> Model {
    model(json!({
        "id": "repro-model",
        "name": "Repro Model",
        "api": "openai-completions",
        "provider": "repro-provider",
        "baseUrl": base_url,
        "reasoning": true,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 128_000,
        "maxTokens": 4096,
        "compat": {
            "supportsStore": true,
            "supportsDeveloperRole": true,
            "supportsReasoningEffort": true,
            "supportsUsageInStreaming": true,
            "supportsFinishReason": true,
            "maxTokensField": "max_completion_tokens",
            "requiresToolResultName": false,
            "requiresAssistantAfterToolResult": false,
            "requiresThinkingAsText": true,
            "requiresReasoningContentOnAssistantMessages": false,
            "thinkingFormat": "openai",
            "openRouterRouting": {},
            "vercelGatewayRouting": {},
            "chatTemplateKwargs": {},
            "chatTemplateArgs": {},
            "zaiToolStream": false,
            "supportsThinkingTokenBudget": false,
            "supportsStrictMode": true,
            "supportsOpenAIGrammarTools": false,
            "supportsMidConvoSystemMessages": false,
            "supportsMidConvoToolAdditions": false,
            "sendSessionAffinityHeaders": false,
            "sessionAffinityFormat": "openai",
            "supportsLongCacheRetention": true,
        },
    }))
}

fn build_assistant(content: &JsonValue) -> JsonValue {
    json!({
        "role": "assistant",
        "content": content,
        "api": "openai-completions",
        "provider": "repro-provider",
        "model": "repro-model",
        "usage": {
            "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
            "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
        },
        "stopReason": "stop",
        "timestamp": 2,
    })
}

/// `normalizeContext(buildContext(assistant))`.
// Test helpers take literal JSON by value, mirroring the TS call shape.
#[allow(clippy::needless_pass_by_value)]
fn build_context(assistant: JsonValue) -> TranscriptContext {
    context(json!({
        "messages": [
            { "role": "user", "content": "hello", "timestamp": 1 },
            assistant,
            { "role": "user", "content": "continue", "timestamp": 3 },
        ],
    }))
}

fn convert(model: &Model, context: &TranscriptContext) -> Vec<JsonValue> {
    convert_messages(
        model,
        context,
        &get_compat(model),
        &ConvertCompletionsMessagesOptions::default(),
    )
    .unwrap_or_else(|error| panic!("convert_messages failed: {error:?}"))
}

fn thinking_plus_text() -> JsonValue {
    json!([
        { "type": "thinking", "thinking": "internal reasoning" },
        { "type": "text", "text": "visible answer" },
    ])
}

#[test]
fn serializes_same_model_thinking_plus_text_replay_as_assistant_text_parts() {
    let model = build_model("http://127.0.0.1:1");
    let messages = convert(
        &model,
        &build_context(build_assistant(&thinking_plus_text())),
    );

    assert_eq!(
        messages[1],
        json!({
            "role": "assistant",
            "content": [
                { "type": "text", "text": "internal reasoning" },
                { "type": "text", "text": "visible answer" },
            ],
        })
    );
}

#[test]
fn serializes_same_model_thinking_only_replay_as_assistant_text_parts() {
    let model = build_model("http://127.0.0.1:1");
    let messages = convert(
        &model,
        &build_context(build_assistant(&json!([
            { "type": "thinking", "thinking": "internal reasoning" },
        ]))),
    );

    assert_eq!(
        messages[1],
        json!({
            "role": "assistant",
            "content": [{ "type": "text", "text": "internal reasoning" }],
        })
    );
}

#[tokio::test]
async fn reaches_the_endpoint_when_replay_contains_both_thinking_and_text() {
    let (fetch, requests) = sse_fetch(vec![
        json!({
            "id": "chatcmpl-repro",
            "object": "chat.completion.chunk",
            "created": 0,
            "model": "repro-model",
            "choices": [{ "index": 0, "delta": { "role": "assistant", "content": "ok" }, "finish_reason": null }],
        }),
        json!({
            "id": "chatcmpl-repro",
            "object": "chat.completion.chunk",
            "created": 0,
            "model": "repro-model",
            "choices": [{ "index": 0, "delta": {}, "finish_reason": "stop" }],
            "usage": { "prompt_tokens": 1, "completion_tokens": 1 },
        }),
    ]);
    let options = ProviderStreamOptions {
        stream: StreamOptions {
            request: ProviderRequestOptions {
                api_key: Some("test-key".to_owned()),
                fetch: Some(fetch),
                ..ProviderRequestOptions::default()
            },
            ..StreamOptions::default()
        },
        ..ProviderStreamOptions::default()
    };
    let model = build_model("http://127.0.0.1:1");
    let (events, _) = collect(stream(
        &model,
        &build_context(build_assistant(&thinking_plus_text())),
        options,
    ))
    .await;

    let requests = recorded(&requests);
    assert_eq!(requests.len(), 1);
    assert_eq!(requests[0].method, "POST");
    assert_eq!(requests[0].url, "http://127.0.0.1:1/chat/completions");
    assert_eq!(
        requests[0].json()["messages"][1],
        json!({
            "role": "assistant",
            "content": [
                { "type": "text", "text": "internal reasoning" },
                { "type": "text", "text": "visible answer" },
            ],
        })
    );

    assert!(
        matches!(events.last(), Some(AssistantMessageEvent::Done { .. })),
        "terminal event: {:?}",
        events.last()
    );
}
