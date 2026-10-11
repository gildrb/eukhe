//! Port of `openai-completions-response-model.test.ts`.
//!
//! Router/virtual ids (e.g. `OpenRouter` `auto`) keep `model` pinned to the
//! requested id and surface the routed concrete id on `response_model`.

use serde_json::json;

use super::support::{model, run_with_chunks, user_context};
use crate::api::openai_completions::OpenAICompletionsOptions;
use crate::types::{AssistantMessage, JsonValue, Model, StopReason};

fn open_router_auto() -> Model {
    model(json!({
        "id": "openrouter/auto",
        "name": "OpenRouter Auto",
        "api": "openai-completions",
        "provider": "openrouter",
        "baseUrl": "https://openrouter.ai/api/v1",
        "reasoning": false,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 200_000,
        "maxTokens": 8192,
    }))
}

async fn complete(chunks: Vec<JsonValue>) -> AssistantMessage {
    let (_, _, message) = run_with_chunks(
        &open_router_auto(),
        &user_context("hi"),
        OpenAICompletionsOptions::default(),
        chunks,
    )
    .await;
    message
}

#[tokio::test]
async fn surfaces_routed_chunk_model_on_response_model_without_changing_model() {
    let message = complete(vec![
        json!({ "id": "chatcmpl-1", "model": "anthropic/claude-opus-4.8", "choices": [{ "index": 0, "delta": { "content": "hi" } }] }),
        json!({
            "id": "chatcmpl-1",
            "model": "anthropic/claude-opus-4.8",
            "choices": [{ "index": 0, "delta": {}, "finish_reason": "stop" }],
            "usage": {
                "prompt_tokens": 10,
                "completion_tokens": 5,
                "prompt_tokens_details": { "cached_tokens": 0 },
                "completion_tokens_details": { "reasoning_tokens": 0 },
            },
        }),
    ])
    .await;

    assert_eq!(message.model, "openrouter/auto");
    assert_eq!(
        message.response_model.as_deref(),
        Some("anthropic/claude-opus-4.8")
    );
    assert_eq!(message.provider, "openrouter");
    assert_eq!(message.stop_reason, StopReason::Stop);
}

#[tokio::test]
async fn leaves_response_model_undefined_when_chunks_echo_the_requested_id() {
    let message = complete(vec![
        json!({ "id": "chatcmpl-2", "model": "openrouter/auto", "choices": [{ "index": 0, "delta": { "content": "hi" } }] }),
        json!({
            "id": "chatcmpl-2",
            "model": "openrouter/auto",
            "choices": [{ "index": 0, "delta": {}, "finish_reason": "stop" }],
            "usage": {
                "prompt_tokens": 1,
                "completion_tokens": 1,
                "prompt_tokens_details": { "cached_tokens": 0 },
                "completion_tokens_details": { "reasoning_tokens": 0 },
            },
        }),
    ])
    .await;

    assert_eq!(message.model, "openrouter/auto");
    assert_eq!(message.response_model, None);
}

#[tokio::test]
async fn ignores_empty_or_missing_chunk_model() {
    let message = complete(vec![
        json!({ "id": "chatcmpl-3", "choices": [{ "index": 0, "delta": { "content": "hi" } }] }),
        json!({ "id": "chatcmpl-3", "model": "", "choices": [{ "index": 0, "delta": { "content": "!" } }] }),
        json!({
            "id": "chatcmpl-3",
            "choices": [{ "index": 0, "delta": {}, "finish_reason": "stop" }],
            "usage": {
                "prompt_tokens": 1,
                "completion_tokens": 2,
                "prompt_tokens_details": { "cached_tokens": 0 },
                "completion_tokens_details": { "reasoning_tokens": 0 },
            },
        }),
    ])
    .await;

    assert_eq!(message.model, "openrouter/auto");
    assert_eq!(message.response_model, None);
}
