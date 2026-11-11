//! eukhe addition: the output cap of an `openai-completions` request (the
//! compiled `Fx.cap`, `laws/facts.bend` `facts_cap_*`): the catalog's max
//! unless the window forces a shrink, omitted when the max is unknown.

use std::sync::PoisonError;

use serde_json::json;

use super::support::{collect, model, payload_recorder, sse_fetch, stop_chunks, user_context};
use crate::api::openai_completions::stream_simple;
use crate::types::{
    JsonValue, Model, ProviderRequestOptions, SimpleStreamOptions, StreamOptions, ThinkingLevel,
    TranscriptContext,
};
use crate::utils::context_tokens::{model_tokenizer, output_cap_prompt_tokens};

/// A reasoning model on a local vLLM with the catalog max `max_tokens`.
fn vllm_model(context_window: u64, max_tokens: u64) -> Model {
    model(json!({
        "id": "qwen3.8-27b",
        "name": "Qwen 3.8 27B (local vLLM)",
        "api": "openai-completions",
        "provider": "local-vllm",
        "baseUrl": "http://localhost:8000/v1",
        "reasoning": true,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": context_window,
        "maxTokens": max_tokens,
        "compat": { "maxTokensField": "max_tokens" },
    }))
}

/// The `onPayload` params of one high-reasoning `streamSimple` call.
async fn capture(model: &Model, context: &TranscriptContext) -> JsonValue {
    let (fetch, _) = sse_fetch(stop_chunks());
    let (on_payload, seen) = payload_recorder();
    collect(stream_simple(
        model,
        context,
        SimpleStreamOptions {
            stream: StreamOptions {
                request: ProviderRequestOptions {
                    api_key: Some("test".to_owned()),
                    fetch: Some(fetch),
                    on_payload: Some(on_payload),
                    ..ProviderRequestOptions::default()
                },
                ..StreamOptions::default()
            },
            reasoning: Some(ThinkingLevel::High),
            ..SimpleStreamOptions::default()
        },
    ))
    .await;
    let payloads = seen.lock().unwrap_or_else(PoisonError::into_inner);
    payloads.last().cloned().expect("payload captured")
}

/// Both output cap fields of a payload.
fn caps(params: &JsonValue) -> (Option<&JsonValue>, Option<&JsonValue>) {
    (
        params.get("max_tokens"),
        params.get("max_completion_tokens"),
    )
}

/// Regression: a reasoning model got a cap below its catalog max (a
/// made-up 16384) and spent it all on thinking. With the window far away
/// the request carries the catalog max whole.
#[tokio::test]
async fn a_reasoning_model_with_a_short_prompt_sends_its_catalog_max() {
    let params = capture(&vllm_model(262_144, 81_920), &user_context("Hi")).await;
    assert_eq!(caps(&params), (Some(&json!(81_920)), None));
}

/// Regression (the user's case): a models.json model without `maxTokens`
/// has its window as its max, which says nothing beyond the window: the
/// request omits the field and the server's own max applies.
#[tokio::test]
async fn a_model_whose_max_is_its_window_omits_the_cap() {
    let params = capture(&vllm_model(262_144, 262_144), &user_context("Hi")).await;
    assert_eq!(caps(&params), (None, None));
}

/// A prompt near the window shrinks the cap to the room it leaves after
/// the prompt (counted locally and padded) and the 4096-token safety
/// margin.
#[tokio::test]
async fn a_long_prompt_near_the_window_shrinks_the_cap_to_the_room() {
    let context = user_context(&"word ".repeat(2_000));
    let prompt =
        output_cap_prompt_tokens(&model_tokenizer(&vllm_model(0, 4000)), context.messages());
    let params = capture(&vllm_model(prompt + 4096 + 1000, 4000), &context).await;
    assert_eq!(caps(&params), (Some(&json!(1000)), None), "prompt {prompt}");
}
