//! Payload cases of `baseten-models.test.ts` (the catalog assertions live in
//! the model-catalog port). TS throws from `onPayload` to stop before the
//! network; here the `fetch` option answers with a plain stop instead.

use std::sync::PoisonError;

use serde_json::json;

use super::support::{payload_recorder, sse_fetch, stop_chunks};
use crate::compat::{get_model, stream_simple};
use crate::types::{
    Context, JsonValue, Model, ProviderRequestOptions, SimpleStreamOptions, StreamOptions,
    ThinkingLevel,
};

fn baseten_model(id: &str) -> Model {
    get_model("baseten", id).unwrap_or_else(|| panic!("missing model baseten/{id}"))
}

/// `streamSimple(model, { messages: [user "test"] }, { apiKey, reasoning,
/// onPayload })`; returns the first payload.
async fn simple_payload(model: &Model, reasoning: Option<ThinkingLevel>) -> JsonValue {
    let (fetch, _requests) = sse_fetch(stop_chunks());
    let (hook, seen) = payload_recorder();
    let options = SimpleStreamOptions {
        stream: StreamOptions {
            request: ProviderRequestOptions {
                api_key: Some("test-baseten-key".to_owned()),
                fetch: Some(fetch),
                on_payload: Some(hook),
                ..ProviderRequestOptions::default()
            },
            ..StreamOptions::default()
        },
        reasoning,
        ..SimpleStreamOptions::default()
    };
    let context: Context = serde_json::from_value(json!({
        "messages": [{ "role": "user", "content": "test", "timestamp": 0 }],
    }))
    .expect("valid context JSON");
    let message = stream_simple(model, context, options)
        .expect("stream starts")
        .result()
        .await;
    let payloads = seen.lock().unwrap_or_else(PoisonError::into_inner);
    payloads
        .first()
        .cloned()
        .unwrap_or_else(|| panic!("no payload captured: {:?}", message.error_message))
}

#[tokio::test]
async fn models_kimi_k2_6_reasoning_as_an_explicit_off_on_toggle() {
    let payload = simple_payload(
        &baseten_model("moonshotai/Kimi-K2.6"),
        Some(ThinkingLevel::High),
    )
    .await;

    assert_eq!(
        payload.get("chat_template_args"),
        Some(&json!({ "enable_thinking": true }))
    );
    assert_eq!(payload.get("reasoning_effort"), None);
}

#[tokio::test]
async fn sends_baseten_chat_template_args_with_reasoning_effort() {
    let payload =
        simple_payload(&baseten_model("zai-org/GLM-5.2"), Some(ThinkingLevel::High)).await;

    assert_eq!(
        payload.get("chat_template_args"),
        Some(&json!({ "enable_thinking": true }))
    );
    assert_eq!(payload.get("reasoning_effort"), Some(&json!("high")));
}

#[tokio::test]
async fn disables_baseten_opt_in_reasoning_when_thinking_is_off() {
    let payload = simple_payload(&baseten_model("zai-org/GLM-5.2"), None).await;

    assert_eq!(
        payload.get("chat_template_args"),
        Some(&json!({ "enable_thinking": false }))
    );
    assert_eq!(payload.get("reasoning_effort"), Some(&json!("none")));
}
