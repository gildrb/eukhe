//! `openai-completions` payload cases of `fireworks-models.test.ts` (the
//! catalog and Anthropic-Messages cases live in their own ports). TS throws
//! from `onPayload` to stop before the network; here the `fetch` option
//! answers with a plain stop instead.

use std::sync::PoisonError;

use serde_json::json;

use super::support::{payload_recorder, sse_fetch, stop_chunks};
use crate::compat::{get_model, stream_simple};
use crate::types::{
    CacheRetention, Context, JsonValue, Model, ProviderRequestOptions, SimpleStreamOptions,
    StreamOptions, ThinkingLevel,
};

fn fireworks_model(id: &str) -> Model {
    get_model("fireworks", id).unwrap_or_else(|| panic!("missing model fireworks/{id}"))
}

/// Options with `apiKey: "test-fireworks-key"`, the stop-answering `fetch`,
/// and a payload recorder; `configure` adds the case's fields.
async fn simple_payload(
    model: &Model,
    configure: impl FnOnce(&mut SimpleStreamOptions),
) -> JsonValue {
    let (fetch, _requests) = sse_fetch(stop_chunks());
    let (hook, seen) = payload_recorder();
    let mut options = SimpleStreamOptions {
        stream: StreamOptions {
            request: ProviderRequestOptions {
                api_key: Some("test-fireworks-key".to_owned()),
                fetch: Some(fetch),
                on_payload: Some(hook),
                ..ProviderRequestOptions::default()
            },
            ..StreamOptions::default()
        },
        ..SimpleStreamOptions::default()
    };
    configure(&mut options);
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
async fn omits_unsupported_long_cache_retention() {
    for model_id in [
        "accounts/fireworks/models/glm-5p3",
        "accounts/fireworks/routers/glm-5p3-fast",
    ] {
        let payload = simple_payload(&fireworks_model(model_id), |options| {
            options.stream.cache_retention = Some(CacheRetention::Long);
            options.stream.session_id = Some("test-fireworks-session".to_owned());
        })
        .await;

        assert_eq!(payload.get("prompt_cache_retention"), None, "{model_id}");
    }
}

#[tokio::test]
async fn routes_kimi_k3_through_the_openai_compatible_api_with_native_effort_controls() {
    let base = fireworks_model("accounts/fireworks/models/kimi-k3");
    assert_eq!(base.api, "openai-completions");

    let payload = simple_payload(&base, |options| {
        options.reasoning = Some(ThinkingLevel::Max);
    })
    .await;

    assert_eq!(payload.get("reasoning_effort"), Some(&json!("max")));
}
