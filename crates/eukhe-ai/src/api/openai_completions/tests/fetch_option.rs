//! The `openai-completions` adapter of `fetch-option.test.ts` ("passes fetch
//! through `streamSimple` to `OpenAI` SDK adapters"); the other adapters belong
//! to their APIs' ports. Rust has no ambient `globalThis.fetch` to stub, so
//! "only the custom fetch was called" is the custom fetch recording the one
//! request.

use serde_json::json;

use super::support::{error_fetch, model, user_context};
use crate::api::openai_completions::stream_simple;
use crate::api::system_one_shared::test_fetch::recorded;
use crate::types::{ProviderRequestOptions, SimpleStreamOptions, StreamOptions};

#[tokio::test]
async fn passes_fetch_through_stream_simple_to_openai_sdk_adapters() {
    let (custom, requests) = error_fetch(
        401,
        &json!({ "error": { "message": "upstream rejected request" } }),
    );
    let test_model = model(json!({
        "id": "test-model",
        "name": "Test Model",
        "api": "openai-completions",
        "provider": "test-provider",
        "baseUrl": "https://upstream.test/v1",
        "reasoning": false,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 10_000,
        "maxTokens": 1_000,
    }));
    let options = SimpleStreamOptions {
        stream: StreamOptions {
            request: ProviderRequestOptions {
                api_key: Some("test-key".to_owned()),
                fetch: Some(custom),
                max_retries: Some(0),
                ..ProviderRequestOptions::default()
            },
            ..StreamOptions::default()
        },
        ..SimpleStreamOptions::default()
    };

    stream_simple(&test_model, &user_context("hello"), options)
        .result()
        .await;

    assert_eq!(recorded(&requests).len(), 1);
}
