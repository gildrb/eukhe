//! Port of `test/compat-env.test.ts`.

mod common;

use std::sync::{Arc, Mutex, PoisonError};

use common::{context, ok_stream};
use eukhe_pi_ai::compat::{complete, register_api_provider, reset_api_providers, ApiProvider};
use eukhe_pi_ai::types::ProviderStreamOptions;
use eukhe_types::pi_ai::Model;

fn model() -> Model {
    serde_json::from_value(serde_json::json!({
        "id": "test-model",
        "name": "Test Model",
        "api": "openai-responses",
        "provider": "custom-openai",
        "baseUrl": "https://example.test/v1",
        "reasoning": false,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 128_000,
        "maxTokens": 4096,
    }))
    .expect("model")
}

/// TS `afterEach(resetApiProviders)`.
struct ResetApiProviders;

impl Drop for ResetApiProviders {
    fn drop(&mut self) {
        reset_api_providers();
    }
}

#[tokio::test]
async fn dispatches_unknown_providers_through_the_legacy_api_registry() {
    let _reset = ResetApiProviders;
    let captured_api_key: Arc<Mutex<Option<String>>> = Arc::default();
    let (stream_capture, simple_capture) =
        (Arc::clone(&captured_api_key), Arc::clone(&captured_api_key));
    register_api_provider(
        ApiProvider {
            api: "openai-responses".to_owned(),
            stream: Arc::new(move |model, _context, options| {
                *stream_capture
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner) = options.stream.request.api_key;
                ok_stream(model)
            }),
            stream_simple: Arc::new(move |model, _context, options| {
                *simple_capture
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner) = options.stream.request.api_key;
                ok_stream(model)
            }),
        },
        None,
    );

    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = Some("request-key".to_owned());
    complete(&model(), context(), options)
        .await
        .expect("complete");

    assert_eq!(
        captured_api_key
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .as_deref(),
        Some("request-key")
    );
}
