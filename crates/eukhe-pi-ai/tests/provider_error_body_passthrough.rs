//! Port of `test/provider-error-body-passthrough.test.ts`.
//!
//! When an endpoint behind a proxy / gateway returns a non-2xx response with
//! a body, the provider must surface both the status and the body reason
//! instead of the opaque SDK message.
//!
//! TS replaces the `openai` SDK (`vi.mock("openai")`) with a client whose
//! request rejects with an `APIError` (status 403, parsed body
//! `{ error: "blocked by gateway WAF" }`, message
//! `"403 status code (no body)"`). Here the failure is produced one layer
//! down, where the SDK builds that error: the `fetch` option answers the
//! request with HTTP 403 and the JSON body `{ "error": "blocked by gateway
//! WAF" }`, which the SDK port parses into the same status and parsed body.

use std::sync::Arc;

use eukhe_pi_ai::images::generate_images;
use eukhe_pi_ai::types::{FetchFunction, ProviderImagesOptions};
use eukhe_types::pi_ai::{ImageModel, ImagesContext, ImagesStopReason};
use serde_json::json;

/// A fetch answering every request with HTTP 403 and `body` as JSON.
fn forbidden_fetch(body: &serde_json::Value) -> FetchFunction {
    let body = body.to_string();
    Arc::new(move |_request: reqwest::Request| {
        let body = body.clone();
        Box::pin(async move {
            let response = http::Response::builder()
                .status(403)
                .header("content-type", "application/json")
                .body(body)
                .expect("mock response");
            Ok(reqwest::Response::from(response))
        })
    })
}

#[tokio::test]
async fn surfaces_the_http_body_reason_instead_of_the_opaque_sdk_message_openrouter_images() {
    let model: ImageModel = serde_json::from_value(json!({
        "type": "image",
        "id": "black-forest-labs/flux.2-pro",
        "name": "FLUX.2 Pro",
        "api": "openrouter-images",
        "provider": "openrouter",
        "baseUrl": "https://openrouter.ai/api/v1",
        "input": ["text", "image"],
        "output": ["image"],
        "cost": { "input": 0.015, "output": 0.03, "cacheRead": 0, "cacheWrite": 0 },
    }))
    .expect("image model");
    let context: ImagesContext =
        serde_json::from_value(json!({ "input": [{ "type": "text", "text": "Generate a dog" }] }))
            .expect("images context");
    let mut options = ProviderImagesOptions::default();
    options.images.request.api_key = Some("test".to_owned());
    options.images.request.fetch = Some(forbidden_fetch(
        &json!({ "error": "blocked by gateway WAF" }),
    ));

    let output = generate_images(&model, &context, options)
        .await
        .expect("dispatch");

    assert_eq!(output.stop_reason, ImagesStopReason::Error);
    let error_message = output.error_message.as_deref().unwrap_or_default();
    // The status should be surfaced.
    assert!(error_message.contains("403"), "{error_message}");
    // The body reason must not be swallowed by the opaque SDK message.
    assert!(
        error_message.contains("blocked by gateway WAF"),
        "{error_message}"
    );
    assert_ne!(error_message, "403 status code (no body)");
}
