//! "is inherited by every request option surface and simple-stream
//! conversion" of `telemetry-options.test.ts` (`buildBaseOptions`, the
//! simple-options step `openai-completions` `streamSimple` goes through); the
//! dispatch cases live in `tests/telemetry_options.rs`.

use std::sync::Arc;

use futures::future::BoxFuture;
use serde_json::json;

use super::support::{context, model};
use crate::api::simple_options::build_base_options;
use crate::types::{
    ProviderRequestOptions, SimpleStreamOptions, SpanAttributes, SpanCallback, SpanOptions,
    SpanStatus, StreamOptions, TelemetryContext, TelemetrySpan,
};

/// TS `NOOP_TELEMETRY_CONTEXT`: runs span callbacks without recording.
struct NoopTelemetry;

impl TelemetryContext for NoopTelemetry {
    fn start_span(&self, _options: SpanOptions, callback: SpanCallback) -> BoxFuture<'static, ()> {
        let span: Arc<dyn TelemetrySpan> = Arc::new(Self);
        callback(span)
    }
}

impl TelemetrySpan for NoopTelemetry {
    fn add_event(&self, _name: &str, _attributes: Option<SpanAttributes>) {}
    fn set_attributes(&self, _attributes: SpanAttributes) {}
    fn set_status(&self, _status: SpanStatus) {}
}

#[test]
fn is_inherited_by_every_request_option_surface_and_simple_stream_conversion() {
    let telemetry: Arc<dyn TelemetryContext> = Arc::new(NoopTelemetry);
    let telemetry_model = model(json!({
        "id": "model",
        "name": "Model",
        "api": "telemetry-test",
        "provider": "telemetry-provider",
        "baseUrl": "https://example.test",
        "reasoning": false,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 1000,
        "maxTokens": 100,
    }));
    let request = ProviderRequestOptions {
        telemetry_context: Some(Arc::clone(&telemetry)),
        ..ProviderRequestOptions::default()
    };
    assert!(request
        .telemetry_context
        .as_ref()
        .is_some_and(|value| Arc::ptr_eq(value, &telemetry)));

    let options = SimpleStreamOptions {
        stream: StreamOptions {
            request,
            ..StreamOptions::default()
        },
        ..SimpleStreamOptions::default()
    };
    let base = build_base_options(
        &telemetry_model,
        &context(json!({ "messages": [] })),
        Some(&options),
        None,
    );

    assert!(base
        .request
        .telemetry_context
        .as_ref()
        .is_some_and(|value| Arc::ptr_eq(value, &telemetry)));
}
