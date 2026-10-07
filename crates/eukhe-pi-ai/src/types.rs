//! Runtime-only part of `types.ts`: request options with their callbacks
//! (abort signal, fetch, `onPayload`, `onResponse`, `onProviderStreamEvent`),
//! the telemetry context contract, and the stream/images/classifier function
//! shapes. The serializable data types live in [`eukhe_types::pi_ai`] and are
//! re-exported here, so `eukhe_pi_ai::types` is the whole TS `types.ts`.
//!
//! TS `ApiOptionsMap`/`ApiStreamOptions<TApi>` are type-level only; per-API
//! option fields travel in [`ProviderStreamOptions::extra`] and each API
//! module reads its own keys.

use std::fmt;
use std::future::Future;
use std::sync::Arc;

use eukhe_chord::context::AbortSignal;
use futures::future::BoxFuture;
use serde::{Deserialize, Serialize};

pub use eukhe_types::pi_ai::*;

use crate::utils::diagnostics::Thrown;
use crate::utils::event_stream::AssistantMessageEventStream;

// ---------------------------------------------------------------------------
// Telemetry (the `@earendil-works/pi-telemetry` contract pi-ai passes through)
// ---------------------------------------------------------------------------

/// TS `AttributeValue`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum AttributeValue {
    String(String),
    Number(#[serde(serialize_with = "js_number::serialize")] f64),
    Bool(bool),
    Strings(Vec<String>),
    Numbers(Vec<f64>),
    Bools(Vec<bool>),
}

/// TS `SpanAttributes`; an `undefined` attribute is an absent key.
pub type SpanAttributes = IndexMap<String, AttributeValue>;

/// TS `SpanOptions`.
#[derive(Debug, Clone, PartialEq)]
pub struct SpanOptions {
    pub name: String,
    pub attributes: Option<SpanAttributes>,
}

/// Error details of a failed span.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpanError {
    pub name: String,
    pub message: String,
}

/// TS `SpanStatus`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SpanStatus {
    Ok,
    Error { error: Option<SpanError> },
}

/// Body of a span: runs with the started span and settles the span when its
/// future completes.
pub type SpanCallback = Box<dyn FnOnce(Arc<dyn TelemetrySpan>) -> BoxFuture<'static, ()> + Send>;

/// Parent context for telemetry produced by a logical request (TS
/// `TelemetryContext`).
///
/// Implementations start a child span named by `options`, run `callback` with
/// it, end the span when the callback's future completes, and resolve after
/// that. Results flow out of the callback through captured state; see
/// [`start_span`] for the typed form of TS `startSpan<T>`.
pub trait TelemetryContext: Send + Sync {
    /// Start a span, run `callback` inside it, and end it afterwards.
    fn start_span(&self, options: SpanOptions, callback: SpanCallback) -> BoxFuture<'static, ()>;
}

/// An active span (TS `TelemetrySpan`). Implementations record events,
/// attributes, and the final status on the span they represent, and act as
/// the parent context for nested spans.
pub trait TelemetrySpan: TelemetryContext {
    /// Record a named event.
    fn add_event(&self, name: &str, attributes: Option<SpanAttributes>);
    /// Merge attributes into the span.
    fn set_attributes(&self, attributes: SpanAttributes);
    /// Set the span status.
    fn set_status(&self, status: SpanStatus);
}

/// TS `telemetryContext.startSpan<T>(options, callback)`: run `callback` in a
/// child span and return its result.
///
/// # Errors
///
/// Returns `Err(())` when the telemetry implementation dropped the callback
/// without running it to completion.
pub async fn start_span<T, F, Fut>(
    context: &dyn TelemetryContext,
    options: SpanOptions,
    callback: F,
) -> Result<T, SpanCallbackDropped>
where
    T: Send + 'static,
    F: FnOnce(Arc<dyn TelemetrySpan>) -> Fut + Send + 'static,
    Fut: Future<Output = T> + Send + 'static,
{
    let (sender, receiver) = tokio::sync::oneshot::channel();
    context
        .start_span(
            options,
            Box::new(move |span| {
                Box::pin(async move {
                    // The receiver lives until `start_span` returns below.
                    let _ = sender.send(callback(span).await);
                })
            }),
        )
        .await;
    receiver.await.map_err(|_| SpanCallbackDropped)
}

/// The telemetry implementation did not run the span callback to completion.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[error("telemetry span callback did not complete")]
pub struct SpanCallbackDropped;

// ---------------------------------------------------------------------------
// Callbacks
// ---------------------------------------------------------------------------

/// TS `FetchFunction = typeof globalThis.fetch`: performs one HTTP request.
/// Providers that cannot inject a custom implementation may reject it.
pub type FetchFunction = Arc<
    dyn Fn(reqwest::Request) -> BoxFuture<'static, Result<reqwest::Response, Thrown>> + Send + Sync,
>;

/// Inspect or replace a provider payload before sending; `Ok(None)` keeps it.
pub type OnPayload<M> = Arc<
    dyn for<'a> Fn(JsonValue, &'a M) -> BoxFuture<'a, Result<Option<JsonValue>, Thrown>>
        + Send
        + Sync,
>;

/// Called after an HTTP response is received (for streams: before its body is consumed).
pub type OnResponse<M> =
    Arc<dyn for<'a> Fn(ProviderResponse, &'a M) -> BoxFuture<'a, Result<(), Thrown>> + Send + Sync>;

/// Observes each parsed provider stream event before Pi normalization. Event
/// data is adapter-owned and read-only; adapter support is explicit.
pub type OnProviderStreamEvent = Arc<
    dyn for<'a> Fn(&'a JsonValue, &'a Model) -> BoxFuture<'a, Result<(), Thrown>> + Send + Sync,
>;

// ---------------------------------------------------------------------------
// Options
// ---------------------------------------------------------------------------

/// Authentication, HTTP transport, and lifecycle callbacks shared by provider requests.
pub struct ProviderRequestOptions<M = Model> {
    pub signal: Option<AbortSignal>,
    /// Explicit parent context for telemetry produced by this logical request.
    pub telemetry_context: Option<Arc<dyn TelemetryContext>>,
    pub api_key: Option<String>,
    /// Optional fetch implementation for provider HTTP requests. Does not
    /// affect WebSocket transports.
    pub fetch: Option<FetchFunction>,
    /// Provider-scoped environment values; they take precedence over the
    /// process environment for provider configuration.
    pub env: Option<ProviderEnv>,
    /// Inspect or replace provider payloads before sending.
    pub on_payload: Option<OnPayload<M>>,
    /// Called after an HTTP response is received.
    pub on_response: Option<OnResponse<M>>,
    /// Custom HTTP headers merged over provider defaults; `None` values
    /// suppress a default header of the same name.
    pub headers: Option<ProviderHeaders>,
    /// HTTP request timeout in milliseconds for providers/SDKs that support it.
    pub timeout_ms: Option<f64>,
    /// Maximum client-side retry attempts for providers/SDKs that support it.
    pub max_retries: Option<u32>,
    /// Maximum delay in milliseconds to wait for a server-requested retry.
    /// Default: 60000. `0` disables the cap.
    pub max_retry_delay_ms: Option<f64>,
}

impl<M> Default for ProviderRequestOptions<M> {
    fn default() -> Self {
        Self {
            signal: None,
            telemetry_context: None,
            api_key: None,
            fetch: None,
            env: None,
            on_payload: None,
            on_response: None,
            headers: None,
            timeout_ms: None,
            max_retries: None,
            max_retry_delay_ms: None,
        }
    }
}

impl<M> Clone for ProviderRequestOptions<M> {
    fn clone(&self) -> Self {
        Self {
            signal: self.signal.clone(),
            telemetry_context: self.telemetry_context.clone(),
            api_key: self.api_key.clone(),
            fetch: self.fetch.clone(),
            env: self.env.clone(),
            on_payload: self.on_payload.clone(),
            on_response: self.on_response.clone(),
            headers: self.headers.clone(),
            timeout_ms: self.timeout_ms,
            max_retries: self.max_retries,
            max_retry_delay_ms: self.max_retry_delay_ms,
        }
    }
}

impl<M> fmt::Debug for ProviderRequestOptions<M> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ProviderRequestOptions")
            .field("signal", &self.signal)
            .field(
                "telemetry_context",
                &self.telemetry_context.as_ref().map(|_| "TelemetryContext"),
            )
            .field("api_key", &self.api_key.as_ref().map(|_| "<redacted>"))
            .field("fetch", &self.fetch.as_ref().map(|_| "FetchFunction"))
            .field("env", &self.env)
            .field("on_payload", &self.on_payload.as_ref().map(|_| "OnPayload"))
            .field(
                "on_response",
                &self.on_response.as_ref().map(|_| "OnResponse"),
            )
            .field("headers", &self.headers)
            .field("timeout_ms", &self.timeout_ms)
            .field("max_retries", &self.max_retries)
            .field("max_retry_delay_ms", &self.max_retry_delay_ms)
            .finish()
    }
}

/// Options shared by every chat stream request.
#[derive(Clone, Default)]
pub struct StreamOptions {
    pub request: ProviderRequestOptions<Model>,
    /// Observer for each parsed provider stream event before Pi normalization.
    pub on_provider_stream_event: Option<OnProviderStreamEvent>,
    pub temperature: Option<f64>,
    /// Arbitrary sampling parameters merged into the request body after the
    /// named fields (so these keys override them) and over
    /// `Model::sampling_params` per key. Only OpenAI-compatible adapters apply it.
    pub sampling_params: Option<SamplingParams>,
    pub max_tokens: Option<u64>,
    /// Preferred transport for providers that support several.
    pub transport: Option<Transport>,
    /// Prompt cache retention preference. Default: short.
    pub cache_retention: Option<CacheRetention>,
    /// Session identifier for providers with session-based caching or routing.
    pub session_id: Option<String>,
    /// WebSocket connect (handshake) timeout in milliseconds.
    pub websocket_connect_timeout_ms: Option<f64>,
    /// Metadata to include in API requests; providers extract what they understand.
    pub metadata: Option<JsonObject>,
    /// eukhe addition: `OpenAI` service tier requested for this call.
    pub service_tier: Option<ServiceTier>,
}

impl fmt::Debug for StreamOptions {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("StreamOptions")
            .field("request", &self.request)
            .field(
                "on_provider_stream_event",
                &self
                    .on_provider_stream_event
                    .as_ref()
                    .map(|_| "OnProviderStreamEvent"),
            )
            .field("temperature", &self.temperature)
            .field("sampling_params", &self.sampling_params)
            .field("max_tokens", &self.max_tokens)
            .field("transport", &self.transport)
            .field("cache_retention", &self.cache_retention)
            .field("session_id", &self.session_id)
            .field(
                "websocket_connect_timeout_ms",
                &self.websocket_connect_timeout_ms,
            )
            .field("metadata", &self.metadata)
            .field("service_tier", &self.service_tier)
            .finish()
    }
}

/// TS `ProviderStreamOptions = StreamOptions & Record<string, unknown>`: the
/// generic options plus API-specific keys (`AnthropicOptions` fields and the
/// like), which each API module reads from `extra`.
#[derive(Debug, Clone, Default)]
pub struct ProviderStreamOptions {
    pub stream: StreamOptions,
    pub extra: JsonObject,
}

/// Options of a deferred-response status fetch.
#[derive(Debug, Clone, Default)]
pub struct DeferredFetchOptions {
    pub request: ProviderRequestOptions<Model>,
    /// Maximum provider long-poll duration in milliseconds. Default 0: one status check.
    pub wait: Option<f64>,
}

/// Request options for best-effort deferred-response cancellation.
pub type DeferredCancelOptions = ProviderRequestOptions<Model>;

/// Options of a classifier request.
#[derive(Debug, Clone, Default)]
pub struct ClassifierOptions {
    pub request: ProviderRequestOptions<ClassifierModel>,
    /// Divides the answer logits by this value before normalization. Must be
    /// positive; APIs that cannot apply it ignore it.
    pub temperature: Option<f64>,
}

/// Options of an image-generation request.
#[derive(Debug, Clone, Default)]
pub struct ImagesOptions {
    pub request: ProviderRequestOptions<ImageModel>,
    /// Metadata to include in API requests; providers extract what they understand.
    pub metadata: Option<JsonObject>,
}

/// TS `ProviderImagesOptions = ImagesOptions & Record<string, unknown>`.
#[derive(Debug, Clone, Default)]
pub struct ProviderImagesOptions {
    pub images: ImagesOptions,
    pub extra: JsonObject,
}

/// Deferred-processing window of a [`DeferredRequest`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum DeferredWindow {
    #[serde(rename = "15m")]
    Minutes15,
    #[serde(rename = "1h")]
    Hours1,
    #[serde(rename = "24h")]
    Hours24,
}

impl DeferredWindow {
    /// The wire string.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Minutes15 => "15m",
            Self::Hours1 => "1h",
            Self::Hours24 => "24h",
        }
    }
}

/// TS `deferred?: boolean | { window?: "15m" | "1h" | "24h" }`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeferredRequest {
    /// `true` or `false`.
    Flag(bool),
    /// `{ window? }`.
    Window(Option<DeferredWindow>),
}

/// Unified options with reasoning, passed to `streamSimple()`/`completeSimple()`.
#[derive(Debug, Clone, Default)]
pub struct SimpleStreamOptions {
    pub stream: StreamOptions,
    /// Provider-neutral tool selection. When `None`, adapters use provider-specific behavior.
    pub tool_choice: Option<ToolChoice>,
    pub reasoning: Option<ThinkingLevel>,
    /// Ask a capable provider to return a durable handle and continue asynchronously.
    pub deferred: Option<DeferredRequest>,
    /// Custom token budgets for thinking levels (token-based providers only).
    pub thinking_budgets: Option<ThinkingBudgets>,
}

// ---------------------------------------------------------------------------
// Function shapes
// ---------------------------------------------------------------------------

/// TS `StreamFunction`: receives a normalized transcript (prompt and tools
/// in the leading system message) and returns the event stream. Request,
/// model, and runtime failures are encoded in the stream as an `error` event
/// with `stopReason` `error` or `aborted`.
pub type StreamFunction<O = StreamOptions> =
    Arc<dyn Fn(&Model, TranscriptContext, Option<O>) -> AssistantMessageEventStream + Send + Sync>;

/// TS `ImagesFunction`.
pub type ImagesFunction<O = ImagesOptions> = Arc<
    dyn Fn(
            &ImageModel,
            ImagesContext,
            Option<O>,
        ) -> BoxFuture<'static, Result<AssistantImages, Thrown>>
        + Send
        + Sync,
>;

/// TS `ClassifierFunction`.
pub type ClassifierFunction<O = ClassifierOptions> = Arc<
    dyn Fn(
            &ClassifierModel,
            ClassifierContext,
            Option<O>,
        ) -> BoxFuture<'static, Result<ClassifierResult, Thrown>>
        + Send
        + Sync,
>;
