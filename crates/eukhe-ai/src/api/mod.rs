//! Wire-API implementations and the contract they implement.
//!
//! # The API-module contract
//!
//! A *wire API* is one request protocol, identified by an API id string:
//! the chat APIs `anthropic-messages`, `openai-completions`,
//! `openai-responses`, `azure-openai-responses`, `openai-codex-responses`,
//! `google-generative-ai`, `google-vertex`, `mistral-conversations`,
//! `bedrock-converse-stream`, and `pi-messages`; the image API
//! `openrouter-images`; and the classifier APIs `typesafe-system-one`,
//! `cloudflare-workers-ai-system-one`, `llama-cpp-classify`, and
//! `openai-decisions`. Every model names its API in `model.api`.
//!
//! Each wire API lives in its own module `api::<id_in_snake_case>` (port of
//! `src/api/<id>.ts`) and exposes one constructor returning the API's
//! capability value:
//!
//! - chat APIs: `pub fn streams() -> ProviderStreams` built from the module's
//!   free functions `stream` and `stream_simple` (TS: the module exports
//!   `stream` and `streamSimple`), plus `fetch_deferred` / `cancel_deferred`
//!   when the API supports deferred responses;
//! - image APIs: `pub fn images() -> ProviderImages` (TS: exports
//!   `generateImages`);
//! - classifier APIs: `pub fn classifier() -> ProviderClassifier` (TS:
//!   exports `classify`).
//!
//! The behavior each function must implement is the TS `StreamFunction`
//! contract:
//!
//! - `stream` / `stream_simple` receive a normalized transcript (the system
//!   prompt and tools live in the leading system message) and return an
//!   [`AssistantMessageEventStream`] synchronously; the request runs on a
//!   spawned task. Once the stream is returned, request, model, and runtime
//!   failures are encoded in the stream: termination with an error produces
//!   an `AssistantMessage` with `stopReason` `"error"` or `"aborted"` and an
//!   `errorMessage`, delivered as an `error` event followed by `end`.
//!   Successful streams emit `start` first and end with `done`.
//! - API-specific stream options (TS `ApiStreamOptions<TApi>`, e.g.
//!   `AnthropicOptions.thinkingEnabled`) arrive in
//!   [`ProviderStreamOptions::extra`] under their TS camelCase names; the
//!   shared options are in [`ProviderStreamOptions::stream`]. Each module
//!   parses the keys it understands and ignores the rest.
//! - `fetch_deferred` resumes a deferred response from its
//!   [`DeferredHandle`] and streams like `stream`; `cancel_deferred` is a
//!   best-effort cancellation that fails with the thrown error.
//! - `generate_images` and `classify` never fail: errors become an
//!   `AssistantImages` / `ClassifierResult` with `stopReason` `"error"` (or
//!   `"aborted"` when the request signal aborted) and an `errorMessage`.
//!
//! # Binding providers to APIs
//!
//! Providers do not link API modules directly. A provider factory binds an
//! API by id through the lazy constructors in [`builtin`] (port of the
//! `src/api/*.lazy.ts` files), e.g. [`builtin::anthropic_messages_api`]. The
//! lazy value resolves the module from the built-in registry tables in
//! [`builtin`] on first use, the Rust counterpart of the TS dynamic
//! `import()`. A module registers itself by adding one entry to the matching
//! table (`BUILTIN_STREAM_APIS`, `BUILTIN_IMAGE_APIS`, or
//! `BUILTIN_CLASSIFIER_APIS`) with its id and constructor. An id without a
//! table entry behaves like a failed import: chat requests end with an error
//! event, image and classifier requests return an error result. Deferred
//! capabilities of a chat API are declared on its lazy constructor (TS
//! `lazyApi(load, { fetchDeferred, cancelDeferred })`) so providers know them
//! before the module loads.

pub mod anthropic_messages;
pub mod azure_openai_config;
pub mod azure_openai_responses;
pub mod bedrock_converse_stream;
pub mod builtin;
pub mod cache_breakpoints;
pub(crate) mod classifier_shared;
pub mod cloudflare;
pub mod cloudflare_ai_binding;
pub mod cloudflare_workers_ai_system_one;
pub mod constrained_sampling;
pub mod github_copilot_headers;
pub mod google_generative_ai;
pub mod google_shared;
pub mod google_vertex;
pub mod lazy;
pub mod llama_cpp_classify;
pub mod mistral_conversations;
pub mod openai_codex_responses;
pub mod openai_completions;
pub mod openai_decisions;
pub mod openai_prompt_cache;
pub mod openai_responses;
pub mod openai_responses_shared;
pub(crate) mod openai_sdk;
pub mod openrouter_images;
pub mod pi_messages;
pub mod simple_options;
pub(crate) mod system_one_shared;
pub mod transform_messages;
pub mod typesafe_system_one;

use std::fmt;
use std::sync::Arc;

use eukhe_types::pi_ai::{
    AssistantImages, ClassifierContext, ClassifierModel, ClassifierResult, DeferredHandle,
    ImageModel, ImagesContext, Model, TranscriptContext,
};
use futures::future::BoxFuture;

use crate::types::{
    ClassifierOptions, DeferredCancelOptions, DeferredFetchOptions, ImagesOptions,
    ProviderStreamOptions, SimpleStreamOptions,
};
use crate::utils::diagnostics::Thrown;
use crate::utils::event_stream::AssistantMessageEventStream;

/// Streams a chat request with full (API-specific) options: TS
/// `ProviderStreams.stream`.
pub type StreamFn = Arc<
    dyn Fn(&Model, &TranscriptContext, ProviderStreamOptions) -> AssistantMessageEventStream
        + Send
        + Sync,
>;

/// Streams a chat request with provider-neutral options: TS
/// `ProviderStreams.streamSimple`.
pub type StreamSimpleFn = Arc<
    dyn Fn(&Model, &TranscriptContext, SimpleStreamOptions) -> AssistantMessageEventStream
        + Send
        + Sync,
>;

/// Resumes a deferred response: TS `ProviderStreams.fetchDeferred`.
pub type FetchDeferredFn = Arc<
    dyn Fn(&Model, &DeferredHandle, DeferredFetchOptions) -> AssistantMessageEventStream
        + Send
        + Sync,
>;

/// Best-effort deferred-response cancellation: TS
/// `ProviderStreams.cancelDeferred`.
pub type CancelDeferredFn = Arc<
    dyn Fn(&Model, &DeferredHandle, DeferredCancelOptions) -> BoxFuture<'static, Result<(), Thrown>>
        + Send
        + Sync,
>;

/// Generates images; never fails: TS `ProviderImages.generateImages`.
pub type GenerateImagesFn = Arc<
    dyn Fn(&ImageModel, &ImagesContext, ImagesOptions) -> BoxFuture<'static, AssistantImages>
        + Send
        + Sync,
>;

/// Classifies structured state; never fails: TS
/// `ProviderClassifier.classify`.
pub type ClassifyFn = Arc<
    dyn Fn(
            &ClassifierModel,
            &ClassifierContext,
            ClassifierOptions,
        ) -> BoxFuture<'static, ClassifierResult>
        + Send
        + Sync,
>;

/// The uniform stream contract of a chat API module: TS `ProviderStreams`.
/// Values are cheap to clone and freely wrapped (see
/// `providers::cloudflare_stream`).
#[derive(Clone)]
pub struct ProviderStreams {
    pub stream: StreamFn,
    pub stream_simple: StreamSimpleFn,
    /// Present when the API can resume deferred responses.
    pub fetch_deferred: Option<FetchDeferredFn>,
    /// Present when the API can cancel deferred responses.
    pub cancel_deferred: Option<CancelDeferredFn>,
}

impl fmt::Debug for ProviderStreams {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ProviderStreams")
            .field("fetch_deferred", &self.fetch_deferred.is_some())
            .field("cancel_deferred", &self.cancel_deferred.is_some())
            .finish_non_exhaustive()
    }
}

/// The uniform contract of an image-generation API module: TS
/// `ProviderImages`.
#[derive(Clone)]
pub struct ProviderImages {
    pub generate_images: GenerateImagesFn,
}

impl fmt::Debug for ProviderImages {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ProviderImages")
            .finish_non_exhaustive()
    }
}

/// The uniform contract of a classifier API module: TS
/// `ProviderClassifier`.
#[derive(Clone)]
pub struct ProviderClassifier {
    pub classify: ClassifyFn,
}

impl fmt::Debug for ProviderClassifier {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ProviderClassifier")
            .finish_non_exhaustive()
    }
}
