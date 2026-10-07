//! Deprecated per-API stream functions of the old global API. Port of
//! `legacy-api-aliases.ts`. Each streams through the lazily bound built-in
//! API; API-specific options travel in `ProviderStreamOptions::extra`.

use std::sync::LazyLock;

use eukhe_types::pi_ai::{Model, TranscriptContext};

use crate::api::builtin::{
    anthropic_messages_api, azure_openai_responses_api, google_generative_ai_api,
    google_vertex_api, mistral_conversations_api, openai_codex_responses_api,
    openai_completions_api, openai_responses_api,
};
use crate::api::ProviderStreams;
use crate::types::{ProviderStreamOptions, SimpleStreamOptions};
use crate::utils::event_stream::AssistantMessageEventStream;

static ANTHROPIC_MESSAGES_STREAMS: LazyLock<ProviderStreams> =
    LazyLock::new(anthropic_messages_api);
static AZURE_OPENAI_RESPONSES_STREAMS: LazyLock<ProviderStreams> =
    LazyLock::new(azure_openai_responses_api);
static GOOGLE_GENERATIVE_AI_STREAMS: LazyLock<ProviderStreams> =
    LazyLock::new(google_generative_ai_api);
static GOOGLE_VERTEX_STREAMS: LazyLock<ProviderStreams> = LazyLock::new(google_vertex_api);
static MISTRAL_CONVERSATIONS_STREAMS: LazyLock<ProviderStreams> =
    LazyLock::new(mistral_conversations_api);
static OPENAI_CODEX_RESPONSES_STREAMS: LazyLock<ProviderStreams> =
    LazyLock::new(openai_codex_responses_api);
static OPENAI_COMPLETIONS_STREAMS: LazyLock<ProviderStreams> =
    LazyLock::new(openai_completions_api);
static OPENAI_RESPONSES_STREAMS: LazyLock<ProviderStreams> = LazyLock::new(openai_responses_api);

/// Deprecated: TS `streamAnthropic`; use `api::builtin::anthropic_messages_api()`.
#[must_use]
pub fn stream_anthropic(
    model: &Model,
    context: &TranscriptContext,
    options: ProviderStreamOptions,
) -> AssistantMessageEventStream {
    (ANTHROPIC_MESSAGES_STREAMS.stream)(model, context, options)
}

/// Deprecated: TS `streamSimpleAnthropic`; use `api::builtin::anthropic_messages_api()`.
#[must_use]
pub fn stream_simple_anthropic(
    model: &Model,
    context: &TranscriptContext,
    options: SimpleStreamOptions,
) -> AssistantMessageEventStream {
    (ANTHROPIC_MESSAGES_STREAMS.stream_simple)(model, context, options)
}

/// Deprecated: TS `streamAzureOpenAIResponses`; use `api::builtin::azure_openai_responses_api()`.
#[must_use]
pub fn stream_azure_openai_responses(
    model: &Model,
    context: &TranscriptContext,
    options: ProviderStreamOptions,
) -> AssistantMessageEventStream {
    (AZURE_OPENAI_RESPONSES_STREAMS.stream)(model, context, options)
}

/// Deprecated: TS `streamSimpleAzureOpenAIResponses`; use `api::builtin::azure_openai_responses_api()`.
#[must_use]
pub fn stream_simple_azure_openai_responses(
    model: &Model,
    context: &TranscriptContext,
    options: SimpleStreamOptions,
) -> AssistantMessageEventStream {
    (AZURE_OPENAI_RESPONSES_STREAMS.stream_simple)(model, context, options)
}

/// Deprecated: TS `streamGoogle`; use `api::builtin::google_generative_ai_api()`.
#[must_use]
pub fn stream_google(
    model: &Model,
    context: &TranscriptContext,
    options: ProviderStreamOptions,
) -> AssistantMessageEventStream {
    (GOOGLE_GENERATIVE_AI_STREAMS.stream)(model, context, options)
}

/// Deprecated: TS `streamSimpleGoogle`; use `api::builtin::google_generative_ai_api()`.
#[must_use]
pub fn stream_simple_google(
    model: &Model,
    context: &TranscriptContext,
    options: SimpleStreamOptions,
) -> AssistantMessageEventStream {
    (GOOGLE_GENERATIVE_AI_STREAMS.stream_simple)(model, context, options)
}

/// Deprecated: TS `streamGoogleVertex`; use `api::builtin::google_vertex_api()`.
#[must_use]
pub fn stream_google_vertex(
    model: &Model,
    context: &TranscriptContext,
    options: ProviderStreamOptions,
) -> AssistantMessageEventStream {
    (GOOGLE_VERTEX_STREAMS.stream)(model, context, options)
}

/// Deprecated: TS `streamSimpleGoogleVertex`; use `api::builtin::google_vertex_api()`.
#[must_use]
pub fn stream_simple_google_vertex(
    model: &Model,
    context: &TranscriptContext,
    options: SimpleStreamOptions,
) -> AssistantMessageEventStream {
    (GOOGLE_VERTEX_STREAMS.stream_simple)(model, context, options)
}

/// Deprecated: TS `streamMistral`; use `api::builtin::mistral_conversations_api()`.
#[must_use]
pub fn stream_mistral(
    model: &Model,
    context: &TranscriptContext,
    options: ProviderStreamOptions,
) -> AssistantMessageEventStream {
    (MISTRAL_CONVERSATIONS_STREAMS.stream)(model, context, options)
}

/// Deprecated: TS `streamSimpleMistral`; use `api::builtin::mistral_conversations_api()`.
#[must_use]
pub fn stream_simple_mistral(
    model: &Model,
    context: &TranscriptContext,
    options: SimpleStreamOptions,
) -> AssistantMessageEventStream {
    (MISTRAL_CONVERSATIONS_STREAMS.stream_simple)(model, context, options)
}

/// Deprecated: TS `streamOpenAICodexResponses`; use `api::builtin::openai_codex_responses_api()`.
#[must_use]
pub fn stream_openai_codex_responses(
    model: &Model,
    context: &TranscriptContext,
    options: ProviderStreamOptions,
) -> AssistantMessageEventStream {
    (OPENAI_CODEX_RESPONSES_STREAMS.stream)(model, context, options)
}

/// Deprecated: TS `streamSimpleOpenAICodexResponses`; use `api::builtin::openai_codex_responses_api()`.
#[must_use]
pub fn stream_simple_openai_codex_responses(
    model: &Model,
    context: &TranscriptContext,
    options: SimpleStreamOptions,
) -> AssistantMessageEventStream {
    (OPENAI_CODEX_RESPONSES_STREAMS.stream_simple)(model, context, options)
}

/// Deprecated: TS `streamOpenAICompletions`; use `api::builtin::openai_completions_api()`.
#[must_use]
pub fn stream_openai_completions(
    model: &Model,
    context: &TranscriptContext,
    options: ProviderStreamOptions,
) -> AssistantMessageEventStream {
    (OPENAI_COMPLETIONS_STREAMS.stream)(model, context, options)
}

/// Deprecated: TS `streamSimpleOpenAICompletions`; use `api::builtin::openai_completions_api()`.
#[must_use]
pub fn stream_simple_openai_completions(
    model: &Model,
    context: &TranscriptContext,
    options: SimpleStreamOptions,
) -> AssistantMessageEventStream {
    (OPENAI_COMPLETIONS_STREAMS.stream_simple)(model, context, options)
}

/// Deprecated: TS `streamOpenAIResponses`; use `api::builtin::openai_responses_api()`.
#[must_use]
pub fn stream_openai_responses(
    model: &Model,
    context: &TranscriptContext,
    options: ProviderStreamOptions,
) -> AssistantMessageEventStream {
    (OPENAI_RESPONSES_STREAMS.stream)(model, context, options)
}

/// Deprecated: TS `streamSimpleOpenAIResponses`; use `api::builtin::openai_responses_api()`.
#[must_use]
pub fn stream_simple_openai_responses(
    model: &Model,
    context: &TranscriptContext,
    options: SimpleStreamOptions,
) -> AssistantMessageEventStream {
    (OPENAI_RESPONSES_STREAMS.stream_simple)(model, context, options)
}
