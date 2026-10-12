//! Deprecated per-API stream functions of the old global API. Port of
//! `legacy-api-aliases.ts`. Each streams through the lazily bound built-in
//! API; API-specific options travel in `ProviderStreamOptions::extra`.

use std::sync::LazyLock;

use eukhe_types::pi_ai::{Model, TranscriptContext};

use crate::api::builtin::{
    anthropic_messages_api, mistral_conversations_api, openai_responses_api,
};
use crate::api::ProviderStreams;
use crate::types::ProviderStreamOptions;
use crate::utils::event_stream::AssistantMessageEventStream;

static ANTHROPIC_MESSAGES_STREAMS: LazyLock<ProviderStreams> =
    LazyLock::new(anthropic_messages_api);
static MISTRAL_CONVERSATIONS_STREAMS: LazyLock<ProviderStreams> =
    LazyLock::new(mistral_conversations_api);
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

/// Deprecated: TS `streamMistral`; use `api::builtin::mistral_conversations_api()`.
#[must_use]
pub fn stream_mistral(
    model: &Model,
    context: &TranscriptContext,
    options: ProviderStreamOptions,
) -> AssistantMessageEventStream {
    (MISTRAL_CONVERSATIONS_STREAMS.stream)(model, context, options)
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
