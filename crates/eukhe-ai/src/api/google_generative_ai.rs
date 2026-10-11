//! The `google-generative-ai` wire API (Gemini API via `@google/genai`).
//! Port of `api/google-generative-ai.ts`.
//!
//! API-specific stream options in [`ProviderStreamOptions::extra`] (TS
//! `GoogleOptions`): `toolChoice` (`"auto" | "none" | "any"`) and `thinking`
//! (`{ enabled, budgetTokens?, level? }`).

#[cfg(test)]
pub(crate) mod tests;

use std::sync::Arc;

use eukhe_types::pi_ai::{Model, ProviderHeaders, ThinkingBudgets, TranscriptContext};

use super::google_shared::genai::{GoogleGenAi, GoogleGenAiOptions, HttpOptions};
use super::google_shared::{
    budget_for, custom_budget, pi_headers, run_google_stream, simple_request_options,
    GoogleApiKind, GoogleRequestOptions, ResolvedGoogleThinkingLevel,
};
use super::lazy::lazy_stream;
use super::ProviderStreams;
use crate::types::{ProviderStreamOptions, SimpleStreamOptions};
use crate::utils::diagnostics::{ErrorObject, Thrown};
use crate::utils::event_stream::AssistantMessageEventStream;

/// The module's stream contract.
#[must_use]
pub fn streams() -> ProviderStreams {
    ProviderStreams {
        stream: Arc::new(stream),
        stream_simple: Arc::new(stream_simple),
        fetch_deferred: None,
        cancel_deferred: None,
    }
}

/// TS `stream`.
#[must_use]
pub fn stream(
    model: &Model,
    context: &TranscriptContext,
    options: ProviderStreamOptions,
) -> AssistantMessageEventStream {
    stream_with(
        model,
        context,
        GoogleRequestOptions::from_provider_options(options),
    )
}

fn stream_with(
    model: &Model,
    context: &TranscriptContext,
    options: Result<GoogleRequestOptions, Thrown>,
) -> AssistantMessageEventStream {
    run_google_stream(
        GoogleApiKind::GenerativeAi,
        model,
        context,
        options,
        Box::new(|model, options| {
            let api_key = options
                .stream
                .request
                .api_key
                .clone()
                .filter(|key| !key.is_empty())
                .ok_or_else(|| {
                    ErrorObject::new(format!("No API key for provider: {}", model.provider))
                        .thrown()
                })?;
            create_client(model, api_key, options.stream.request.headers.as_ref())
        }),
    )
}

/// TS `streamSimple`. Its synchronous throws (no API key, an unsupported
/// thinking-level mapping) end the returned stream with an error event, as
/// the lazy API wrapper reports them.
#[must_use]
pub fn stream_simple(
    model: &Model,
    context: &TranscriptContext,
    options: SimpleStreamOptions,
) -> AssistantMessageEventStream {
    let api_key = options
        .stream
        .request
        .api_key
        .clone()
        .filter(|key| !key.is_empty());
    let Some(api_key) = api_key else {
        let error =
            ErrorObject::new(format!("No API key for provider: {}", model.provider)).thrown();
        return lazy_stream(model, async move { Err(error) });
    };
    match simple_request_options(model, context, options, Some(&api_key), get_google_budget) {
        Ok(options) => stream_with(model, context, Ok(options)),
        Err(error) => lazy_stream(model, async move { Err(error) }),
    }
}

/// TS `createClient(model, apiKey, headers)`.
fn create_client(
    model: &Model,
    api_key: String,
    options_headers: Option<&ProviderHeaders>,
) -> Result<GoogleGenAi, Thrown> {
    let mut http_options = HttpOptions::default();
    if !model.base_url.is_empty() {
        http_options.base_url = Some(model.base_url.clone());
        // baseUrl already includes the version path; don't append one.
        http_options.api_version = Some(String::new());
    }
    http_options.headers = pi_headers(model, options_headers);
    GoogleGenAi::new(GoogleGenAiOptions {
        api_key: Some(api_key),
        http_options: (!http_options.is_empty()).then_some(http_options),
        ..GoogleGenAiOptions::default()
    })
}

/// TS `getGoogleBudget` of `google-generative-ai.ts`.
fn get_google_budget(
    model: &Model,
    level: ResolvedGoogleThinkingLevel,
    custom_budgets: Option<&ThinkingBudgets>,
) -> i64 {
    if let Some(budget) = custom_budget(custom_budgets, level) {
        return budget;
    }
    let budgets: [i64; 4] = if model.id.contains("2.5-pro") {
        [128, 2048, 8192, 32768]
    } else if model.id.contains("2.5-flash-lite") {
        [512, 2048, 8192, 24576]
    } else if model.id.contains("2.5-flash") {
        [128, 2048, 8192, 24576]
    } else {
        return -1;
    };
    budget_for(budgets, level)
}
