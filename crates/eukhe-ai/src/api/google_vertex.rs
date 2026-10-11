//! The `google-vertex` wire API (Vertex AI via `@google/genai`).
//! Port of `api/google-vertex.ts`.
//!
//! API-specific stream options in [`ProviderStreamOptions::extra`] (TS
//! `GoogleVertexOptions`): `toolChoice`, `thinking`, `project`, `location`.

#[cfg(test)]
mod tests;

use std::sync::{Arc, LazyLock};

use eukhe_types::pi_ai::{Model, ProviderEnv, ProviderHeaders, ThinkingBudgets, TranscriptContext};
use regex::Regex;

use super::google_shared::genai::{
    GoogleAuthOptions, GoogleGenAi, GoogleGenAiOptions, HttpOptions, ResourceScope,
};
use super::google_shared::{
    budget_for, custom_budget, pi_headers, run_google_stream, simple_request_options,
    GoogleApiKind, GoogleRequestOptions, ResolvedGoogleThinkingLevel,
};
use super::lazy::lazy_stream;
use super::ProviderStreams;
use crate::types::{ProviderStreamOptions, SimpleStreamOptions};
use crate::utils::diagnostics::{ErrorObject, Thrown};
use crate::utils::event_stream::AssistantMessageEventStream;
use crate::utils::provider_env::get_provider_env_value;

const API_VERSION: &str = "v1";
const GCP_VERTEX_CREDENTIALS_MARKER: &str = "gcp-vertex-credentials";

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
        GoogleApiKind::Vertex,
        model,
        context,
        options,
        Box::new(|model, options| {
            let headers = options.stream.request.headers.as_ref();
            // A Vertex API key when provided, else ADC with project and location.
            match resolve_api_key(options) {
                Some(api_key) => create_client_with_api_key(model, api_key, headers),
                None => create_client(
                    model,
                    resolve_project(options)?,
                    resolve_location(options)?,
                    headers,
                    options.stream.request.env.as_ref(),
                ),
            }
        }),
    )
}

/// TS `streamSimple`. A synchronous throw (an unsupported thinking-level
/// mapping) ends the returned stream with an error event, as the lazy API
/// wrapper reports it.
#[must_use]
pub fn stream_simple(
    model: &Model,
    context: &TranscriptContext,
    options: SimpleStreamOptions,
) -> AssistantMessageEventStream {
    match simple_request_options(model, context, options, None, get_google_budget) {
        Ok(options) => stream_with(model, context, Ok(options)),
        Err(error) => lazy_stream(model, async move { Err(error) }),
    }
}

/// TS `createClient(model, project, location, headers, env)` (ADC).
fn create_client(
    model: &Model,
    project: String,
    location: String,
    options_headers: Option<&ProviderHeaders>,
    env: Option<&ProviderEnv>,
) -> Result<GoogleGenAi, Thrown> {
    GoogleGenAi::new(GoogleGenAiOptions {
        vertexai: true,
        project: Some(project),
        location: Some(location),
        api_version: Some(API_VERSION.to_owned()),
        google_auth_options: build_google_auth_options(env),
        http_options: build_http_options(model, options_headers),
        ..GoogleGenAiOptions::default()
    })
}

/// TS `createClientWithApiKey(model, apiKey, headers)` (Vertex express mode).
fn create_client_with_api_key(
    model: &Model,
    api_key: String,
    options_headers: Option<&ProviderHeaders>,
) -> Result<GoogleGenAi, Thrown> {
    GoogleGenAi::new(GoogleGenAiOptions {
        vertexai: true,
        api_key: Some(api_key),
        api_version: Some(API_VERSION.to_owned()),
        http_options: build_http_options(model, options_headers),
        ..GoogleGenAiOptions::default()
    })
}

fn build_http_options(
    model: &Model,
    options_headers: Option<&ProviderHeaders>,
) -> Option<HttpOptions> {
    let mut http_options = HttpOptions::default();
    if let Some(base_url) = resolve_custom_base_url(&model.base_url) {
        http_options.base_url_resource_scope = Some(ResourceScope::Collection);
        if base_url_includes_api_version(&base_url) {
            http_options.api_version = Some(String::new());
        }
        http_options.base_url = Some(base_url);
    }
    http_options.headers = pi_headers(model, options_headers);
    (!http_options.is_empty()).then_some(http_options)
}

/// A model base URL usable as-is: generated `{location}` templates are not.
fn resolve_custom_base_url(base_url: &str) -> Option<String> {
    let trimmed = base_url.trim();
    (!trimmed.is_empty() && !trimmed.contains("{location}")).then(|| trimmed.to_owned())
}

static API_VERSION_SEGMENT: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"^v\d+(?:beta\d*)?$").unwrap_or_else(|error| panic!("{error}")));
static API_VERSION_IN_TEXT: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"(?:^|/)v\d+(?:beta\d*)?(?:/|$)").unwrap_or_else(|error| panic!("{error}"))
});

fn base_url_includes_api_version(base_url: &str) -> bool {
    match url::Url::parse(base_url) {
        Ok(url) => url
            .path()
            .split('/')
            .any(|part| API_VERSION_SEGMENT.is_match(part)),
        Err(_) => API_VERSION_IN_TEXT.is_match(base_url),
    }
}

fn build_google_auth_options(env: Option<&ProviderEnv>) -> Option<GoogleAuthOptions> {
    get_provider_env_value("GOOGLE_APPLICATION_CREDENTIALS", env)
        .filter(|key_filename| !key_filename.is_empty())
        .map(|key_filename| GoogleAuthOptions { key_filename })
}

/// The explicit API key, unless it is empty, the ADC marker, or a
/// `<placeholder>`.
fn resolve_api_key(options: &GoogleRequestOptions) -> Option<String> {
    let api_key = options.stream.request.api_key.as_deref()?.trim();
    if api_key.is_empty()
        || api_key == GCP_VERTEX_CREDENTIALS_MARKER
        || is_placeholder_api_key(api_key)
    {
        return None;
    }
    Some(api_key.to_owned())
}

/// `/^<[^>]+>$/`.
fn is_placeholder_api_key(api_key: &str) -> bool {
    api_key
        .strip_prefix('<')
        .and_then(|rest| rest.strip_suffix('>'))
        .is_some_and(|inner| !inner.is_empty() && !inner.contains('>'))
}

fn resolve_project(options: &GoogleRequestOptions) -> Result<String, Thrown> {
    let env = options.stream.request.env.as_ref();
    options
        .project
        .clone()
        .filter(|project| !project.is_empty())
        .or_else(|| get_provider_env_value("GOOGLE_CLOUD_PROJECT", env).filter(|p| !p.is_empty()))
        .or_else(|| get_provider_env_value("GCLOUD_PROJECT", env).filter(|p| !p.is_empty()))
        .ok_or_else(|| {
            ErrorObject::new(
                "Vertex AI requires a project ID. Set GOOGLE_CLOUD_PROJECT/GCLOUD_PROJECT or pass project in options.",
            )
            .thrown()
        })
}

fn resolve_location(options: &GoogleRequestOptions) -> Result<String, Thrown> {
    options
        .location
        .clone()
        .filter(|location| !location.is_empty())
        .or_else(|| {
            get_provider_env_value("GOOGLE_CLOUD_LOCATION", options.stream.request.env.as_ref())
                .filter(|location| !location.is_empty())
        })
        .ok_or_else(|| {
            ErrorObject::new(
                "Vertex AI requires a location. Set GOOGLE_CLOUD_LOCATION or pass location in options.",
            )
            .thrown()
        })
}

/// TS `getGoogleBudget` of `google-vertex.ts` (no `2.5-flash-lite` table).
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
    } else if model.id.contains("2.5-flash") {
        [128, 2048, 8192, 24576]
    } else {
        return -1;
    };
    budget_for(budgets, level)
}
