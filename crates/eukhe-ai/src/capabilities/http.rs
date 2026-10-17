//! The JSON exchange every capability dialect shares: headers merged from
//! the dialect's defaults, the model, and the request; a fresh timeout per
//! attempt; provider retries; the `onPayload`/`onResponse` hooks.

use eukhe_types::pi_ai::{IndexMap, JsonValue, ProviderHeaders};

use crate::api::classifier_shared::{error, fetch_json};
use crate::types::{Model, ProviderRequestOptions};
use crate::utils::diagnostics::Thrown;
use crate::utils::headers::provider_headers_to_record;
use crate::utils::js::json_stringify;
use crate::utils::provider_retry::{retry_provider_request, ProviderRetryOptions};

/// What a capability request sends.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Body {
    /// A `GET` without a body.
    Get,
    /// A `POST` of this JSON value.
    Post(JsonValue),
}

/// One capability request: a label for errors, the absolute URL, and the
/// dialect's default headers (auth included).
#[derive(Debug, Clone)]
pub(crate) struct Call<'a> {
    /// Names the provider in error messages (`"<label> returned 404"`).
    pub(crate) label: &'a str,
    pub(crate) url: String,
    pub(crate) defaults: ProviderHeaders,
    pub(crate) body: Body,
}

/// The base URL without trailing slashes.
pub(crate) fn trimmed(base_url: &str) -> &str {
    base_url.trim_end_matches('/')
}

/// The OpenAI-style versioned root of `base_url`: the base URL when it
/// ends with `/v1`, else the base URL with `/v1` appended.
pub(crate) fn v1_root(base_url: &str) -> String {
    let base = trimmed(base_url);
    if base.ends_with("/v1") {
        base.to_owned()
    } else {
        format!("{base}/v1")
    }
}

/// The unversioned root of `base_url`: the base URL without a trailing
/// `/v1`.
pub(crate) fn unversioned_root(base_url: &str) -> &str {
    let base = trimmed(base_url);
    base.strip_suffix("/v1").unwrap_or(base)
}

/// The resolved API key, or the error that names the unconfigured
/// provider.
pub(crate) fn api_key<'a>(
    model: &Model,
    options: &'a ProviderRequestOptions,
) -> Result<&'a str, Thrown> {
    options
        .api_key
        .as_deref()
        .filter(|key| !key.is_empty())
        .ok_or_else(|| error(format!("No API key for provider: {}", model.provider)))
}

/// Headers of the form `[(name, value)]` as a header source.
pub(crate) fn header_source<const N: usize>(pairs: [(&str, String); N]) -> ProviderHeaders {
    pairs
        .into_iter()
        .map(|(name, value)| (name.to_owned(), Some(value)))
        .collect()
}

/// Runs `call`: `POST` bodies go through `onPayload` first; the parsed
/// response body comes back after `onResponse`. Retries follow the request
/// options (`maxRetries` defaults to 2).
#[tracing::instrument(skip_all, fields(label = call.label, url = %call.url))]
pub(crate) async fn send(
    model: &Model,
    options: &ProviderRequestOptions,
    call: Call<'_>,
) -> Result<JsonValue, Thrown> {
    let Call {
        label,
        url,
        mut defaults,
        body,
    } = call;
    let (method, text) = match body {
        Body::Get => (reqwest::Method::GET, None),
        Body::Post(payload) => {
            let mut payload = payload;
            if let Some(on_payload) = &options.on_payload {
                if let Some(transformed) = on_payload(payload.clone(), model).await? {
                    payload = transformed;
                }
            }
            defaults
                .entry("content-type".to_owned())
                .or_insert_with(|| Some("application/json".to_owned()));
            (reqwest::Method::POST, Some(json_stringify(&payload)))
        }
    };
    defaults
        .entry("accept".to_owned())
        .or_insert_with(|| Some("application/json".to_owned()));
    let model_headers: Option<ProviderHeaders> = model.headers.as_ref().map(|headers| {
        headers
            .iter()
            .map(|(name, value)| (name.clone(), Some(value.clone())))
            .collect()
    });
    let headers: IndexMap<String, String> = provider_headers_to_record(&[
        Some(&defaults),
        model_headers.as_ref(),
        options.headers.as_ref(),
    ])
    .unwrap_or_default();
    let retry = ProviderRetryOptions {
        max_retries: Some(options.max_retries.unwrap_or(2)),
        max_retry_delay_ms: options.max_retry_delay_ms,
        signal: options.signal.clone(),
        no_retry_statuses: Vec::new(),
    };
    let response = retry_provider_request(
        || {
            fetch_json(
                options.fetch.as_ref(),
                method.clone(),
                &url,
                &headers,
                text.clone(),
                label,
                options.signal.as_ref(),
                options.timeout_ms,
            )
        },
        &retry,
    )
    .await?;
    if let Some(on_response) = &options.on_response {
        on_response(response.provider_response(), model).await?;
    }
    Ok(response.body)
}

/// The error of a response without the expected shape.
pub(crate) fn unexpected(label: &str, what: &str) -> Thrown {
    error(format!("{label} returned an unexpected {what}"))
}

/// A non-negative integer field.
pub(crate) fn count(value: Option<&JsonValue>) -> Option<u64> {
    value.and_then(JsonValue::as_u64)
}
