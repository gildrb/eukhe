//! JSON-over-`fetch` request and response helpers the classifier APIs share
//! (port of `src/api/classifier-shared.ts`).

use std::future::pending;
use std::sync::LazyLock;

use eukhe_chord::context::AbortSignal;
use eukhe_types::pi_ai::{
    ClassifierModel, ClassifierResult, ClassifierStopReason, IndexMap, JsonObject, JsonValue,
    ProviderHeaders, ProviderResponse, Usage,
};
use reqwest::header::{HeaderMap, HeaderName, HeaderValue};

use crate::models::calculate_cost;
use crate::types::{ClassifierOptions, FetchFunction};
use crate::utils::diagnostics::{ErrorObject, SdkValue, Thrown};
use crate::utils::error_body::{format_provider_error, normalize_provider_error};
use crate::utils::headers::{headers_to_record, provider_headers_to_record};
use crate::utils::js::{array_index_key, json_stringify, number_to_js_string};
use crate::utils::provider_retry::{retry_provider_request, ProviderRetryOptions};
use crate::utils::sleep::timer_duration;

/// A plain JS `Error` with `message`.
pub(crate) fn error(message: impl Into<String>) -> Thrown {
    ErrorObject::new(message).thrown()
}

/// TS `new URL(relative, base)`; `TypeError: Invalid URL` on failure.
pub(crate) fn join_url(base: &str, relative: &str) -> Result<url::Url, Thrown> {
    url::Url::parse(base)
        .and_then(|base| base.join(relative))
        .map_err(|_| ErrorObject::named("TypeError", "Invalid URL").thrown())
}

/// TS `baseUrl.replace(/\/+$/u, "")`.
pub(crate) fn trim_trailing_slashes(text: &str) -> &str {
    text.trim_end_matches('/')
}

/// An HTTP failure in the shape `retryProviderRequest` and
/// `normalizeProviderError` understand: `status`, `headers` and the raw `body`
/// (TS `ClassifierHttpError`).
fn http_error(label: &str, status: u16, headers: HeaderMap, body: String) -> Thrown {
    let mut error = ErrorObject::new(format!("{label} returned {status}"));
    error.status = Some(Some(JsonValue::from(status)));
    error.headers = Some(Some(headers));
    error.body = Some(SdkValue::Json(JsonValue::String(body)));
    error.thrown()
}

fn timeout_error(timeout_ms: f64) -> Thrown {
    let mut error = ErrorObject::named(
        "TimeoutError",
        format!(
            "Request timed out after {}ms",
            number_to_js_string(timeout_ms)
        ),
    );
    error.status = Some(None);
    error.headers = Some(None);
    error.body = Some(SdkValue::Json(JsonValue::String(String::new())));
    error.thrown()
}

/// The `status` of a classifier HTTP error, when it has one.
pub(crate) fn http_error_status(error: &Thrown) -> Option<f64> {
    error
        .downcast_ref::<ErrorObject>()?
        .status
        .as_ref()?
        .as_ref()?
        .as_f64()
}

static CLIENT: LazyLock<reqwest::Client> = LazyLock::new(reqwest::Client::new);

#[allow(clippy::needless_pass_by_value)] // used as `map_err(network_error)`
fn network_error(error: reqwest::Error) -> Thrown {
    ErrorObject::named("TypeError", format!("fetch failed: {error}")).thrown()
}

/// `options.fetch ?? globalThis.fetch`.
pub(crate) async fn send(
    fetch: Option<&FetchFunction>,
    request: reqwest::Request,
) -> Result<reqwest::Response, Thrown> {
    match fetch {
        Some(fetch) => fetch(request).await,
        None => CLIENT.execute(request).await.map_err(network_error),
    }
}

/// A successful JSON response.
pub(crate) struct JsonResponse {
    pub(crate) status: u16,
    pub(crate) headers: HeaderMap,
    pub(crate) body: JsonValue,
}

impl JsonResponse {
    /// The `onResponse` view of the response.
    pub(crate) fn provider_response(&self) -> ProviderResponse {
        ProviderResponse {
            status: self.status,
            headers: headers_to_record(&self.headers),
        }
    }
}

/// A `POST` request with `headers` and `body`, as `new Request(url, init)`
/// builds it: invalid header names/values reject with a `TypeError`.
pub(crate) fn post_request(
    url: url::Url,
    headers: &IndexMap<String, String>,
    body: String,
) -> Result<reqwest::Request, Thrown> {
    let mut request = reqwest::Request::new(reqwest::Method::POST, url);
    for (name, value) in headers {
        let name = HeaderName::from_bytes(name.as_bytes()).map_err(|_| {
            ErrorObject::named("TypeError", format!("Invalid header name: \"{name}\"")).thrown()
        })?;
        let value = HeaderValue::from_str(value).map_err(|_| {
            ErrorObject::named("TypeError", format!("Invalid header value: \"{value}\"")).thrown()
        })?;
        request.headers_mut().insert(name, value);
    }
    *request.body_mut() = Some(body.into());
    Ok(request)
}

/// One attempt of a JSON `POST`: `fetch(url, { method: "POST", headers,
/// body, signal })` where `signal` combines the caller's signal with a fresh
/// `AbortSignal.timeout(timeoutMs)`. A non-2xx response throws
/// `"<label> returned <status>"` with the body; a timeout that is not a
/// caller abort throws `"Request timed out after <ms>ms"`; a caller abort
/// rejects with the signal's reason.
pub(crate) async fn post_json(
    fetch: Option<&FetchFunction>,
    url: &str,
    headers: &IndexMap<String, String>,
    body: String,
    label: &str,
    signal: Option<&AbortSignal>,
    timeout_ms: Option<f64>,
) -> Result<JsonResponse, Thrown> {
    let exchange = async {
        let parsed_url = url::Url::parse(url)
            .map_err(|_| ErrorObject::named("TypeError", "Invalid URL").thrown())?;
        let request = post_request(parsed_url, headers, body)?;
        let response = send(fetch, request).await?;
        let status = response.status().as_u16();
        let headers = response.headers().clone();
        let bytes = response.bytes().await.map_err(network_error)?;
        let text = String::from_utf8_lossy(&bytes).into_owned();
        if !(200..300).contains(&status) {
            return Err(http_error(label, status, headers, text));
        }
        let body = serde_json::from_str(&text)
            .map_err(|failure| ErrorObject::named("SyntaxError", failure.to_string()).thrown())?;
        Ok(JsonResponse {
            status,
            headers,
            body,
        })
    };
    let aborted = async {
        match signal {
            Some(signal) => signal.cancelled().await,
            None => pending().await,
        }
    };
    let timed_out = async {
        match timeout_ms {
            Some(ms) => {
                tokio::time::sleep(timer_duration(ms)).await;
                ms
            }
            None => pending().await,
        }
    };
    tokio::select! {
        biased;
        reason = aborted => Err(reason),
        ms = timed_out => Err(timeout_error(ms)),
        result = exchange => result,
    }
}

/// TS `isRecord`.
pub(crate) fn as_record(value: &JsonValue) -> Option<&JsonObject> {
    value.as_object()
}

/// `Object.entries` order of a string-keyed map: array-index keys first,
/// ascending, then the rest in insertion order.
pub(crate) fn js_entries<V>(map: &IndexMap<String, V>) -> Vec<(&String, &V)> {
    let mut indexed: Vec<(u32, &String, &V)> = Vec::new();
    let mut named: Vec<(&String, &V)> = Vec::new();
    for (key, value) in map {
        match array_index_key(key) {
            Some(index) => indexed.push((index, key, value)),
            None => named.push((key, value)),
        }
    }
    indexed.sort_by_key(|(index, _, _)| *index);
    indexed
        .into_iter()
        .map(|(_, key, value)| (key, value))
        .chain(named)
        .collect()
}

/// `model.headers` as a header source.
pub(crate) fn model_headers(model: &ClassifierModel) -> Option<ProviderHeaders> {
    model.headers.as_ref().map(|headers| {
        headers
            .iter()
            .map(|(name, value)| (name.clone(), Some(value.clone())))
            .collect()
    })
}

/// TS `requiredNumber`: a finite number, else `"<label> returned an invalid <field>"`.
pub(crate) fn required_number(
    label: &str,
    value: Option<&JsonValue>,
    field: &str,
) -> Result<f64, Thrown> {
    value
        .and_then(JsonValue::as_f64)
        .filter(|number| number.is_finite())
        .ok_or_else(|| error(format!("{label} returned an invalid {field}")))
}

fn request_headers(
    model: &ClassifierModel,
    api_key: &str,
    options_headers: Option<&ProviderHeaders>,
) -> IndexMap<String, String> {
    let defaults: ProviderHeaders = [
        (
            "authorization".to_owned(),
            Some(format!("Bearer {api_key}")),
        ),
        (
            "content-type".to_owned(),
            Some("application/json".to_owned()),
        ),
    ]
    .into_iter()
    .collect();
    let model_headers = model_headers(model);
    provider_headers_to_record(&[Some(&defaults), model_headers.as_ref(), options_headers])
        .unwrap_or_default()
}

/// The retry options of a classifier request (`maxRetries` defaults to 2).
pub(crate) fn retry_options(options: &ClassifierOptions) -> ProviderRetryOptions {
    ProviderRetryOptions {
        max_retries: Some(options.request.max_retries.unwrap_or(2)),
        max_retry_delay_ms: options.request.max_retry_delay_ms,
        signal: options.request.signal.clone(),
        no_retry_statuses: Vec::new(),
    }
}

/// Posts one JSON classifier request with bearer auth, `onPayload`/
/// `onResponse` hooks, a fresh timeout per attempt, and provider retries.
/// Returns the parsed response body; fails like the request did.
/// `no_retry_statuses` lists HTTP statuses that fail at once although they
/// are normally retried.
pub(crate) async fn post_classifier_request(
    label: &str,
    url: &url::Url,
    model: &ClassifierModel,
    body: JsonValue,
    options: &ClassifierOptions,
    no_retry_statuses: &[u16],
) -> Result<JsonValue, Thrown> {
    let request = &options.request;
    let Some(api_key) = request.api_key.as_deref().filter(|key| !key.is_empty()) else {
        return Err(error(format!(
            "No API key for provider: {}",
            model.provider
        )));
    };
    let mut payload = body;
    if let Some(on_payload) = &request.on_payload {
        if let Some(transformed) = on_payload(payload.clone(), model).await? {
            payload = transformed;
        }
    }
    let headers = request_headers(model, api_key, request.headers.as_ref());
    let body = json_stringify(&payload);
    let retry = ProviderRetryOptions {
        no_retry_statuses: no_retry_statuses.to_vec(),
        ..retry_options(options)
    };
    let response = retry_provider_request(
        || {
            post_json(
                request.fetch.as_ref(),
                url.as_str(),
                &headers,
                body.clone(),
                label,
                request.signal.as_ref(),
                request.timeout_ms,
            )
        },
        &retry,
    )
    .await?;
    if let Some(on_response) = &request.on_response {
        on_response(response.provider_response(), model).await?;
    }
    Ok(response.body)
}

/// A positive finite token count, else 0. `Usage` counts are integers, so a
/// fractional count is truncated.
#[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)] // positive, finite, below 2^53
fn token_count(value: Option<&JsonValue>) -> u64 {
    match value.and_then(JsonValue::as_f64) {
        Some(number) if number.is_finite() && number > 0.0 => number as u64,
        _ => 0,
    }
}

/// Usage from a `{ input_tokens, output_tokens }` object, priced from the
/// model catalog like chat usage. A missing or malformed usage object leaves
/// the result without usage instead of failing it.
pub(crate) fn parse_classifier_usage(
    value: Option<&JsonValue>,
    model: &ClassifierModel,
) -> Option<Usage> {
    let record = value.and_then(as_record)?;
    if !record.contains_key("input_tokens") && !record.contains_key("output_tokens") {
        return None;
    }
    let input = token_count(record.get("input_tokens"));
    let output = token_count(record.get("output_tokens"));
    let mut usage = Usage {
        input,
        output,
        total_tokens: input + output,
        ..Usage::default()
    };
    calculate_cost(model, &mut usage);
    Some(usage)
}

/// A fresh `stop` result for `model`.
pub(crate) fn empty_result(model: &ClassifierModel) -> ClassifierResult {
    ClassifierResult {
        api: model.api.clone(),
        provider: model.provider.clone(),
        model: model.id.clone(),
        answers: IndexMap::new(),
        usage: None,
        stop_reason: ClassifierStopReason::Stop,
        error_message: None,
        timestamp: crate::utils::now_ms(),
    }
}

/// Whether the caller's signal has aborted (`options.signal?.aborted`).
pub(crate) fn aborted(options: &ClassifierOptions) -> bool {
    options
        .request
        .signal
        .as_ref()
        .is_some_and(AbortSignal::aborted)
}

/// Records a caught classifier error on `output`.
pub(crate) fn fail(
    output: &mut ClassifierResult,
    options: &ClassifierOptions,
    error: &Thrown,
    prefix: &str,
) {
    output.stop_reason = if aborted(options) {
        ClassifierStopReason::Aborted
    } else {
        ClassifierStopReason::Error
    };
    output.error_message = Some(format_provider_error(
        &normalize_provider_error(error),
        Some(prefix),
    ));
}
