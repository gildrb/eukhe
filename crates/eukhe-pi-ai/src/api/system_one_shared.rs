//! System One classification shared by the services that serve `TypeSafe`'s
//! System One models (port of `src/api/system-one-shared.ts`), plus the
//! JSON-over-`fetch` request helper the classifier APIs share.

use std::future::pending;
use std::sync::LazyLock;

use eukhe_chord::context::AbortSignal;
use eukhe_types::pi_ai::{
    ClassifierAnswer, ClassifierContext, ClassifierModel, ClassifierQuestion, ClassifierResult,
    ClassifierStopReason, IndexMap, JsonObject, JsonValue, ProviderHeaders, ProviderResponse,
    Usage,
};
use reqwest::header::{HeaderMap, HeaderName, HeaderValue};

use crate::models::calculate_cost;
use crate::types::{ClassifierOptions, FetchFunction};
use crate::utils::diagnostics::{ErrorObject, SdkValue, Thrown};
use crate::utils::error_body::{format_provider_error, normalize_provider_error};
use crate::utils::headers::{headers_to_record, provider_headers_to_record};
use crate::utils::js::{array_index_key, js_object_entries, json_stringify, number_to_js_string};
use crate::utils::provider_retry::{retry_provider_request, ProviderRetryOptions};
use crate::utils::sleep::timer_duration;

/// Differences between services that serve System One models.
pub(crate) struct SystemOneTransport {
    /// Classifier API implemented by this transport.
    pub(crate) api: &'static str,
    /// Service name used in error messages.
    pub(crate) label: &'static str,
    /// Absolute request URL.
    pub(crate) url: fn(&ClassifierModel) -> Result<url::Url, Thrown>,
    /// Wraps the System One request (`{ state, questions }`) in the service's
    /// request envelope.
    pub(crate) payload: fn(&ClassifierModel, JsonObject) -> JsonValue,
    /// Extracts the System One output (`{ answers, usage }`) from the
    /// service's response envelope.
    pub(crate) output: fn(JsonValue) -> Result<JsonObject, Thrown>,
}

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

/// An HTTP error carrying `status`, `headers` and the raw `body`, so
/// `retryProviderRequest` and `normalizeProviderError` see it as a provider
/// error.
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

fn required_number(label: &str, value: Option<&JsonValue>, field: &str) -> Result<f64, Thrown> {
    value
        .and_then(JsonValue::as_f64)
        .filter(|number| number.is_finite())
        .ok_or_else(|| error(format!("{label} returned an invalid {field}")))
}

fn probabilities(
    label: &str,
    value: Option<&JsonValue>,
    id: &str,
) -> Result<IndexMap<String, f64>, Thrown> {
    let Some(record) = value.and_then(as_record) else {
        return Err(error(format!(
            "{label} returned invalid probabilities for {id}"
        )));
    };
    js_object_entries(record)
        .into_iter()
        .map(|(key, probability)| {
            let number = required_number(
                label,
                Some(probability),
                &format!("probability for {id}.{key}"),
            )?;
            Ok((key.clone(), number))
        })
        .collect()
}

fn parse_answers(
    label: &str,
    value: Option<&JsonValue>,
    context: &ClassifierContext,
) -> Result<IndexMap<String, ClassifierAnswer>, Thrown> {
    let Some(value) = value.and_then(as_record) else {
        return Err(error(format!("{label} returned an unexpected response")));
    };
    let mut answers = IndexMap::new();
    for (id, question) in js_entries(&context.questions) {
        let Some(answer) = value.get(id).and_then(as_record) else {
            return Err(error(format!("{label} did not return an answer for {id}")));
        };
        let answer_type = answer.get("type").and_then(JsonValue::as_str);
        let parsed = match question {
            ClassifierQuestion::Choice { .. } => {
                let choice = answer.get("choice").and_then(JsonValue::as_str);
                let (Some("choice"), Some(choice)) = (answer_type, choice) else {
                    return Err(error(format!(
                        "{label} did not return a choice answer for {id}"
                    )));
                };
                ClassifierAnswer::Choice {
                    choice: choice.to_owned(),
                    probabilities: probabilities(label, answer.get("probabilities"), id)?,
                    confidence: required_number(
                        label,
                        answer.get("confidence"),
                        &format!("confidence for {id}"),
                    )?,
                }
            }
            ClassifierQuestion::Score { .. } => {
                if answer_type != Some("score") {
                    return Err(error(format!(
                        "{label} did not return a score answer for {id}"
                    )));
                }
                ClassifierAnswer::Score {
                    score: required_number(label, answer.get("score"), &format!("score for {id}"))?,
                    confidence: required_number(
                        label,
                        answer.get("confidence"),
                        &format!("confidence for {id}"),
                    )?,
                }
            }
            ClassifierQuestion::Bool { .. } => {
                if answer_type != Some("noul") {
                    return Err(error(format!(
                        "{label} did not return a bool answer for {id}"
                    )));
                }
                ClassifierAnswer::Bool {
                    probability: required_number(
                        label,
                        answer.get("noul"),
                        &format!("probability for {id}"),
                    )?,
                }
            }
        };
        answers.insert(id.clone(), parsed);
    }
    Ok(answers)
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

/// Usage from System One's `{ input_tokens, output_tokens }`, priced from the
/// model catalog like chat usage. A missing or malformed usage object leaves
/// the result without usage instead of failing it.
fn parse_usage(value: Option<&JsonValue>, model: &ClassifierModel) -> Option<Usage> {
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

/// Maps public `bool` questions to `TypeSafe`'s wire-level `noul` type:
/// `{ state, questions }`.
fn wire_request(context: &ClassifierContext) -> JsonObject {
    let mut questions = JsonObject::new();
    for (id, question) in js_entries(&context.questions) {
        let mut value = serde_json::to_value(question).unwrap_or(JsonValue::Null);
        if matches!(question, ClassifierQuestion::Bool { .. }) {
            if let Some(object) = value.as_object_mut() {
                object.insert("type".to_owned(), JsonValue::from("noul"));
            }
        }
        questions.insert(id.clone(), value);
    }
    let mut request = JsonObject::new();
    request.insert("state".to_owned(), JsonValue::Object(context.state.clone()));
    request.insert("questions".to_owned(), JsonValue::Object(questions));
    request
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

/// Records a caught classifier error on `output`.
pub(crate) fn fail(
    output: &mut ClassifierResult,
    options: &ClassifierOptions,
    error: &Thrown,
    prefix: &str,
) {
    output.stop_reason = if options
        .request
        .signal
        .as_ref()
        .is_some_and(AbortSignal::aborted)
    {
        ClassifierStopReason::Aborted
    } else {
        ClassifierStopReason::Error
    };
    output.error_message = Some(format_provider_error(
        &normalize_provider_error(error),
        Some(prefix),
    ));
}

/// The retry options of a classifier request (`maxRetries` defaults to 2).
pub(crate) fn retry_options(options: &ClassifierOptions) -> ProviderRetryOptions {
    ProviderRetryOptions {
        max_retries: Some(options.request.max_retries.unwrap_or(2)),
        max_retry_delay_ms: options.request.max_retry_delay_ms,
        signal: options.request.signal.clone(),
    }
}

/// Runs one System One classification over the given transport.
pub(crate) async fn classify_system_one(
    transport: &SystemOneTransport,
    model: ClassifierModel,
    context: ClassifierContext,
    options: ClassifierOptions,
) -> ClassifierResult {
    let mut output = empty_result(&model);
    if let Err(error) = run(transport, &model, &context, &options, &mut output).await {
        fail(
            &mut output,
            &options,
            &error,
            &format!("{} error", transport.label),
        );
    }
    output
}

async fn run(
    transport: &SystemOneTransport,
    model: &ClassifierModel,
    context: &ClassifierContext,
    options: &ClassifierOptions,
    output: &mut ClassifierResult,
) -> Result<(), Thrown> {
    let request = &options.request;
    if model.api != transport.api {
        return Err(error(format!("Unsupported classifier API: {}", model.api)));
    }
    let Some(api_key) = request.api_key.as_deref().filter(|key| !key.is_empty()) else {
        return Err(error(format!(
            "No API key for provider: {}",
            model.provider
        )));
    };
    let mut payload = (transport.payload)(model, wire_request(context));
    if let Some(on_payload) = &request.on_payload {
        if let Some(transformed) = on_payload(payload.clone(), model).await? {
            payload = transformed;
        }
    }
    let url = (transport.url)(model)?;
    let headers = request_headers(model, api_key, request.headers.as_ref());
    let body = json_stringify(&payload);
    let response = retry_provider_request(
        || {
            post_json(
                request.fetch.as_ref(),
                url.as_str(),
                &headers,
                body.clone(),
                transport.label,
                request.signal.as_ref(),
                request.timeout_ms,
            )
        },
        &retry_options(options),
    )
    .await?;
    if let Some(on_response) = &request.on_response {
        on_response(response.provider_response(), model).await?;
    }
    let result = (transport.output)(response.body)?;
    // Set before parsing answers: a request with malformed answers was still billed.
    if let Some(usage) = parse_usage(result.get("usage"), model) {
        output.usage = Some(usage);
    }
    output.answers = parse_answers(transport.label, result.get("answers"), context)?;
    Ok(())
}

#[cfg(test)]
#[path = "system_one_test_fetch.rs"]
pub(crate) mod test_fetch;
