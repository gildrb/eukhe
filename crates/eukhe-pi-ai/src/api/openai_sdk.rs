//! The request path of the `openai` npm SDK (v7.19.0) that the
//! OpenAI-family wire APIs use (`client.<resource>.create(params,
//! { signal, timeout, maxRetries: 0 }).withResponse()` with `stream: true`):
//! header assembly, URL building, the `fetch` call with its timeout and
//! abort handling, `APIError` construction for non-2xx responses, and the
//! server-sent-event decoding of `Stream.fromSSEResponse`.
//!
//! Not a TS module of pi-ai: pi-ai links the SDK. The SDK features pi-ai
//! never uses (retries, which pi-ai runs through `retryProviderRequest`,
//! non-streaming bodies, workload identity, logging) are not reproduced.

mod sse;

use std::collections::HashMap;
use std::sync::LazyLock;

use crate::types::{FetchFunction, JsonValue, ProviderHeaders};
use crate::utils::diagnostics::{ErrorObject, SdkValue, Thrown};
use crate::utils::js::{json_stringify, number_to_js_string};
use crate::utils::stream_failure::{
    stream_failure_from_stop_reason, ConnectionErrorKind, ConnectionErrorProfile,
    ProviderConnectionError, ProviderError,
};
use eukhe_chord::context::AbortSignal;
use futures::stream::BoxStream;
use futures::StreamExt;
use reqwest::header::{HeaderMap, HeaderName, HeaderValue};
use serde_json::json;

pub(crate) use sse::SseEventStream;

/// `VERSION` of the pinned `openai` package.
pub(crate) const OPENAI_SDK_VERSION: &str = "7.19.0";

/// `OpenAI.DEFAULT_TIMEOUT`: 10 minutes.
const DEFAULT_TIMEOUT_MS: f64 = 600_000.0;

/// Which SDK client class sends the request.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum OpenAiClientKind {
    /// `new OpenAI(...)`: `Authorization: Bearer <apiKey>`.
    OpenAI,
    /// `new AzureOpenAI(...)`: `api-key: <apiKey>`, redirects not followed.
    AzureOpenAI,
}

impl OpenAiClientKind {
    /// `${this.constructor.name}/JS ${VERSION}`.
    fn user_agent(self) -> String {
        let name = match self {
            Self::OpenAI => "OpenAI",
            Self::AzureOpenAI => "AzureOpenAI",
        };
        format!("{name}/JS {OPENAI_SDK_VERSION}")
    }
}

/// Client construction options (`ClientOptions` subset).
#[derive(Clone)]
pub(crate) struct OpenAiClientConfig {
    pub kind: OpenAiClientKind,
    pub api_key: String,
    pub base_url: String,
    /// `defaultHeaders`: merged over the SDK headers; `None` deletes one.
    pub default_headers: ProviderHeaders,
    /// `defaultQuery` (Azure: `api-version`).
    pub default_query: Vec<(String, String)>,
    pub fetch: Option<FetchFunction>,
}

/// Per-request options (`RequestOptions` subset).
#[derive(Debug, Clone, Default)]
pub(crate) struct OpenAiRequestOptions {
    pub signal: Option<AbortSignal>,
    pub timeout_ms: Option<f64>,
}

/// A streaming response: TS `{ data: Stream, response }` of `withResponse()`.
pub(crate) struct OpenAiStreamResponse {
    pub status: u16,
    pub headers: HeaderMap,
    pub events: SseEventStream,
}

impl std::fmt::Debug for OpenAiStreamResponse {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("OpenAiStreamResponse")
            .field("status", &self.status)
            .field("headers", &self.headers)
            .finish_non_exhaustive()
    }
}

/// A non-streaming response: TS `{ data, response }` of `withResponse()`.
#[derive(Debug)]
pub(crate) struct OpenAiJsonResponse {
    pub status: u16,
    pub headers: HeaderMap,
    /// The parsed body; `null` for an empty JSON body (TS `undefined`).
    pub data: JsonValue,
}

static CLIENT: LazyLock<reqwest::Client> = LazyLock::new(reqwest::Client::new);

/// `AzureOpenAI` sets `redirect: "manual"` when it sends `api-key`.
static NO_REDIRECT_CLIENT: LazyLock<reqwest::Client> = LazyLock::new(|| {
    reqwest::Client::builder()
        .redirect(reqwest::redirect::Policy::none())
        .build()
        .unwrap_or_default()
});

/// An `OpenAIError` (a plain `Error` subclass).
fn openai_error(message: impl Into<String>) -> Thrown {
    ErrorObject::new(message).thrown()
}

/// An `APIError` with `status`, `headers`, and the parsed `error` body.
pub(crate) fn api_error(
    status: Option<u16>,
    error: Option<JsonValue>,
    message: Option<&str>,
    headers: Option<HeaderMap>,
) -> ErrorObject {
    let text = api_error_message(status, error.as_ref(), message);
    let mut object = ErrorObject::new(text);
    object.status = Some(status.map(JsonValue::from));
    object.headers = Some(headers);
    object.error = error.map(SdkValue::Json);
    object
}

/// TS `APIError.makeMessage`.
fn api_error_message(
    status: Option<u16>,
    error: Option<&JsonValue>,
    message: Option<&str>,
) -> String {
    let error_message = error
        .and_then(|error| error.get("message"))
        .filter(|value| js_truthy(value));
    let msg: Option<String> = match error_message {
        Some(JsonValue::String(text)) => Some(text.clone()),
        Some(value) => Some(json_stringify(value)),
        None => match error {
            Some(error) if js_truthy(error) => Some(json_stringify(error)),
            _ => message.map(str::to_owned),
        },
    };
    let msg = msg.filter(|msg| !msg.is_empty());
    match (status.filter(|status| *status != 0), msg) {
        (Some(status), Some(msg)) => format!("{status} {msg}"),
        (Some(status), None) => format!("{status} status code (no body)"),
        (None, Some(msg)) => msg,
        (None, None) => "(no status code or body)".to_owned(),
    }
}

/// JS truthiness of a JSON value.
pub(crate) fn js_truthy(value: &JsonValue) -> bool {
    match value {
        JsonValue::Null => false,
        JsonValue::Bool(flag) => *flag,
        JsonValue::Number(number) => number.as_f64().is_some_and(|n| n != 0.0 && !n.is_nan()),
        JsonValue::String(text) => !text.is_empty(),
        JsonValue::Array(_) | JsonValue::Object(_) => true,
    }
}

/// `APIUserAbortError`: "Request was aborted.".
fn user_abort_error() -> Thrown {
    api_error(None, None, Some("Request was aborted."), None).thrown()
}

/// `APIConnectionTimeoutError`: "Request timed out.".
fn timeout_error() -> Thrown {
    api_error(None, None, Some("Request timed out."), None).thrown()
}

/// `APIConnectionError`: "Connection error.".
fn connection_error() -> Thrown {
    api_error(None, None, Some("Connection error."), None).thrown()
}

/// Whether `error` is one of the SDK's connection errors (connect failure
/// or timeout before the response headers).
pub(crate) fn is_connection_error(error: &Thrown) -> Option<ConnectionFailure> {
    let object = error.downcast_ref::<ErrorObject>()?;
    if object.status != Some(None) || object.headers != Some(None) {
        return None;
    }
    match object.message.as_str() {
        "Connection error." => Some(ConnectionFailure::Connect),
        "Request timed out." => Some(ConnectionFailure::Timeout),
        _ => None,
    }
}

/// The SDK connection-error kinds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ConnectionFailure {
    Connect,
    Timeout,
}

/// TS `buildHeaders`: later sources override earlier ones by
/// case-insensitive name; a `None` value deletes the header.
struct HeaderBuilder {
    entries: Vec<(String, String)>,
}

impl HeaderBuilder {
    const fn new() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    fn set(&mut self, name: &str, value: Option<&str>) {
        self.entries
            .retain(|(existing, _)| !existing.eq_ignore_ascii_case(name));
        if let Some(value) = value {
            self.entries.push((name.to_owned(), value.to_owned()));
        }
    }

    fn into_header_map(self) -> Result<HeaderMap, Thrown> {
        let mut map = HeaderMap::new();
        for (name, value) in self.entries {
            let header_name = HeaderName::from_bytes(name.as_bytes()).map_err(|_| {
                ErrorObject::named("TypeError", format!("Invalid header name: \"{name}\"")).thrown()
            })?;
            let header_value = HeaderValue::from_str(&value).map_err(|_| {
                ErrorObject::named("TypeError", format!("Invalid header value for \"{name}\""))
                    .thrown()
            })?;
            map.append(header_name, header_value);
        }
        Ok(map)
    }
}

/// `X-Stainless-OS` of the supported platforms (`normalizePlatform`).
fn stainless_os() -> String {
    match std::env::consts::OS {
        "macos" => "MacOS".to_owned(),
        "linux" => "Linux".to_owned(),
        other => format!("Other:{other}"),
    }
}

/// `X-Stainless-Arch` of the supported platforms (`normalizeArch`).
fn stainless_arch() -> String {
    match std::env::consts::ARCH {
        "x86_64" => "x64".to_owned(),
        "aarch64" => "arm64".to_owned(),
        other => format!("other:{other}"),
    }
}

/// An SDK client bound to one configuration.
pub(crate) struct OpenAiClient {
    config: OpenAiClientConfig,
}

impl OpenAiClient {
    pub(crate) const fn new(config: OpenAiClientConfig) -> Self {
        Self { config }
    }

    /// TS `buildURL(path, query)`.
    fn build_url(&self, path: &str) -> Result<url::Url, Thrown> {
        let base = &self.config.base_url;
        let joined = if base.ends_with('/') && path.starts_with('/') {
            format!("{base}{}", &path[1..])
        } else {
            format!("{base}{path}")
        };
        let mut url = url::Url::parse(&joined)
            .map_err(|_| ErrorObject::named("TypeError", "Invalid URL").thrown())?;
        if !self.config.default_query.is_empty() {
            let mut query: Vec<(String, String)> = url
                .query_pairs()
                .map(|(key, value)| (key.into_owned(), value.into_owned()))
                .collect();
            for (key, value) in &self.config.default_query {
                if let Some(existing) = query.iter_mut().find(|(name, _)| name == key) {
                    existing.1.clone_from(value);
                } else {
                    query.push((key.clone(), value.clone()));
                }
            }
            url.query_pairs_mut().clear().extend_pairs(query);
        }
        Ok(url)
    }

    /// TS `buildHeaders`: SDK defaults, auth, `defaultHeaders`, body headers.
    fn build_headers(&self, timeout_ms: f64) -> Result<HeaderMap, Thrown> {
        let mut headers = HeaderBuilder::new();
        headers.set("Accept", Some("application/json"));
        headers.set("User-Agent", Some(&self.config.kind.user_agent()));
        headers.set("X-Stainless-Retry-Count", Some("0"));
        if timeout_ms != 0.0 {
            headers.set(
                "X-Stainless-Timeout",
                Some(&number_to_js_string((timeout_ms / 1000.0).trunc())),
            );
        }
        headers.set("X-Stainless-Lang", Some("js"));
        headers.set("X-Stainless-Package-Version", Some(OPENAI_SDK_VERSION));
        headers.set("X-Stainless-OS", Some(&stainless_os()));
        headers.set("X-Stainless-Arch", Some(&stainless_arch()));
        headers.set("X-Stainless-Runtime", Some("unknown"));
        headers.set("X-Stainless-Runtime-Version", Some("unknown"));
        match self.config.kind {
            OpenAiClientKind::OpenAI => headers.set(
                "Authorization",
                Some(&format!("Bearer {}", self.config.api_key)),
            ),
            OpenAiClientKind::AzureOpenAI => headers.set("api-key", Some(&self.config.api_key)),
        }
        for (name, value) in &self.config.default_headers {
            headers.set(name, value.as_deref());
        }
        headers.set("content-type", Some("application/json"));
        headers.into_header_map()
    }

    /// `this._client.post(path, { body, stream: true, signal, timeout })`
    /// followed by `.withResponse()`.
    ///
    /// # Errors
    ///
    /// The SDK errors: `APIUserAbortError`, `APIConnectionTimeoutError`,
    /// `APIConnectionError`, a status `APIError`, an invalid timeout.
    pub(crate) async fn post_stream(
        &self,
        path: &str,
        body: &JsonValue,
        options: &OpenAiRequestOptions,
    ) -> Result<OpenAiStreamResponse, Thrown> {
        if let Some(timeout) = options.timeout_ms {
            if timeout.fract() != 0.0 || !timeout.is_finite() {
                return Err(openai_error("timeout must be an integer"));
            }
            if timeout < 0.0 {
                return Err(openai_error("timeout must be a positive integer"));
            }
        }
        let timeout_ms = options.timeout_ms.unwrap_or(DEFAULT_TIMEOUT_MS);
        let url = self.build_url(path)?;
        let headers = self.build_headers(timeout_ms)?;
        let signal = options.signal.clone();
        if signal.as_ref().is_some_and(AbortSignal::aborted) {
            return Err(user_abort_error());
        }

        let mut request = reqwest::Request::new(reqwest::Method::POST, url);
        *request.headers_mut() = headers;
        *request.body_mut() = Some(reqwest::Body::from(json_stringify(body)));

        let send = async {
            if let Some(fetch) = &self.config.fetch {
                fetch(request).await
            } else {
                let client = match self.config.kind {
                    OpenAiClientKind::OpenAI => &*CLIENT,
                    OpenAiClientKind::AzureOpenAI => &*NO_REDIRECT_CLIENT,
                };
                client
                    .execute(request)
                    .await
                    .map_err(crate::utils::diagnostics::thrown)
            }
        };
        let aborted = async {
            if let Some(signal) = &signal {
                signal.cancelled().await;
            } else {
                std::future::pending::<()>().await;
            }
        };
        let timer = crate::utils::sleep::timer_duration(timeout_ms);
        let response = tokio::select! {
            () = aborted => return Err(user_abort_error()),
            () = tokio::time::sleep(timer) => return Err(timeout_error()),
            result = send => result,
        };
        let response = match response {
            Ok(response) => response,
            Err(_) if signal.as_ref().is_some_and(AbortSignal::aborted) => {
                return Err(user_abort_error());
            }
            Err(_) => return Err(connection_error()),
        };

        let status = response.status().as_u16();
        let response_headers = response.headers().clone();
        if !response.status().is_success() {
            let text = match response.text().await {
                Ok(text) => text,
                Err(error) => error.to_string(),
            };
            return Err(status_error(status, &text, response_headers).thrown());
        }
        let bytes: BoxStream<'static, Result<Vec<u8>, String>> = response
            .bytes_stream()
            .map(|chunk| {
                chunk
                    .map(|bytes| bytes.to_vec())
                    .map_err(|error| error.to_string())
            })
            .boxed();
        Ok(OpenAiStreamResponse {
            status,
            headers: response_headers.clone(),
            events: sse::sse_json_stream(bytes, response_headers, signal),
        })
    }

    /// `this._client.post(path, { body, signal, timeout })` followed by
    /// `.withResponse()` for a non-streaming request: the response body is
    /// read under the same deadline as the headers (`parseResponseWithTimeout`)
    /// and parsed by `defaultParseResponse` (JSON media types as JSON, `null`
    /// for an empty JSON body, otherwise the text). Added for
    /// `openrouter-images`.
    ///
    /// # Errors
    ///
    /// The SDK errors: `APIUserAbortError`, `APIConnectionTimeoutError`,
    /// `APIConnectionError`, a status `APIError`, an invalid timeout, and the
    /// `SyntaxError` of an invalid JSON body.
    pub(crate) async fn post_json(
        &self,
        path: &str,
        body: &JsonValue,
        options: &OpenAiRequestOptions,
    ) -> Result<OpenAiJsonResponse, Thrown> {
        if let Some(timeout) = options.timeout_ms {
            if timeout.fract() != 0.0 || !timeout.is_finite() {
                return Err(openai_error("timeout must be an integer"));
            }
            if timeout < 0.0 {
                return Err(openai_error("timeout must be a positive integer"));
            }
        }
        let timeout_ms = options.timeout_ms.unwrap_or(DEFAULT_TIMEOUT_MS);
        let url = self.build_url(path)?;
        let headers = self.build_headers(timeout_ms)?;
        let signal = options.signal.clone();
        if signal.as_ref().is_some_and(AbortSignal::aborted) {
            return Err(user_abort_error());
        }

        let mut request = reqwest::Request::new(reqwest::Method::POST, url);
        *request.headers_mut() = headers;
        *request.body_mut() = Some(reqwest::Body::from(json_stringify(body)));

        let exchange = async {
            let sent = if let Some(fetch) = &self.config.fetch {
                fetch(request).await
            } else {
                let client = match self.config.kind {
                    OpenAiClientKind::OpenAI => &*CLIENT,
                    OpenAiClientKind::AzureOpenAI => &*NO_REDIRECT_CLIENT,
                };
                client
                    .execute(request)
                    .await
                    .map_err(crate::utils::diagnostics::thrown)
            };
            let response = sent.map_err(|_| connection_error())?;
            let status = response.status().as_u16();
            let response_headers = response.headers().clone();
            let text = match response.text().await {
                Ok(text) => text,
                Err(error) if !(200..300).contains(&status) => error.to_string(),
                Err(_) => return Err(connection_error()),
            };
            Ok((status, response_headers, text))
        };
        let aborted = async {
            match &signal {
                Some(signal) => {
                    signal.cancelled().await;
                }
                None => std::future::pending::<()>().await,
            }
        };
        let timer = crate::utils::sleep::timer_duration(timeout_ms);
        let (status, headers, text) = tokio::select! {
            () = aborted => return Err(user_abort_error()),
            () = tokio::time::sleep(timer) => return Err(timeout_error()),
            result = exchange => result?,
        };
        if !(200..300).contains(&status) {
            return Err(status_error(status, &text, headers).thrown());
        }
        let media_type = headers
            .get(reqwest::header::CONTENT_TYPE)
            .and_then(|value| value.to_str().ok())
            .and_then(|value| value.split(';').next())
            .map(|value| value.trim().to_lowercase());
        let is_json = media_type
            .as_deref()
            .is_some_and(|media| media.contains("application/json") || media.ends_with("+json"));
        let data = if !is_json {
            JsonValue::String(text)
        } else if text.is_empty() {
            JsonValue::Null
        } else {
            serde_json::from_str(&text).map_err(|failure| {
                ErrorObject::named("SyntaxError", failure.to_string()).thrown()
            })?
        };
        Ok(OpenAiJsonResponse {
            status,
            headers,
            data,
        })
    }
}

/// TS `makeStatusError(status, safeJSON(errText), errMessage, headers)`.
fn status_error(status: u16, text: &str, headers: HeaderMap) -> ErrorObject {
    let parsed: Option<JsonValue> = serde_json::from_str(text).ok();
    let message = match &parsed {
        Some(value) if js_truthy(value) => None,
        _ => Some(text),
    };
    // `{ error }` normalization, then `APIError.generate` reads `.error`.
    let error = match parsed {
        Some(value @ (JsonValue::Object(_) | JsonValue::Array(_))) => {
            match value.get("error").filter(|inner| !inner.is_null()) {
                Some(inner) => Some(inner.clone()),
                None => Some(value),
            }
        }
        Some(_) | None => None,
    };
    api_error(Some(status), error, message, Some(headers))
}

/// eukhe addition: the provider stream-failure classification of an error
/// a request through this SDK ended with, for
/// [`record_stream_failure`](crate::utils::stream_failure::record_stream_failure).
/// `raw_stop_reason` is the message's raw stop reason when a terminal
/// response event set one (a failed or incomplete response).
pub(crate) fn stream_failure_of(
    error: &Thrown,
    aborted: bool,
    raw_stop_reason: Option<&str>,
    request_id: Option<&str>,
) -> ProviderError {
    if aborted {
        return ProviderError::Aborted;
    }
    if let Some(failure) = is_connection_error(error) {
        return ProviderError::Connection(ProviderConnectionError {
            kind: match failure {
                ConnectionFailure::Connect => ConnectionErrorKind::Connect,
                ConnectionFailure::Timeout => ConnectionErrorKind::Timeout,
            },
            profile: ConnectionErrorProfile::Sdk,
            cause: error.to_string(),
        });
    }
    if let Some(object) = error.downcast_ref::<ErrorObject>() {
        if let Some(Some(status)) = object.status.as_ref().map(|status| {
            status
                .as_ref()
                .and_then(JsonValue::as_u64)
                .and_then(|status| u16::try_from(status).ok())
        }) {
            let body = match &object.error {
                Some(SdkValue::Json(value)) => json_stringify(&json!({ "error": value })),
                Some(SdkValue::Stream | SdkValue::Instance) | None => object.message.clone(),
            };
            let headers: HashMap<String, String> = object
                .headers
                .clone()
                .flatten()
                .map(|headers| {
                    headers
                        .iter()
                        .filter_map(|(name, value)| {
                            Some((name.as_str().to_owned(), value.to_str().ok()?.to_owned()))
                        })
                        .collect()
                })
                .unwrap_or_default();
            return ProviderError::from_http_status_body(status, &body, headers);
        }
    }
    if let Some(raw_stop_reason) = raw_stop_reason {
        return ProviderError::StreamFailure(stream_failure_from_stop_reason(
            Some(raw_stop_reason),
            request_id,
        ));
    }
    ProviderError::Message(error.to_string())
}

#[cfg(test)]
mod tests;
