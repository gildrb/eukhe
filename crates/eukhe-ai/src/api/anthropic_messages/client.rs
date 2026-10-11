//! The part of the `@anthropic-ai/sdk` client (v0.129.0) that
//! `anthropic-messages.ts` relies on: header assembly (`buildHeaders`,
//! `validateHeaders`), `beta.messages.create(params).asResponse()` for a
//! streaming request, and the SDK error classes (`APIError.generate`,
//! `APIConnectionError`, `APIConnectionTimeoutError`, `APIUserAbortError`).

use std::collections::HashSet;
use std::sync::{Arc, LazyLock};
use std::time::Duration;

use eukhe_chord::context::AbortSignal;
use eukhe_types::pi_ai::{IndexMap, JsonObject, JsonValue, ProviderHeaders};
use reqwest::header::{HeaderMap, HeaderName, HeaderValue};

use super::federation::FederationAuth;
use crate::types::FetchFunction;
use crate::utils::diagnostics::{ErrorObject, Thrown};
use crate::utils::js::{js_to_string, json_stringify};

/// The pinned SDK version (TS `VERSION`).
pub(crate) const SDK_VERSION: &str = "0.129.0";

/// SDK default request timeout of `beta.messages.create` in milliseconds.
const DEFAULT_TIMEOUT_MS: f64 = 600_000.0;

/// The headers the SDK sends: case-insensitive, last write wins, `null`
/// removes and records the name (TS `buildHeaders` → `{ values, nulls }`).
#[derive(Debug, Default, Clone)]
pub(crate) struct HeaderBag {
    values: IndexMap<String, String>,
    nulls: HashSet<String>,
}

impl HeaderBag {
    pub(crate) fn set(&mut self, name: &str, value: Option<&str>) {
        let lower = name.to_ascii_lowercase();
        self.values.shift_remove(&lower);
        if let Some(value) = value {
            self.nulls.remove(&lower);
            self.values.insert(lower, value.to_owned());
        } else {
            self.nulls.insert(lower);
        }
    }

    pub(crate) fn apply(&mut self, headers: &ProviderHeaders) {
        for (name, value) in headers {
            self.set(name, value.as_deref());
        }
    }

    pub(crate) fn get(&self, name: &str) -> Option<&str> {
        self.values.get(name).map(String::as_str)
    }

    pub(crate) fn values(&self) -> &IndexMap<String, String> {
        &self.values
    }
}

/// How the SDK client authenticates.
#[derive(Clone)]
pub(crate) enum ClientAuth {
    /// `apiKey` / `authToken` constructor options (either may be null).
    Static {
        api_key: Option<String>,
        auth_token: Option<String>,
    },
    /// `config` with OIDC workload identity federation (token cache).
    Federation(Arc<FederationAuth>),
}

/// A constructed SDK client (TS `new PiAnthropic({...})`).
#[derive(Clone)]
pub(crate) struct SdkClient {
    pub(crate) base_url: String,
    pub(crate) auth: ClientAuth,
    pub(crate) default_headers: ProviderHeaders,
    pub(crate) fetch: Option<FetchFunction>,
}

/// Per-request options (TS `{ signal, timeout, maxRetries: 0 }`).
#[derive(Default)]
pub(crate) struct RequestOptions {
    pub(crate) signal: Option<AbortSignal>,
    pub(crate) timeout_ms: Option<f64>,
}

static HTTP_CLIENT: LazyLock<reqwest::Client> = LazyLock::new(reqwest::Client::new);

fn auth_error_message() -> &'static str {
    "Could not resolve authentication method. Expected one of apiKey, authToken, credentials, config, or profile to be set. Or for one of the \"X-Api-Key\" or \"Authorization\" headers to be explicitly omitted"
}

/// TS `APIError.makeMessage`.
fn make_message(status: Option<u16>, error: Option<&JsonValue>, message: Option<&str>) -> String {
    let msg = match error {
        Some(error) => match error.get("message") {
            Some(JsonValue::String(text)) if !text.is_empty() => Some(text.clone()),
            Some(value) if is_truthy(value) => Some(json_stringify(value)),
            _ if is_truthy(error) => Some(json_stringify(error)),
            _ => message.map(str::to_owned),
        },
        None => message.map(str::to_owned),
    };
    let msg = msg.filter(|msg| !msg.is_empty());
    match (status, msg) {
        (Some(status), Some(msg)) => format!("{status} {msg}"),
        (Some(status), None) => format!("{status} status code (no body)"),
        (None, Some(msg)) => msg,
        (None, None) => "(no status code or body)".to_owned(),
    }
}

fn is_truthy(value: &JsonValue) -> bool {
    match value {
        JsonValue::Null => false,
        JsonValue::Bool(flag) => *flag,
        JsonValue::Number(number) => number.as_f64().is_some_and(|n| n != 0.0 && !n.is_nan()),
        JsonValue::String(text) => !text.is_empty(),
        JsonValue::Array(_) | JsonValue::Object(_) => true,
    }
}

/// An HTTP status error (TS `APIError.generate` for a status response).
pub(crate) fn status_error(status: u16, body: &str, headers: HeaderMap) -> Thrown {
    // TS `safeJSON(errText)`: parsed JSON, or the text as `message`.
    let parsed: Option<JsonValue> = serde_json::from_str(body).ok();
    let message = if parsed.is_some() { None } else { Some(body) };
    let text = make_message(Some(status), parsed.as_ref(), message);
    ErrorObject {
        status: Some(Some(JsonValue::from(status))),
        headers: Some(Some(headers)),
        ..ErrorObject::new(text)
    }
    .thrown()
}

/// An `APIError` without status or headers (`APIUserAbortError`,
/// `APIConnectionError`, `APIConnectionTimeoutError`).
fn statusless_error(message: &str) -> Thrown {
    ErrorObject {
        status: Some(None),
        headers: Some(None),
        ..ErrorObject::new(message)
    }
    .thrown()
}

pub(crate) const USER_ABORT_MESSAGE: &str = "Request was aborted.";
pub(crate) const CONNECTION_ERROR_MESSAGE: &str = "Connection error.";
pub(crate) const TIMEOUT_MESSAGE: &str = "Request timed out.";

/// Outcome of a messages request that failed, with what the eukhe
/// stream-failure diagnostic needs.
pub(crate) struct RequestFailure {
    pub(crate) thrown: Thrown,
    pub(crate) http: Option<(u16, String, HeaderMap)>,
    pub(crate) connection: Option<ConnectionFailure>,
}

/// A transport-level failure of the request.
pub(crate) struct ConnectionFailure {
    pub(crate) timeout: bool,
    pub(crate) cause: String,
}

impl RequestFailure {
    fn boxed(thrown: Thrown) -> Box<Self> {
        Box::new(Self {
            thrown,
            http: None,
            connection: None,
        })
    }
}

/// TS `transformOutputFormat`.
fn transform_output_format(params: JsonObject) -> Result<JsonObject, Thrown> {
    let Some(output_format) = params.get("output_format").filter(|value| is_truthy(value)) else {
        return Ok(params);
    };
    let output_format = output_format.clone();
    if params
        .get("output_config")
        .and_then(|config| config.get("format"))
        .is_some_and(is_truthy)
    {
        return Err(ErrorObject::new(
            "Both output_format and output_config.format were provided. Please use only output_config.format (output_format is deprecated).",
        )
        .thrown());
    }
    let mut output_config = match params.get("output_config") {
        Some(JsonValue::Object(config)) => config.clone(),
        _ => JsonObject::new(),
    };
    output_config.insert("format".into(), output_format);
    let mut rest: JsonObject = params
        .into_iter()
        .filter(|(key, _)| key != "output_format")
        .collect();
    rest.insert("output_config".into(), JsonValue::Object(output_config));
    Ok(rest)
}

impl SdkClient {
    /// TS `buildURL("/v1/messages?beta=true")`.
    fn messages_url(&self) -> String {
        let path = "/v1/messages?beta=true";
        if self.base_url.ends_with('/') {
            format!("{}{}", self.base_url, &path[1..])
        } else {
            format!("{}{path}", self.base_url)
        }
    }

    /// TS `client.beta.messages.create(params, options).asResponse()` for a
    /// streaming request with `maxRetries: 0`.
    #[allow(clippy::too_many_lines)] // One linear port of the SDK request path.
    pub(crate) async fn create_message_stream(
        &self,
        params: JsonObject,
        options: &RequestOptions,
    ) -> Result<reqwest::Response, Box<RequestFailure>> {
        let mut body = transform_output_format(params).map_err(RequestFailure::boxed)?;
        let betas = body.shift_remove("betas");
        let user_profile_id = body.shift_remove("user_profile_id");
        let workspace_id = body.shift_remove("workspace_id");
        let timeout_ms = options.timeout_ms.unwrap_or(DEFAULT_TIMEOUT_MS);

        let mut headers = HeaderBag::default();
        headers.set("Accept", Some("application/json"));
        headers.set("User-Agent", Some(&format!("Anthropic/JS {SDK_VERSION}")));
        headers.set("anthropic-dangerous-direct-browser-access", Some("true"));
        headers.set("anthropic-version", Some("2023-06-01"));
        let mut used_token_cache = false;
        match &self.auth {
            ClientAuth::Static {
                api_key,
                auth_token,
            } => {
                if let Some(api_key) = api_key {
                    headers.set("X-Api-Key", Some(api_key));
                }
                if let Some(auth_token) = auth_token {
                    headers.set("Authorization", Some(&format!("Bearer {auth_token}")));
                }
            }
            ClientAuth::Federation(federation) => {
                let token = federation
                    .get_token(self.fetch.as_ref())
                    .await
                    .map_err(RequestFailure::boxed)?;
                used_token_cache = true;
                headers.set("Authorization", Some(&format!("Bearer {token}")));
            }
        }
        headers.apply(&self.default_headers);
        headers.set("content-type", Some("application/json"));
        if let Some(betas) = betas.as_ref().filter(|betas| !betas.is_null()) {
            headers.set("anthropic-beta", Some(&js_to_string(betas)));
        }
        if let Some(id) = user_profile_id.filter(|id| !id.is_null()) {
            headers.set("anthropic-user-profile-id", Some(&js_to_string(&id)));
        }
        if let Some(id) = workspace_id.filter(|id| !id.is_null()) {
            headers.set("anthropic-workspace-id", Some(&js_to_string(&id)));
        }
        // TS `validateHeaders`.
        let federated = matches!(self.auth, ClientAuth::Federation(_));
        if headers.get("x-api-key").is_none_or(str::is_empty)
            && headers.get("authorization").is_none_or(str::is_empty)
            && !federated
            && !headers.nulls.contains("x-api-key")
            && !headers.nulls.contains("authorization")
        {
            return Err(RequestFailure::boxed(
                ErrorObject::new(auth_error_message()).thrown(),
            ));
        }

        if options.signal.as_ref().is_some_and(AbortSignal::aborted) {
            return Err(RequestFailure::boxed(statusless_error(USER_ABORT_MESSAGE)));
        }

        let request = self
            .build_request(&headers, &JsonValue::Object(body))
            .map_err(RequestFailure::boxed)?;
        let response = self
            .send(request, timeout_ms, options.signal.as_ref())
            .await;
        let response = match response {
            Ok(response) => response,
            Err(SendError::Aborted) => {
                return Err(RequestFailure::boxed(statusless_error(USER_ABORT_MESSAGE)));
            }
            Err(SendError::Failed { timeout, cause }) => {
                if options.signal.as_ref().is_some_and(AbortSignal::aborted) {
                    return Err(RequestFailure::boxed(statusless_error(USER_ABORT_MESSAGE)));
                }
                let message = if timeout {
                    TIMEOUT_MESSAGE
                } else {
                    CONNECTION_ERROR_MESSAGE
                };
                return Err(Box::new(RequestFailure {
                    thrown: statusless_error(message),
                    http: None,
                    connection: Some(ConnectionFailure { timeout, cause }),
                }));
            }
        };
        let status = response.status().as_u16();
        if response.status().is_success() {
            return Ok(response);
        }
        // TS `shouldRetry`: a 401 on a token-cache request invalidates the
        // cached token even though no retry follows (`maxRetries: 0`).
        if status == 401 && used_token_cache {
            if let ClientAuth::Federation(federation) = &self.auth {
                federation.invalidate();
            }
        }
        let response_headers = response.headers().clone();
        let text = match response.text().await {
            Ok(text) => text,
            Err(error) => error.to_string(),
        };
        Err(Box::new(RequestFailure {
            thrown: status_error(status, &text, response_headers.clone()),
            http: Some((status, text, response_headers)),
            connection: None,
        }))
    }

    fn build_request(
        &self,
        headers: &HeaderBag,
        body: &JsonValue,
    ) -> Result<reqwest::Request, Thrown> {
        let url = reqwest::Url::parse(&self.messages_url())
            .map_err(|_| ErrorObject::named("TypeError", "Invalid URL").thrown())?;
        let mut request = reqwest::Request::new(reqwest::Method::POST, url);
        let map = request.headers_mut();
        for (name, value) in headers.values() {
            let name = HeaderName::from_bytes(name.as_bytes())
                .map_err(|error| ErrorObject::named("TypeError", error.to_string()).thrown())?;
            let value = HeaderValue::from_str(value)
                .map_err(|error| ErrorObject::named("TypeError", error.to_string()).thrown())?;
            map.insert(name, value);
        }
        *request.body_mut() = Some(json_stringify(body).into());
        Ok(request)
    }

    async fn send(
        &self,
        request: reqwest::Request,
        timeout_ms: f64,
        signal: Option<&AbortSignal>,
    ) -> Result<reqwest::Response, SendError> {
        let fetch = self.fetch.clone();
        let call = async move {
            match fetch {
                Some(fetch) => fetch(request).await.map_err(|error| {
                    let text = error.to_string();
                    SendError::Failed {
                        timeout: is_timeout_text(&text),
                        cause: text,
                    }
                }),
                None => HTTP_CLIENT
                    .execute(request)
                    .await
                    .map_err(|error| SendError::Failed {
                        timeout: error.is_timeout() || is_timeout_text(&format!("{error:?}")),
                        cause: error.to_string(),
                    }),
            }
        };
        // Timeout covers the fetch until headers arrive (TS `timedFetch`).
        let timeout = Duration::from_secs_f64(timeout_ms.max(0.0) / 1000.0);
        let timed = async move {
            match tokio::time::timeout(timeout, call).await {
                Ok(result) => result,
                Err(_) => Err(SendError::Failed {
                    timeout: true,
                    cause: "The operation was aborted due to timeout".to_owned(),
                }),
            }
        };
        match signal {
            Some(signal) => {
                let token = signal.cancellation_token();
                tokio::select! {
                    result = timed => result,
                    () = token.cancelled() => Err(SendError::Aborted),
                }
            }
            None => timed.await,
        }
    }
}

enum SendError {
    Aborted,
    Failed { timeout: bool, cause: String },
}

/// TS `/timed? ?out/i` over the error and its cause.
fn is_timeout_text(text: &str) -> bool {
    static TIMEOUT: LazyLock<regex::Regex> =
        LazyLock::new(|| regex::Regex::new("(?i)timed? ?out").expect("valid regex"));
    TIMEOUT.is_match(text)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn make_message_matches_sdk() {
        assert_eq!(
            make_message(
                Some(400),
                Some(&json!({"type": "error", "error": {"message": "bad"}})),
                None
            ),
            "400 {\"type\":\"error\",\"error\":{\"message\":\"bad\"}}"
        );
        assert_eq!(
            make_message(Some(400), Some(&json!({"message": "top"})), None),
            "400 top"
        );
        assert_eq!(make_message(Some(500), None, Some("oops")), "500 oops");
        assert_eq!(
            make_message(Some(429), None, Some("")),
            "429 status code (no body)"
        );
        assert_eq!(make_message(None, None, None), "(no status code or body)");
    }

    #[test]
    fn header_bag_null_removes_and_records() {
        let mut bag = HeaderBag::default();
        bag.set("X-Api-Key", Some("k"));
        bag.set("x-api-key", None);
        assert!(bag.get("x-api-key").is_none());
        assert!(bag.nulls.contains("x-api-key"));
        bag.set("Accept", Some("a"));
        bag.set("ACCEPT", Some("b"));
        assert_eq!(bag.get("accept"), Some("b"));
    }
}
