//! Codex error classes, retry classification, and the error-body parser.
//! Section of the port of `api/openai-codex-responses.ts`.

use std::sync::LazyLock;

use eukhe_types::pi_ai::{DiagnosticCode, JsonValue};
use regex::Regex;
use reqwest::header::HeaderMap;

use crate::utils::diagnostics::{
    error_name, format_thrown_value, ErrorObject, Thrown, ThrownValue,
};
use crate::utils::js::{js_to_string, js_trim, number_to_js_string};
use crate::utils::provider_retry::parse_http_date;
use crate::utils::stream_failure::{ProviderError, ProviderHttpError, ProviderWsTransportError};

use super::{clock_ms, DEFAULT_MAX_RETRY_DELAY_MS};

/// TS `CodexApiError.name`.
pub(crate) const CODEX_API_ERROR: &str = "CodexApiError";
/// TS `CodexProtocolError.name`.
pub(crate) const CODEX_PROTOCOL_ERROR: &str = "CodexProtocolError";
/// TS `ProviderStreamEventCallbackError.name`.
pub(crate) const PROVIDER_STREAM_EVENT_CALLBACK_ERROR: &str = "ProviderStreamEventCallbackError";
/// TS `WebSocketCloseError.name`.
pub(crate) const WEBSOCKET_CLOSE_ERROR: &str = "WebSocketCloseError";

const WEBSOCKET_CONNECTION_LIMIT_REACHED_CODE: &str = "websocket_connection_limit_reached";
const PREVIOUS_RESPONSE_NOT_FOUND_CODE: &str = "previous_response_not_found";
const WEBSOCKET_MESSAGE_TOO_BIG_CLOSE_CODE: u16 = 1009;

/// The message of every abort the Codex stream raises.
pub(crate) const REQUEST_ABORTED: &str = "Request was aborted";

/// `new Error("Request was aborted")`.
pub(crate) fn aborted_error() -> Thrown {
    ErrorObject::new(REQUEST_ABORTED).thrown()
}

/// TS `new CodexApiError(message, { code, payload })`. The payload is kept
/// by TS for debugging only and never read, so it is not carried.
pub(crate) fn codex_api_error(message: String, code: Option<String>) -> Thrown {
    let error = ErrorObject::named(CODEX_API_ERROR, message);
    match code {
        Some(code) => error.with_code(DiagnosticCode::String(code)),
        None => error,
    }
    .thrown()
}

/// TS `new CodexProtocolError(message, { cause, payload })`.
pub(crate) fn codex_protocol_error(message: String) -> Thrown {
    ErrorObject::named(CODEX_PROTOCOL_ERROR, message).thrown()
}

/// TS `new ProviderStreamEventCallbackError(cause)`.
pub(crate) fn provider_stream_event_callback_error(cause: &Thrown) -> Thrown {
    ErrorObject::named(
        PROVIDER_STREAM_EVENT_CALLBACK_ERROR,
        format_thrown_value(cause),
    )
    .thrown()
}

/// TS `new WebSocketCloseError(message, { code, reason, wasClean })`; the
/// numeric close code is the error's `code`.
pub(crate) fn websocket_close_error(message: String, code: Option<u16>) -> Thrown {
    let error = ErrorObject::named(WEBSOCKET_CLOSE_ERROR, message);
    match code {
        Some(code) => error.with_code(DiagnosticCode::Number(f64::from(code))),
        None => error,
    }
    .thrown()
}

fn codex_error_code<'a>(error: &'a Thrown, name: &str) -> Option<&'a str> {
    let object = error.downcast_ref::<ErrorObject>()?;
    if object.name != name {
        return None;
    }
    match &object.code {
        Some(DiagnosticCode::String(code)) => Some(code),
        Some(DiagnosticCode::Number(_)) | None => None,
    }
}

fn has_error_name(error: &Thrown, name: &str) -> bool {
    error
        .downcast_ref::<ErrorObject>()
        .is_some_and(|object| object.name == name)
}

/// TS `isCodexNonTransportError`.
pub(crate) fn is_codex_non_transport_error(error: &Thrown) -> bool {
    has_error_name(error, CODEX_API_ERROR)
        || has_error_name(error, CODEX_PROTOCOL_ERROR)
        || has_error_name(error, PROVIDER_STREAM_EVENT_CALLBACK_ERROR)
}

/// TS `isWebSocketConnectionLimitReachedError`.
pub(crate) fn is_websocket_connection_limit_reached_error(error: &Thrown) -> bool {
    codex_error_code(error, CODEX_API_ERROR) == Some(WEBSOCKET_CONNECTION_LIMIT_REACHED_CODE)
}

/// TS `isPreviousResponseNotFoundError`.
pub(crate) fn is_previous_response_not_found_error(error: &Thrown) -> bool {
    codex_error_code(error, CODEX_API_ERROR) == Some(PREVIOUS_RESPONSE_NOT_FOUND_CODE)
}

/// TS `extractWebSocketError`: the event's (or its nested error's) message.
pub(crate) fn extract_websocket_error(message: Option<&str>) -> Thrown {
    match message.filter(|message| !message.is_empty()) {
        Some(message) => ErrorObject::new(message).thrown(),
        None => ErrorObject::new("WebSocket error").thrown(),
    }
}

/// TS `extractWebSocketCloseError` for a close event.
pub(crate) fn extract_websocket_close_error(code: Option<u16>, reason: Option<&str>) -> Thrown {
    let code_text = code.map_or_else(String::new, |code| format!(" {code}"));
    let reason = reason.filter(|reason| !reason.is_empty());
    let reason_text = match reason {
        Some(reason) => format!(" {reason}"),
        None if code == Some(WEBSOCKET_MESSAGE_TOO_BIG_CLOSE_CODE) => " message too big".to_owned(),
        None => String::new(),
    };
    let message = format!("WebSocket closed{code_text}{reason_text}");
    websocket_close_error(js_trim(&message).to_owned(), code)
}

// ---------------------------------------------------------------------------
// Retry helpers
// ---------------------------------------------------------------------------

/// A JS regex `.`: any code point but a line terminator.
const JS_DOT: &str = r"[^\n\r\u{2028}\u{2029}]";

static TERMINAL_RATE_LIMIT: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(
        "(?i)GoUsageLimitError|FreeUsageLimitError|Monthly usage limit reached|available balance|insufficient_quota|out of budget|quota exceeded|billing",
    )
    .expect("static regex")
});

static RETRYABLE_TEXT: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(&format!(
        "(?i)rate{JS_DOT}?limit|overloaded|service{JS_DOT}?unavailable|upstream{JS_DOT}?connect|connection{JS_DOT}?refused"
    ))
    .expect("static regex")
});

static USAGE_LIMIT_CODE: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new("(?i)usage_limit_reached|usage_not_included|rate_limit_exceeded")
        .expect("static regex")
});

/// TS `isTerminalRateLimitError`.
fn is_terminal_rate_limit_error(error_text: &str) -> bool {
    TERMINAL_RATE_LIMIT.is_match(error_text)
}

/// TS `isRetryableError`.
pub(crate) fn is_retryable_error(status: u16, error_text: &str) -> bool {
    if status == 429 && is_terminal_rate_limit_error(error_text) {
        return false;
    }
    if matches!(status, 429 | 500 | 502 | 503 | 504) {
        return true;
    }
    RETRYABLE_TEXT.is_match(error_text)
}

/// JS `Number(string)`: whitespace-trimmed decimal, `Infinity`, or
/// `0x`/`0o`/`0b` integer literal; the empty string is `0`; anything else
/// is `NaN`.
pub(crate) fn js_number(text: &str) -> f64 {
    let text = js_trim(text);
    if text.is_empty() {
        return 0.0;
    }
    let (sign, unsigned) = match text.as_bytes()[0] {
        b'+' => (1.0, &text[1..]),
        b'-' => (-1.0, &text[1..]),
        _ => (1.0, text),
    };
    if unsigned == "Infinity" {
        return sign * f64::INFINITY;
    }
    for (prefix, radix) in [
        ("0x", 16),
        ("0X", 16),
        ("0o", 8),
        ("0O", 8),
        ("0b", 2),
        ("0B", 2),
    ] {
        if let Some(digits) = text.strip_prefix(prefix) {
            if digits.is_empty() || !digits.chars().all(|c| c.is_digit(radix)) {
                return f64::NAN;
            }
            return digits
                .chars()
                .filter_map(|c| c.to_digit(radix))
                .fold(0.0, |value, digit| {
                    value * f64::from(radix) + f64::from(digit)
                });
        }
    }
    let decimal = unsigned
        .bytes()
        .all(|byte| byte.is_ascii_digit() || matches!(byte, b'.' | b'e' | b'E' | b'+' | b'-'))
        && unsigned.bytes().any(|byte| byte.is_ascii_digit());
    if !decimal {
        return f64::NAN;
    }
    text.parse::<f64>().unwrap_or(f64::NAN)
}

fn header<'a>(headers: &'a HeaderMap, name: &str) -> Option<&'a str> {
    headers.get(name).and_then(|value| value.to_str().ok())
}

/// TS `getRetryAfterDelayMs`.
pub(crate) fn get_retry_after_delay_ms(headers: &HeaderMap) -> Option<f64> {
    if let Some(retry_after_ms) = header(headers, "retry-after-ms") {
        let millis = js_number(retry_after_ms);
        if millis.is_finite() {
            return Some(millis.max(0.0));
        }
    }

    let retry_after = header(headers, "retry-after").filter(|value| !value.is_empty())?;

    let seconds = js_number(retry_after);
    if seconds.is_finite() {
        return Some((seconds * 1000.0).max(0.0));
    }

    // `Date.parse(retryAfter) - Date.now()`.
    parse_http_date(retry_after).map(|date| (date - clock_ms()).max(0.0))
}

/// TS `RetryDelayExceededError`: a plain `Error` subclass (its `name` stays
/// `Error`) that stops the retry loop.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("{0}")]
pub(crate) struct RetryDelayExceededError(pub String);

/// TS `validateRetryDelayMs`.
pub(crate) fn validate_retry_delay_ms(
    delay_ms: f64,
    max_retry_delay_ms: Option<f64>,
) -> Result<f64, Thrown> {
    let max_retry_delay_ms = max_retry_delay_ms.unwrap_or(DEFAULT_MAX_RETRY_DELAY_MS);
    if max_retry_delay_ms > 0.0 && delay_ms > max_retry_delay_ms {
        return Err(crate::utils::diagnostics::thrown(RetryDelayExceededError(
            format!(
                "Server requested {}s retry delay (max: {}s)",
                number_to_js_string((delay_ms / 1000.0).ceil()),
                number_to_js_string((max_retry_delay_ms / 1000.0).ceil()),
            ),
        )));
    }
    Ok(delay_ms)
}

/// Whether `error` is an abort: TS `error.name === "AbortError" ||
/// error.message === "Request was aborted"`.
pub(crate) fn is_abort_error(error: &Thrown) -> bool {
    if error.is::<ThrownValue>() {
        return false;
    }
    error_name(error.as_ref()) == "AbortError" || error.to_string() == REQUEST_ABORTED
}

// ---------------------------------------------------------------------------
// Error body
// ---------------------------------------------------------------------------

/// TS `parseErrorResponse` result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ErrorResponseInfo {
    pub message: String,
    pub friendly_message: Option<String>,
    /// eukhe addition: the error's `code || type` for the stream-failure
    /// diagnostic.
    pub code: Option<String>,
}

/// JS truthiness of a JSON value.
fn truthy(value: &JsonValue) -> bool {
    match value {
        JsonValue::Null => false,
        JsonValue::Bool(flag) => *flag,
        JsonValue::Number(number) => number
            .as_f64()
            .is_some_and(|number| number != 0.0 && !number.is_nan()),
        JsonValue::String(text) => !text.is_empty(),
        JsonValue::Array(_) | JsonValue::Object(_) => true,
    }
}

/// `a || b` over optional JSON values (missing = `undefined`).
fn or_value<'a>(
    left: Option<&'a JsonValue>,
    right: Option<&'a JsonValue>,
) -> Option<&'a JsonValue> {
    match left {
        Some(value) if truthy(value) => Some(value),
        _ => right,
    }
}

/// `Math.round`.
fn js_round(value: f64) -> f64 {
    (value + 0.5).floor()
}

/// TS `parseErrorResponse` over the already-read body text. `status_text`
/// is the response's `statusText`.
pub(crate) fn parse_error_response(raw: &str, status: u16, status_text: &str) -> ErrorResponseInfo {
    let mut message = if !raw.is_empty() {
        raw.to_owned()
    } else if !status_text.is_empty() {
        status_text.to_owned()
    } else {
        "Request failed".to_owned()
    };
    let mut friendly_message = None;
    let mut code_text = None;

    if let Ok(parsed) = serde_json::from_str::<JsonValue>(raw) {
        let err = parsed
            .as_object()
            .and_then(|object| object.get("error"))
            .filter(|err| truthy(err));
        if let Some(err) = err {
            let field = |name: &str| err.as_object().and_then(|object| object.get(name));
            let code =
                or_value(field("code"), field("type")).map_or_else(String::new, js_to_string);
            if USAGE_LIMIT_CODE.is_match(&code) || status == 429 {
                let plan = field("plan_type")
                    .filter(|plan| truthy(plan))
                    .map_or_else(String::new, |plan| {
                        format!(" ({} plan)", js_to_string(plan).to_lowercase())
                    });
                let mins = field("resets_at")
                    .filter(|resets_at| truthy(resets_at))
                    .and_then(JsonValue::as_f64)
                    .map(|resets_at| {
                        js_round((resets_at * 1000.0 - clock_ms()) / 60000.0).max(0.0)
                    });
                let when = mins.map_or_else(String::new, |mins| {
                    format!(" Try again in ~{} min.", number_to_js_string(mins))
                });
                friendly_message = Some(
                    js_trim(&format!(
                        "You have hit your ChatGPT usage limit{plan}.{when}"
                    ))
                    .to_owned(),
                );
            }
            message = match field("message").filter(|value| truthy(value)) {
                Some(value) => js_to_string(value),
                None => friendly_message.clone().unwrap_or(message),
            };
            code_text = Some(code).filter(|code| !code.is_empty());
        }
    }

    ErrorResponseInfo {
        message,
        friendly_message,
        code: code_text,
    }
}

/// eukhe addition: the final SSE HTTP failure. TS throws a plain `Error`
/// with the friendly (or parsed) message; the status, wire code, and retry
/// delay ride along for the stream-failure diagnostic.
#[derive(Debug, Clone, PartialEq, thiserror::Error)]
#[error("{message}")]
pub(crate) struct CodexHttpError {
    pub message: String,
    pub status: u16,
    pub code: Option<String>,
    pub retry_after_ms: Option<f64>,
}

/// eukhe addition: classify a terminal Codex error for
/// [`crate::utils::stream_failure::record_stream_failure`], like the old
/// eukhe port (`CodexApiError`/`CodexProtocolError` as HTTP errors with
/// their class name, WebSocket close errors as transport failures).
pub(crate) fn to_provider_error(error: &Thrown, aborted: bool) -> ProviderError {
    if aborted {
        return ProviderError::Aborted;
    }
    if let Some(provider_error) = error.downcast_ref::<ProviderError>() {
        return provider_error.clone();
    }
    if let Some(http) = error.downcast_ref::<CodexHttpError>() {
        return ProviderError::Http(ProviderHttpError {
            message: http.message.clone(),
            status: Some(http.status),
            body: None,
            headers: std::collections::HashMap::new(),
            request_id: None,
            sdk_name: Some(CODEX_API_ERROR.to_owned()),
            // A finite, non-negative millisecond delay; whole milliseconds are the unit.
            #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
            retry_after_ms: http.retry_after_ms.map(|ms| ms as u64),
            provider_error_type: http.code.clone(),
        });
    }
    if let Some(object) = error.downcast_ref::<ErrorObject>() {
        match object.name.as_str() {
            CODEX_API_ERROR | CODEX_PROTOCOL_ERROR => {
                return ProviderError::Http(ProviderHttpError {
                    message: object.message.clone(),
                    status: None,
                    body: None,
                    headers: std::collections::HashMap::new(),
                    request_id: None,
                    sdk_name: Some(object.name.clone()),
                    retry_after_ms: None,
                    provider_error_type: match &object.code {
                        Some(DiagnosticCode::String(code)) => Some(code.clone()),
                        Some(DiagnosticCode::Number(_)) | None => None,
                    },
                });
            }
            WEBSOCKET_CLOSE_ERROR => {
                return ProviderError::Transport(ProviderWsTransportError {
                    message: object.message.clone(),
                    close_code: match object.code {
                        // Close codes are u16 by construction.
                        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                        Some(DiagnosticCode::Number(code)) => Some(code as u16),
                        Some(DiagnosticCode::String(_)) | None => None,
                    },
                });
            }
            _ => {}
        }
    }
    ProviderError::Message(format_thrown_value(error))
}
