//! HTTP transport of the Mistral chat API: request headers, the streaming
//! `POST /v1/chat/completions` call, and the SSE event reader. Section of the
//! port of `api/mistral-conversations.ts`.

use std::sync::LazyLock;

use eukhe_chord::context::AbortSignal;
use eukhe_types::pi_ai::{JsonValue, Model, ProviderHeaders, ProviderResponse};
use futures::future::BoxFuture;
use regex::Regex;
use reqwest::header::{HeaderMap, HeaderName, HeaderValue};

use super::{type_error, MistralFailure, MistralOptions};
use crate::auth::errors::js_error;
use crate::utils::diagnostics::{ErrorObject, Thrown};
use crate::utils::headers::headers_to_record;
use crate::utils::js::{is_js_whitespace, js_trim, json_stringify, number_to_js_string};
use crate::utils::json_parse::js_json_parse;
use crate::utils::pi_user_agent::get_pi_user_agent;
use crate::utils::sleep::timer_duration;

/// Default request timeout (TS `options?.timeoutMs ?? 60_000`).
const DEFAULT_TIMEOUT_MS: f64 = 60_000.0;

/// The process-wide client behind the default `fetch` (TS `globalThis.fetch`).
static CLIENT: LazyLock<reqwest::Client> = LazyLock::new(reqwest::Client::new);

/// TS `globalThis.fetch` for a prepared request.
fn default_fetch(
    request: reqwest::Request,
) -> BoxFuture<'static, Result<reqwest::Response, Thrown>> {
    Box::pin(async move {
        CLIENT
            .execute(request)
            .await
            .map_err(|error| type_error(&format!("fetch failed: {error}")))
    })
}

/// TS `requestMistralStream`: sends the request and returns the SSE event
/// reader. Fails with [`MistralFailure::Http`] on a non-2xx response.
pub(super) async fn request_mistral_stream(
    model: &Model,
    wire_payload: &JsonValue,
    api_key: &str,
    options: &MistralOptions,
) -> Result<MistralEventReader, MistralFailure> {
    let url = chat_completions_url(&model.base_url)?;
    let headers = build_mistral_headers(model, api_key, options)?;
    // The timeout covers only the wait for response headers. Long streams (e.g. extended thinking)
    // must not be cut off by a fixed deadline; body stalls are left to the HTTP client idle timeout.
    let timeout_ms = options
        .stream
        .request
        .timeout_ms
        .unwrap_or(DEFAULT_TIMEOUT_MS);
    let signal = options.stream.request.signal.clone();

    let mut request = reqwest::Request::new(reqwest::Method::POST, url);
    *request.headers_mut() = headers;
    *request.body_mut() = Some(json_stringify(wire_payload).into());

    if let Some(signal) = &signal {
        signal.throw_if_aborted().map_err(MistralFailure::Thrown)?;
    }
    let exchange = match &options.stream.request.fetch {
        Some(fetch) => fetch(request),
        None => default_fetch(request),
    };
    let aborted = async {
        match &signal {
            Some(signal) => signal.cancelled().await,
            None => std::future::pending().await,
        }
    };
    let response = tokio::select! {
        biased;
        reason = aborted => return Err(MistralFailure::Thrown(reason)),
        () = tokio::time::sleep(timer_duration(timeout_ms)) => {
            return Err(MistralFailure::Thrown(js_error(format!(
                "Mistral response headers timed out after {}ms",
                number_to_js_string(timeout_ms)
            ))));
        }
        response = exchange => response.map_err(MistralFailure::Thrown)?,
    };

    if let Some(on_response) = &options.stream.request.on_response {
        on_response(
            ProviderResponse {
                status: response.status().as_u16(),
                headers: headers_to_record(response.headers()),
            },
            model,
        )
        .await
        .map_err(MistralFailure::Thrown)?;
    }

    let status = response.status();
    if !status.is_success() {
        let headers = response
            .headers()
            .iter()
            .map(|(name, value)| {
                (
                    name.as_str().to_owned(),
                    String::from_utf8_lossy(value.as_bytes()).into_owned(),
                )
            })
            .collect();
        let body = response
            .text()
            .await
            .map_err(|error| MistralFailure::Thrown(type_error(&format!("terminated: {error}"))))?;
        return Err(MistralFailure::Http {
            status: status.as_u16(),
            body,
            status_text: status.canonical_reason().unwrap_or_default().to_owned(),
            headers,
        });
    }

    Ok(MistralEventReader::new(response, signal))
}

/// `new URL("v1/chat/completions", baseUrl)` with the base path forced to
/// end in exactly one `/`.
fn chat_completions_url(base_url: &str) -> Result<reqwest::Url, MistralFailure> {
    let invalid = || MistralFailure::Thrown(type_error("Invalid URL"));
    let mut base = reqwest::Url::parse(base_url).map_err(|_| invalid())?;
    let path = format!("{}/", base.path().trim_end_matches('/'));
    base.set_path(&path);
    base.join("v1/chat/completions").map_err(|_| invalid())
}

fn header_name(name: &str) -> Result<HeaderName, MistralFailure> {
    HeaderName::from_bytes(name.as_bytes()).map_err(|_| {
        MistralFailure::Thrown(type_error(&format!(
            "Headers.set: \"{name}\" is an invalid header name."
        )))
    })
}

fn set_header(headers: &mut HeaderMap, name: &str, value: &str) -> Result<(), MistralFailure> {
    let header = header_name(name)?;
    // `Headers.set` normalizes the value by stripping leading and trailing
    // HTTP whitespace.
    let trimmed = value.trim_matches([' ', '\t', '\n', '\r']);
    let value = HeaderValue::from_str(trimmed).map_err(|_| {
        MistralFailure::Thrown(type_error(&format!(
            "Headers.set: \"{trimmed}\" is an invalid header value."
        )))
    })?;
    headers.insert(header, value);
    Ok(())
}

/// TS `buildMistralHeaders`.
fn build_mistral_headers(
    model: &Model,
    api_key: &str,
    options: &MistralOptions,
) -> Result<HeaderMap, MistralFailure> {
    let mut headers = HeaderMap::new();
    set_header(&mut headers, "User-Agent", get_pi_user_agent())?;
    set_header(&mut headers, "accept", "text/event-stream")?;
    set_header(&mut headers, "authorization", &format!("Bearer {api_key}"))?;
    set_header(&mut headers, "content-type", "application/json")?;
    if let Some(model_headers) = &model.headers {
        for (name, value) in model_headers {
            set_header(&mut headers, name, value)?;
        }
    }
    apply_header_overrides(&mut headers, options.stream.request.headers.as_ref())?;

    let has_explicit_affinity =
        model.headers.as_ref().is_some_and(|headers| {
            headers
                .keys()
                .any(|name| name.to_lowercase() == "x-affinity")
        }) || has_header_override(options.stream.request.headers.as_ref(), "x-affinity");
    if let Some(session_id) = options.prompt_cache_session_id() {
        if !has_explicit_affinity {
            set_header(&mut headers, "x-affinity", session_id)?;
        }
    }
    Ok(headers)
}

/// TS `applyMistralHeaderOverrides`.
fn apply_header_overrides(
    headers: &mut HeaderMap,
    overrides: Option<&ProviderHeaders>,
) -> Result<(), MistralFailure> {
    for (name, value) in overrides.into_iter().flatten() {
        match value {
            None => {
                headers.remove(header_name(name)?);
            }
            Some(value) => set_header(headers, name, value)?,
        }
    }
    Ok(())
}

/// TS `hasMistralHeaderOverride`.
fn has_header_override(overrides: Option<&ProviderHeaders>, target: &str) -> bool {
    overrides.is_some_and(|overrides| overrides.keys().any(|name| name.to_lowercase() == target))
}

/// TS `findMistralEventBoundary`.
static EVENT_BOUNDARY: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"\r\n\r\n|\r\n\r|\r\n\n|\r\r\n|\n\r\n|\r\r|\n\r|\n\n").expect("valid regex")
});

/// TS `/\r\n|\r|\n/u`.
static LINE_BREAK: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"\r\n|\r|\n").expect("valid regex"));

/// What one raw SSE event holds (TS `parseMistralEvent` result).
enum ParsedEvent {
    Event(JsonValue),
    Done,
    Empty,
}

/// TS `parseMistralEvent`.
fn parse_mistral_event(raw: &str) -> Result<ParsedEvent, Thrown> {
    let data = LINE_BREAK
        .split(raw)
        .filter_map(|line| line.strip_prefix("data:"))
        .map(|line| line.trim_start_matches(is_js_whitespace))
        .collect::<Vec<_>>()
        .join("\n");
    let data = js_trim(&data);
    if data.is_empty() {
        return Ok(ParsedEvent::Empty);
    }
    if data == "[DONE]" {
        return Ok(ParsedEvent::Done);
    }
    let parsed = js_json_parse(data)
        .map_err(|error| ErrorObject::named("SyntaxError", error.message).thrown())?;
    if !parsed
        .as_object()
        .is_some_and(|object| object.get("choices").is_some_and(JsonValue::is_array))
    {
        return Err(js_error("Invalid Mistral streaming event"));
    }
    Ok(ParsedEvent::Event(parsed))
}

/// Incremental UTF-8 decoding (TS `TextDecoder` with `{ stream: true }`):
/// invalid sequences become U+FFFD, an incomplete trailing sequence waits
/// for the next chunk.
#[derive(Default)]
struct Utf8Decoder {
    pending: Vec<u8>,
}

impl Utf8Decoder {
    fn decode(&mut self, bytes: &[u8], out: &mut String) {
        self.pending.extend_from_slice(bytes);
        let mut rest: &[u8] = &self.pending;
        loop {
            match std::str::from_utf8(rest) {
                Ok(text) => {
                    out.push_str(text);
                    rest = &[];
                    break;
                }
                Err(error) => {
                    let (valid, after) = rest.split_at(error.valid_up_to());
                    out.push_str(std::str::from_utf8(valid).unwrap_or_default());
                    let Some(length) = error.error_len() else {
                        rest = after;
                        break;
                    };
                    out.push('\u{FFFD}');
                    rest = &after[length..];
                }
            }
        }
        self.pending = rest.to_vec();
    }

    /// `decoder.decode()`: flush an incomplete trailing sequence.
    fn finish(&mut self, out: &mut String) {
        if !self.pending.is_empty() {
            out.push_str(&String::from_utf8_lossy(&self.pending));
            self.pending.clear();
        }
    }
}

/// TS `readMistralEvents`: the SSE events of a streaming response. Reading
/// fails with the signal's reason once the caller's signal aborts.
pub(super) struct MistralEventReader {
    response: reqwest::Response,
    signal: Option<AbortSignal>,
    decoder: Utf8Decoder,
    buffer: String,
    body_done: bool,
    finished: bool,
}

impl MistralEventReader {
    fn new(response: reqwest::Response, signal: Option<AbortSignal>) -> Self {
        Self {
            response,
            signal,
            decoder: Utf8Decoder::default(),
            buffer: String::new(),
            body_done: false,
            finished: false,
        }
    }

    /// The next parsed event, `None` at `[DONE]` or the end of the body.
    pub(super) async fn next_event(&mut self) -> Result<Option<JsonValue>, Thrown> {
        if self.finished {
            return Ok(None);
        }
        loop {
            while let Some(boundary) = EVENT_BOUNDARY.find(&self.buffer) {
                let raw = self.buffer[..boundary.start()].to_owned();
                self.buffer.drain(..boundary.end());
                match parse_mistral_event(&raw)? {
                    ParsedEvent::Done => {
                        self.finished = true;
                        return Ok(None);
                    }
                    ParsedEvent::Event(event) => return Ok(Some(event)),
                    ParsedEvent::Empty => {}
                }
            }
            if self.body_done {
                self.finished = true;
                if js_trim(&self.buffer).is_empty() {
                    return Ok(None);
                }
                let raw = std::mem::take(&mut self.buffer);
                return match parse_mistral_event(&raw)? {
                    ParsedEvent::Event(event) => Ok(Some(event)),
                    ParsedEvent::Done | ParsedEvent::Empty => Ok(None),
                };
            }
            if let Some(signal) = &self.signal {
                signal.throw_if_aborted()?;
            }
            let signal = self.signal.clone();
            let aborted = async {
                match &signal {
                    Some(signal) => signal.cancelled().await,
                    None => std::future::pending().await,
                }
            };
            let chunk = tokio::select! {
                reason = aborted => return Err(reason),
                chunk = self.response.chunk() => chunk
                    .map_err(|error| type_error(&format!("terminated: {error}")))?,
            };
            if let Some(signal) = &self.signal {
                signal.throw_if_aborted()?;
            }
            if let Some(bytes) = chunk {
                self.decoder.decode(&bytes, &mut self.buffer);
            } else {
                self.decoder.finish(&mut self.buffer);
                self.body_done = true;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decoder_joins_split_sequences() {
        let bytes = "héllo 🌍".as_bytes();
        let mut decoder = Utf8Decoder::default();
        let mut out = String::new();
        for byte in bytes {
            decoder.decode(std::slice::from_ref(byte), &mut out);
        }
        decoder.finish(&mut out);
        assert_eq!(out, "héllo 🌍");
    }

    #[test]
    fn decoder_replaces_invalid_bytes() {
        let mut decoder = Utf8Decoder::default();
        let mut out = String::new();
        decoder.decode(&[b'a', 0xFF, b'b', 0xE2, 0x82], &mut out);
        decoder.finish(&mut out);
        assert_eq!(out, "a\u{FFFD}b\u{FFFD}");
    }

    #[test]
    fn url_keeps_base_path() {
        assert_eq!(
            chat_completions_url("https://api.mistral.ai")
                .ok()
                .map(String::from),
            Some("https://api.mistral.ai/v1/chat/completions".to_owned())
        );
        assert_eq!(
            chat_completions_url("http://host/proxy//")
                .ok()
                .map(String::from),
            Some("http://host/proxy/v1/chat/completions".to_owned())
        );
    }
}
