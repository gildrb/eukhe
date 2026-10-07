//! The `@google/genai` streaming response path: `ApiClient.streamApiCall`
//! (the `fetch`, `throwErrorIfNotOK`), `processStreamResponse` (the SSE
//! decoder with its in-band error check), and the per-chunk
//! `generateContentResponseFromMldev` / `generateContentResponseFromVertex`
//! transforms.

use std::collections::VecDeque;
use std::future::Future;

use eukhe_chord::context::AbortSignal;
use eukhe_types::pi_ai::{JsonObject, JsonValue};
use reqwest::header::{HeaderMap, CONTENT_TYPE};
use serde_json::json;

use crate::utils::diagnostics::{ErrorObject, Thrown};
use crate::utils::headers::headers_to_record;
use crate::utils::js::{js_trim, json_stringify};
use crate::utils::json_parse::json_parse;

/// The `AbortError` a `fetch` rejects with when the SDK's per-attempt
/// controller aborts (it is aborted without a reason).
fn abort_error() -> Thrown {
    ErrorObject::named("AbortError", "This operation was aborted").thrown()
}

/// Node `fetch` network failure.
fn fetch_failed() -> Thrown {
    ErrorObject::named("TypeError", "fetch failed").thrown()
}

/// Node `fetch` body failure after the response started.
fn terminated() -> Thrown {
    ErrorObject::named("TypeError", "terminated").thrown()
}

/// SDK `ApiError`: `name` `ApiError` with a numeric `status`.
fn api_error(message: String, status: u16) -> Thrown {
    ErrorObject {
        status: Some(Some(JsonValue::from(status))),
        ..ErrorObject::named("ApiError", message)
    }
    .thrown()
}

/// Run `future` unless `signal` aborts first.
async fn abortable<T>(
    future: impl Future<Output = T>,
    signal: Option<&AbortSignal>,
) -> Result<T, Thrown> {
    match signal {
        Some(signal) => tokio::select! {
            biased;
            _ = signal.cancelled() => Err(abort_error()),
            value = future => Ok(value),
        },
        None => Ok(future.await),
    }
}

/// `apiClient.requestStream(...)`: POST the body and resolve with the event
/// stream once the response is OK.
pub(super) async fn stream_api_call(
    client: &reqwest::Client,
    url: url::Url,
    headers: Vec<(String, String)>,
    body: String,
    signal: Option<&AbortSignal>,
    vertexai: bool,
) -> Result<GenerateContentStream, Thrown> {
    if signal.is_some_and(AbortSignal::aborted) {
        return Err(abort_error());
    }
    let mut request = client.post(url);
    for (name, value) in &headers {
        request = request.header(name.as_str(), value.as_str());
    }
    let response = abortable(request.body(body).send(), signal)
        .await?
        .map_err(|_| fetch_failed())?;
    let response = throw_error_if_not_ok(response, signal).await?;
    Ok(GenerateContentStream {
        source: Source::Http(Box::new(HttpSource {
            headers: response.headers().clone(),
            response,
            signal: signal.cloned(),
            pending_bytes: Vec::new(),
            buffer: String::new(),
            events: VecDeque::new(),
            done: false,
        })),
        vertexai,
    })
}

/// `throwErrorIfNotOK(response)`.
async fn throw_error_if_not_ok(
    response: reqwest::Response,
    signal: Option<&AbortSignal>,
) -> Result<reqwest::Response, Thrown> {
    let status = response.status();
    if status.is_success() {
        return Ok(response);
    }
    let is_json = response
        .headers()
        .get(CONTENT_TYPE)
        .and_then(|value| value.to_str().ok())
        .is_some_and(|value| value.contains("application/json"));
    // Node's `statusText` is the reason phrase; HTTP/2 has none.
    let status_text = if response.version() == reqwest::Version::HTTP_2 {
        ""
    } else {
        status.canonical_reason().unwrap_or_default()
    };
    let text = abortable(response.text(), signal)
        .await?
        .map_err(|_| terminated())?;
    let error_body = if is_json {
        json_parse(&text)
            .map_err(|error| ErrorObject::named("SyntaxError", error.message).thrown())?
    } else {
        json!({ "error": { "message": text, "code": status.as_u16(), "status": status_text } })
    };
    let message = json_stringify(&error_body);
    if (400..600).contains(&status.as_u16()) {
        return Err(api_error(message, status.as_u16()));
    }
    Err(ErrorObject::new(message).thrown())
}

struct HttpSource {
    response: reqwest::Response,
    headers: HeaderMap,
    signal: Option<AbortSignal>,
    /// Undecoded trailing bytes of an incomplete UTF-8 sequence (the
    /// streaming `TextDecoder` state).
    pending_bytes: Vec<u8>,
    buffer: String,
    /// Complete `data:` payloads not yet yielded.
    events: VecDeque<String>,
    done: bool,
}

enum Source {
    Http(Box<HttpSource>),
    /// Canned chunks (the test mock of `generateContentStream`).
    #[cfg(test)]
    Chunks(VecDeque<JsonValue>),
}

/// The async iterable `generateContentStream` resolves with: yields one
/// `GenerateContentResponse` (as JSON) per server-sent event.
pub(crate) struct GenerateContentStream {
    source: Source,
    vertexai: bool,
}

const DATA_PREFIX: &str = "data:";
const DELIMITERS: [&str; 3] = ["\n\n", "\r\r", "\r\n\r\n"];

impl GenerateContentStream {
    #[cfg(test)]
    pub(crate) fn from_chunks(chunks: Vec<JsonValue>) -> Self {
        Self {
            source: Source::Chunks(chunks.into()),
            vertexai: false,
        }
    }

    /// The next response chunk; `None` at the end of the stream.
    pub(crate) async fn next(&mut self) -> Option<Result<JsonValue, Thrown>> {
        let vertexai = self.vertexai;
        match &mut self.source {
            Source::Http(source) => {
                let text = match source.next_event().await? {
                    Ok(text) => text,
                    Err(error) => return Some(Err(error)),
                };
                // `chunk.json()`.
                let parsed = match json_parse(&text) {
                    Ok(parsed) => parsed,
                    Err(error) => {
                        return Some(Err(
                            ErrorObject::named("SyntaxError", error.message).thrown()
                        ));
                    }
                };
                let mut response = if vertexai {
                    generate_content_response_from_vertex(&parsed)
                } else {
                    generate_content_response_from_mldev(&parsed)
                };
                let headers = headers_to_record(&source.headers)
                    .into_iter()
                    .map(|(name, value)| (name, JsonValue::String(value)))
                    .collect::<JsonObject>();
                response.insert(
                    "sdkHttpResponse".into(),
                    json!({ "headers": JsonValue::Object(headers) }),
                );
                Some(Ok(JsonValue::Object(response)))
            }
            #[cfg(test)]
            Source::Chunks(chunks) => chunks.pop_front().map(Ok),
        }
    }
}

impl HttpSource {
    /// The next `data:` payload of `processStreamResponse`.
    async fn next_event(&mut self) -> Option<Result<String, Thrown>> {
        loop {
            if let Some(event) = self.events.pop_front() {
                return Some(Ok(event));
            }
            if self.done {
                return None;
            }
            let chunk = match abortable(self.response.chunk(), self.signal.as_ref()).await {
                Ok(Ok(chunk)) => chunk,
                Ok(Err(_)) => {
                    self.done = true;
                    return Some(Err(terminated()));
                }
                Err(error) => {
                    self.done = true;
                    return Some(Err(error));
                }
            };
            let Some(bytes) = chunk else {
                self.done = true;
                // The SDK never flushes its streaming decoder: undecoded
                // trailing bytes are dropped.
                if !js_trim(&self.buffer).is_empty() {
                    return Some(Err(
                        ErrorObject::new("Incomplete JSON segment at the end").thrown()
                    ));
                }
                return None;
            };
            let chunk_string = self.decode(&bytes);
            // Parse and throw an error if the chunk contains an error.
            if let Ok(JsonValue::Object(chunk_json)) = json_parse(&chunk_string) {
                if let Some(error) = chunk_json.get("error") {
                    let code = error.get("code").and_then(JsonValue::as_f64);
                    let status = error
                        .get("status")
                        .map_or_else(|| "undefined".to_owned(), crate::utils::js::js_to_string);
                    if let Some(code) = code.filter(|code| (400.0..600.0).contains(code)) {
                        self.done = true;
                        let message = format!(
                            "got status: {status}. {}",
                            json_stringify(&JsonValue::Object(chunk_json.clone()))
                        );
                        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                        // `code` is within 400..600.
                        let code = code as u16;
                        return Some(Err(api_error(message, code)));
                    }
                }
            }
            self.buffer.push_str(&chunk_string);
            self.split_events();
        }
    }

    /// Move every complete event out of the buffer.
    fn split_events(&mut self) {
        loop {
            let next = DELIMITERS
                .iter()
                .filter_map(|delimiter| {
                    self.buffer
                        .find(delimiter)
                        .map(|index| (index, delimiter.len()))
                })
                .min_by_key(|(index, _)| *index);
            let Some((index, length)) = next else {
                return;
            };
            let event: String = self.buffer[..index].to_owned();
            self.buffer.drain(..index + length);
            let trimmed = js_trim(&event);
            if let Some(data) = trimmed.strip_prefix(DATA_PREFIX) {
                self.events.push_back(js_trim(data).to_owned());
            }
        }
    }

    /// `TextDecoder.decode(value, { stream: true })`: invalid sequences
    /// become U+FFFD; an incomplete trailing sequence waits for more bytes.
    fn decode(&mut self, bytes: &[u8]) -> String {
        self.pending_bytes.extend_from_slice(bytes);
        let mut output = String::new();
        let mut rest: &[u8] = &self.pending_bytes;
        loop {
            match std::str::from_utf8(rest) {
                Ok(valid) => {
                    output.push_str(valid);
                    rest = &[];
                    break;
                }
                Err(error) => {
                    let (valid, after) = rest.split_at(error.valid_up_to());
                    output.push_str(std::str::from_utf8(valid).unwrap_or_default());
                    let Some(length) = error.error_len() else {
                        rest = after;
                        break;
                    };
                    output.push(char::REPLACEMENT_CHARACTER);
                    rest = &after[length..];
                }
            }
        }
        self.pending_bytes = rest.to_vec();
        output
    }
}

/// `getValueByPath(from, [key]) != null` copied into `to`.
fn copy(from: &JsonObject, to: &mut JsonObject, key: &str) {
    if let Some(value) = from.get(key).filter(|value| !value.is_null()) {
        to.insert(key.to_owned(), value.clone());
    }
}

/// `candidateFromMldev`.
fn candidate_from_mldev(candidate: &JsonValue) -> JsonValue {
    let from = candidate.as_object().cloned().unwrap_or_default();
    let mut to = JsonObject::new();
    copy(&from, &mut to, "content");
    if let Some(citation) = from
        .get("citationMetadata")
        .filter(|value| !value.is_null())
    {
        let mut citations = JsonObject::new();
        if let Some(sources) = citation
            .get("citationSources")
            .filter(|value| !value.is_null())
        {
            citations.insert("citations".into(), sources.clone());
        }
        to.insert("citationMetadata".into(), JsonValue::Object(citations));
    }
    for key in [
        "tokenCount",
        "finishReason",
        "groundingMetadata",
        "avgLogprobs",
        "index",
        "logprobsResult",
        "safetyRatings",
        "urlContextMetadata",
    ] {
        copy(&from, &mut to, key);
    }
    JsonValue::Object(to)
}

/// `generateContentResponseFromMldev`.
fn generate_content_response_from_mldev(response: &JsonValue) -> JsonObject {
    let from = response.as_object().cloned().unwrap_or_default();
    let mut to = JsonObject::new();
    copy(&from, &mut to, "sdkHttpResponse");
    if let Some(candidates) = from.get("candidates").filter(|value| !value.is_null()) {
        let candidates = match candidates {
            JsonValue::Array(items) => {
                JsonValue::Array(items.iter().map(candidate_from_mldev).collect())
            }
            other => other.clone(),
        };
        to.insert("candidates".into(), candidates);
    }
    for key in [
        "modelVersion",
        "promptFeedback",
        "responseId",
        "usageMetadata",
        "modelStatus",
    ] {
        copy(&from, &mut to, key);
    }
    to
}

/// `generateContentResponseFromVertex`.
fn generate_content_response_from_vertex(response: &JsonValue) -> JsonObject {
    let from = response.as_object().cloned().unwrap_or_default();
    let mut to = JsonObject::new();
    for key in [
        "sdkHttpResponse",
        "candidates",
        "createTime",
        "modelVersion",
        "promptFeedback",
        "responseId",
        "usageMetadata",
    ] {
        copy(&from, &mut to, key);
    }
    to
}
