//! `Stream.fromSSEResponse` of the `openai` SDK: line decoding, SSE record
//! decoding, `[DONE]`, JSON parsing, and `APIError` for error payloads.
//! Aborting the request signal ends the stream silently (the SDK swallows
//! transport abort errors).

use std::collections::VecDeque;

use eukhe_chord::context::AbortSignal;
use futures::stream::BoxStream;
use futures::StreamExt;
use reqwest::header::HeaderMap;

use super::{api_error, js_truthy};
use crate::types::JsonValue;
use crate::utils::diagnostics::{ErrorObject, Thrown};

/// Parsed SSE JSON payloads; errors are the SDK's thrown errors.
pub(crate) type SseEventStream = BoxStream<'static, Result<JsonValue, Thrown>>;

/// One decoded server-sent event (TS `ServerSentEvent`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ServerSentEvent {
    pub event: Option<String>,
    pub data: String,
}

/// TS `LineDecoder`: splits bytes into lines at `\n`, `\r`, or `\r\n`.
#[derive(Debug, Default)]
pub(crate) struct LineDecoder {
    buffer: Vec<u8>,
}

impl LineDecoder {
    pub(crate) fn decode(&mut self, chunk: &[u8]) -> Vec<String> {
        self.buffer.extend_from_slice(chunk);
        let mut lines = Vec::new();
        let mut start = 0;
        let mut index = 0;
        while index < self.buffer.len() {
            match self.buffer[index] {
                b'\n' => {
                    lines.push(String::from_utf8_lossy(&self.buffer[start..index]).into_owned());
                    index += 1;
                    start = index;
                }
                b'\r' => {
                    // A trailing `\r` may be the first half of `\r\n`.
                    if index + 1 == self.buffer.len() {
                        break;
                    }
                    lines.push(String::from_utf8_lossy(&self.buffer[start..index]).into_owned());
                    index += if self.buffer[index + 1] == b'\n' {
                        2
                    } else {
                        1
                    };
                    start = index;
                }
                _ => index += 1,
            }
        }
        self.buffer.drain(..start);
        lines
    }

    pub(crate) fn flush(&mut self) -> Vec<String> {
        if self.buffer.is_empty() {
            return Vec::new();
        }
        let mut text = std::mem::take(&mut self.buffer);
        if text.last() == Some(&b'\r') {
            text.pop();
        }
        vec![String::from_utf8_lossy(&text).into_owned()]
    }
}

/// TS `SSEDecoder`.
#[derive(Debug, Default)]
pub(crate) struct SseDecoder {
    data: Vec<String>,
    event: Option<String>,
}

impl SseDecoder {
    pub(crate) fn decode(&mut self, line: &str) -> Option<ServerSentEvent> {
        let line = line.strip_suffix('\r').unwrap_or(line);
        if line.is_empty() {
            // `!this.event && !this.data.length`: an empty event name is falsy.
            if self.event.as_deref().is_none_or(str::is_empty) && self.data.is_empty() {
                return None;
            }
            let sse = ServerSentEvent {
                event: self.event.take(),
                data: self.data.join("\n"),
            };
            self.data.clear();
            return Some(sse);
        }
        if line.starts_with(':') {
            return None;
        }
        let (field, value) = match line.find(':') {
            Some(index) => (&line[..index], &line[index + 1..]),
            None => (line, ""),
        };
        let value = value.strip_prefix(' ').unwrap_or(value);
        if field == "event" {
            self.event = Some(value.to_owned());
        } else if field == "data" {
            self.data.push(value.to_owned());
        }
        None
    }

    pub(crate) fn flush(&mut self) -> Option<ServerSentEvent> {
        self.decode("")
    }
}

/// `SyntaxError` for an unparseable SSE payload.
fn malformed_json_error() -> Thrown {
    ErrorObject::named(
        "SyntaxError",
        "Error reading response: malformed server-sent event JSON.",
    )
    .thrown()
}

/// Turns one SSE record into the SDK's yielded item or thrown error.
/// `Ok(None)` is the `[DONE]` sentinel.
fn handle_event(sse: &ServerSentEvent, headers: &HeaderMap) -> Result<Option<JsonValue>, Thrown> {
    if sse.data == "[DONE]" {
        return Ok(None);
    }
    let data: JsonValue = serde_json::from_str(&sse.data).map_err(|_| malformed_json_error())?;
    match sse.event.as_deref() {
        Some(event) if event.starts_with("thread.") => {
            let mut item = serde_json::Map::new();
            item.insert("event".to_owned(), JsonValue::String(event.to_owned()));
            item.insert("data".to_owned(), data);
            Ok(Some(JsonValue::Object(item)))
        }
        event => {
            if event == Some("error") {
                // `data?.error ?? data`
                let error = match data.get("error") {
                    Some(inner) if !inner.is_null() => inner.clone(),
                    _ => data,
                };
                return Err(api_error(None, Some(error), None, Some(headers.clone())).thrown());
            }
            if let Some(error) = data.get("error").filter(|error| js_truthy(error)) {
                return Err(
                    api_error(None, Some(error.clone()), None, Some(headers.clone())).thrown(),
                );
            }
            Ok(Some(data))
        }
    }
}

struct SseState {
    bytes: BoxStream<'static, Result<Vec<u8>, String>>,
    lines: LineDecoder,
    decoder: SseDecoder,
    pending: VecDeque<ServerSentEvent>,
    headers: HeaderMap,
    signal: Option<AbortSignal>,
    body_done: bool,
    finished: bool,
}

impl SseState {
    fn aborted(&self) -> bool {
        self.signal.as_ref().is_some_and(AbortSignal::aborted)
    }

    fn push_lines(&mut self, lines: Vec<String>) {
        for line in lines {
            if let Some(sse) = self.decoder.decode(&line) {
                self.pending.push_back(sse);
            }
        }
    }

    /// Next chunk of the body, or `None` at its end or on abort.
    async fn next_chunk(&mut self) -> Option<Result<Vec<u8>, String>> {
        match self.signal.clone() {
            Some(signal) => tokio::select! {
                _ = signal.cancelled() => None,
                chunk = self.bytes.next() => chunk,
            },
            None => self.bytes.next().await,
        }
    }

    async fn next_item(&mut self) -> Option<Result<JsonValue, Thrown>> {
        loop {
            if self.finished || self.aborted() {
                return None;
            }
            if let Some(sse) = self.pending.pop_front() {
                match handle_event(&sse, &self.headers) {
                    Ok(Some(item)) => return Some(Ok(item)),
                    Ok(None) => {
                        self.finished = true;
                        return None;
                    }
                    Err(error) => {
                        self.finished = true;
                        return Some(Err(error));
                    }
                }
            }
            if self.body_done {
                self.finished = true;
                return None;
            }
            match self.next_chunk().await {
                Some(Ok(chunk)) => {
                    let lines = self.lines.decode(&chunk);
                    self.push_lines(lines);
                }
                Some(Err(_)) if self.aborted() => return None,
                Some(Err(_)) => {
                    // undici's error for a body that breaks off mid-stream.
                    self.finished = true;
                    return Some(Err(ErrorObject::named("TypeError", "terminated").thrown()));
                }
                None => {
                    if self.aborted() {
                        return None;
                    }
                    let lines = self.lines.flush();
                    self.push_lines(lines);
                    if let Some(sse) = self.decoder.flush() {
                        self.pending.push_back(sse);
                    }
                    self.body_done = true;
                }
            }
        }
    }
}

/// Decode a streamed body into the SDK's SSE item stream.
pub(crate) fn sse_json_stream(
    bytes: BoxStream<'static, Result<Vec<u8>, String>>,
    headers: HeaderMap,
    signal: Option<AbortSignal>,
) -> SseEventStream {
    let state = SseState {
        bytes,
        lines: LineDecoder::default(),
        decoder: SseDecoder::default(),
        pending: VecDeque::new(),
        headers,
        signal,
        body_done: false,
        finished: false,
    };
    futures::stream::unfold(state, |mut state| async move {
        let item = state.next_item().await?;
        Some((item, state))
    })
    .boxed()
}
