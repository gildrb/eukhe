//! Raw SSE decoding of the Anthropic Messages stream: TS `iterateSseMessages`
//! and `iterateAnthropicEvents`.

use eukhe_chord::context::AbortSignal;
use eukhe_types::pi_ai::JsonValue;

use crate::utils::diagnostics::{ErrorObject, Thrown};
use crate::utils::json_parse::parse_json_with_repair;

/// One decoded server-sent event (TS `ServerSentEvent`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ServerSentEvent {
    pub(crate) event: Option<String>,
    pub(crate) data: String,
    pub(crate) raw: Vec<String>,
}

/// TS `SseDecoderState`.
#[derive(Debug, Default)]
struct SseDecoderState {
    event: Option<String>,
    data: Vec<String>,
    raw: Vec<String>,
}

const ANTHROPIC_MESSAGE_EVENTS: [&str; 6] = [
    "message_start",
    "message_delta",
    "message_stop",
    "content_block_start",
    "content_block_delta",
    "content_block_stop",
];

fn flush_sse_event(state: &mut SseDecoderState) -> Option<ServerSentEvent> {
    // TS `!state.event`: an empty event name counts as absent.
    if state.event.as_deref().is_none_or(str::is_empty) && state.data.is_empty() {
        return None;
    }
    let event = ServerSentEvent {
        event: state.event.take(),
        data: state.data.join("\n"),
        raw: std::mem::take(&mut state.raw),
    };
    state.data.clear();
    Some(event)
}

fn decode_sse_line(line: &str, state: &mut SseDecoderState) -> Option<ServerSentEvent> {
    if line.is_empty() {
        return flush_sse_event(state);
    }
    state.raw.push(line.to_owned());
    if line.starts_with(':') {
        return None;
    }
    let (field_name, mut value) = match line.find(':') {
        None => (line, ""),
        Some(index) => (&line[..index], &line[index + 1..]),
    };
    if let Some(rest) = value.strip_prefix(' ') {
        value = rest;
    }
    match field_name {
        "event" => state.event = Some(value.to_owned()),
        "data" => state.data.push(value.to_owned()),
        _ => {}
    }
    None
}

/// TS `consumeLine` on a byte buffer: the line before the first CR, LF, or
/// CRLF, and the number of bytes consumed. CR/LF never occur inside a UTF-8
/// multi-byte sequence, so splitting bytes equals splitting decoded text.
fn consume_line(buffer: &[u8]) -> Option<(&[u8], usize)> {
    let index = buffer
        .iter()
        .position(|&byte| byte == b'\r' || byte == b'\n')?;
    let mut next = index + 1;
    if buffer[index] == b'\r' && buffer.get(next) == Some(&b'\n') {
        next += 1;
    }
    Some((&buffer[..index], next))
}

/// Incremental SSE decoder over response body chunks (TS
/// `iterateSseMessages`, with `TextDecoder` replacement of invalid UTF-8).
#[derive(Debug, Default)]
pub(crate) struct SseDecoder {
    buffer: Vec<u8>,
    state: SseDecoderState,
}

impl SseDecoder {
    /// Feed one chunk; returns the events it completes.
    pub(crate) fn push(&mut self, chunk: &[u8]) -> Vec<ServerSentEvent> {
        self.buffer.extend_from_slice(chunk);
        let mut events = Vec::new();
        let mut start = 0;
        while let Some((line, consumed)) = consume_line(&self.buffer[start..]) {
            let line = String::from_utf8_lossy(line).into_owned();
            start += consumed;
            if let Some(event) = decode_sse_line(&line, &mut self.state) {
                events.push(event);
            }
        }
        self.buffer.drain(..start);
        events
    }

    /// End of body: the trailing partial line and any unterminated event.
    pub(crate) fn finish(&mut self) -> Vec<ServerSentEvent> {
        let mut events = Vec::new();
        if !self.buffer.is_empty() {
            let line = String::from_utf8_lossy(&self.buffer).into_owned();
            self.buffer.clear();
            if let Some(event) = decode_sse_line(&line, &mut self.state) {
                events.push(event);
            }
        }
        if let Some(event) = flush_sse_event(&mut self.state) {
            events.push(event);
        }
        events
    }
}

/// A failure while iterating Anthropic events, with what the eukhe
/// stream-failure diagnostic needs to classify it.
#[derive(Debug, Clone)]
pub(crate) enum EventStreamError {
    /// An in-stream `event: error`; the TS error message is the raw data.
    SseError(String),
    /// A data payload that did not parse as JSON.
    Parse(String),
    /// `message_start` without `message_stop`.
    EndedBeforeStop,
    /// Abort signal or body read failure.
    Thrown(Thrown),
}

impl EventStreamError {
    pub(crate) fn message(&self) -> String {
        match self {
            Self::SseError(data) => data.clone(),
            Self::Parse(message) => message.clone(),
            Self::EndedBeforeStop => "Anthropic stream ended before message_stop".to_owned(),
            Self::Thrown(error) => error.to_string(),
        }
    }
}

/// Iterates the parsed Anthropic message events of a streaming response
/// (TS `iterateAnthropicEvents`).
pub(crate) struct AnthropicEvents {
    response: reqwest::Response,
    decoder: SseDecoder,
    pending: std::collections::VecDeque<ServerSentEvent>,
    finished: bool,
    saw_message_start: bool,
    saw_message_end: bool,
    signal: Option<AbortSignal>,
}

fn aborted_error() -> Thrown {
    ErrorObject::new("Request was aborted").thrown()
}

impl AnthropicEvents {
    pub(crate) fn new(response: reqwest::Response, signal: Option<AbortSignal>) -> Self {
        Self {
            response,
            decoder: SseDecoder::default(),
            pending: std::collections::VecDeque::new(),
            finished: false,
            saw_message_start: false,
            saw_message_end: false,
            signal,
        }
    }

    async fn next_sse(&mut self) -> Result<Option<ServerSentEvent>, EventStreamError> {
        loop {
            if let Some(event) = self.pending.pop_front() {
                return Ok(Some(event));
            }
            if self.finished {
                return Ok(None);
            }
            if self.signal.as_ref().is_some_and(AbortSignal::aborted) {
                return Err(EventStreamError::Thrown(aborted_error()));
            }
            let chunk = match &self.signal {
                Some(signal) => {
                    let token = signal.cancellation_token();
                    tokio::select! {
                        chunk = self.response.chunk() => chunk,
                        () = token.cancelled() => {
                            return Err(EventStreamError::Thrown(aborted_error()));
                        }
                    }
                }
                None => self.response.chunk().await,
            };
            match chunk {
                Ok(Some(bytes)) => self.pending.extend(self.decoder.push(&bytes)),
                Err(error) => {
                    return Err(EventStreamError::Thrown(
                        ErrorObject::named("TypeError", error.to_string()).thrown(),
                    ));
                }
                Ok(None) => {
                    self.finished = true;
                    self.pending.extend(self.decoder.finish());
                }
            }
        }
    }

    /// The next parsed message event; `None` at the end of the body.
    pub(crate) async fn next(&mut self) -> Result<Option<JsonValue>, EventStreamError> {
        while let Some(sse) = self.next_sse().await? {
            if sse.event.as_deref() == Some("error") {
                return Err(EventStreamError::SseError(sse.data));
            }
            if !ANTHROPIC_MESSAGE_EVENTS.contains(&sse.event.as_deref().unwrap_or("")) {
                continue;
            }
            match parse_json_with_repair(&sse.data) {
                Ok(event) => {
                    match event.get("type").and_then(JsonValue::as_str) {
                        Some("message_start") => self.saw_message_start = true,
                        Some("message_stop") => self.saw_message_end = true,
                        _ => {}
                    }
                    return Ok(Some(event));
                }
                Err(error) => {
                    return Err(EventStreamError::Parse(format!(
                        "Could not parse Anthropic SSE event {}: {error}; data={}; raw={}",
                        sse.event.as_deref().unwrap_or("null"),
                        sse.data,
                        sse.raw.join("\\n"),
                    )));
                }
            }
        }
        if self.saw_message_start && !self.saw_message_end {
            return Err(EventStreamError::EndedBeforeStop);
        }
        Ok(None)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn decode_all(chunks: &[&str]) -> Vec<ServerSentEvent> {
        let mut decoder = SseDecoder::default();
        let mut events = Vec::new();
        for chunk in chunks {
            events.extend(decoder.push(chunk.as_bytes()));
        }
        events.extend(decoder.finish());
        events
    }

    #[test]
    fn decodes_crlf_cr_and_split_chunks() {
        let events = decode_all(&[
            "event: a\r\ndata: 1\r",
            "\n\r\nevent:b\rdata:2\n",
            "\n: c\ndata: 3",
        ]);
        assert_eq!(
            events,
            vec![
                ServerSentEvent {
                    event: Some("a".into()),
                    data: "1".into(),
                    raw: vec!["event: a".into(), "data: 1".into()],
                },
                ServerSentEvent {
                    event: Some("b".into()),
                    data: "2".into(),
                    raw: vec!["event:b".into(), "data:2".into()],
                },
                ServerSentEvent {
                    event: None,
                    data: "3".into(),
                    raw: vec![": c".into(), "data: 3".into()],
                },
            ]
        );
    }
}
