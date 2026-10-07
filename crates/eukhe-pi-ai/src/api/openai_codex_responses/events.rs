//! Codex event mapping and SSE parsing. Section of the port of
//! `api/openai-codex-responses.ts`.

use std::collections::VecDeque;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

use bytes::Bytes;
use eukhe_chord::context::AbortSignal;
use eukhe_types::pi_ai::{AssistantMessage, AssistantMessageEvent, JsonValue, Model};
use futures::stream::{BoxStream, Stream, StreamExt};

use crate::types::OnProviderStreamEvent;
use crate::utils::diagnostics::Thrown;
use crate::utils::event_stream::AssistantMessageEventStream;
use crate::utils::js::{js_trim, json_stringify};

use super::errors::{
    aborted_error, codex_api_error, codex_protocol_error, provider_stream_event_callback_error,
};

/// A stream of parsed provider events.
pub(crate) type EventSource = BoxStream<'static, Result<JsonValue, Thrown>>;

const CODEX_RESPONSE_STATUSES: [&str; 6] = [
    "completed",
    "incomplete",
    "failed",
    "cancelled",
    "queued",
    "in_progress",
];

/// Mutations [`map_codex_events`] makes to the output while the Responses
/// processor owns it: TS sets `output.endTurn` before yielding the terminal
/// event. Callers apply them with [`OutputEffects::apply`].
#[derive(Debug, Default)]
pub(crate) struct OutputEffects {
    end_turn: Mutex<Option<bool>>,
}

impl OutputEffects {
    /// Apply the recorded mutations to `output`.
    pub(crate) fn apply(&self, output: &mut AssistantMessage) {
        if let Some(end_turn) = *self.end_turn.lock().unwrap_or_else(PoisonError::into_inner) {
            output.end_turn = Some(end_turn);
        }
    }
}

/// TS `extractCodexEventError`.
fn extract_codex_event_error(event: &JsonValue) -> (Option<String>, Option<String>) {
    let nested = event.get("error").filter(|error| error.is_object());
    let string_field = |name: &str| {
        event
            .get(name)
            .and_then(JsonValue::as_str)
            .or_else(|| {
                nested
                    .and_then(|nested| nested.get(name))
                    .and_then(JsonValue::as_str)
            })
            .map(str::to_owned)
    };
    (string_field("code"), string_field("message"))
}

/// TS `normalizeCodexStatus`.
fn normalize_codex_status(status: Option<&JsonValue>) -> Option<JsonValue> {
    let status = status?.as_str()?;
    CODEX_RESPONSE_STATUSES
        .contains(&status)
        .then(|| JsonValue::String(status.to_owned()))
}

struct MapState {
    source: EventSource,
    model: Model,
    on_provider_stream_event: Option<OnProviderStreamEvent>,
    effects: Arc<OutputEffects>,
    finished: bool,
}

/// TS `mapCodexEvents`: report each event to `onProviderStreamEvent`, raise
/// Codex error events, and normalize the terminal event to
/// `response.completed`.
pub(crate) fn map_codex_events(
    source: EventSource,
    model: &Model,
    on_provider_stream_event: Option<OnProviderStreamEvent>,
    effects: Arc<OutputEffects>,
) -> EventSource {
    let state = MapState {
        source,
        model: model.clone(),
        on_provider_stream_event,
        effects,
        finished: false,
    };
    futures::stream::unfold(state, |mut state| async move {
        if state.finished {
            return None;
        }
        let item = next_mapped_event(&mut state).await;
        match item {
            Some(Ok(_)) => {}
            Some(Err(_)) | None => state.finished = true,
        }
        item.map(|item| (item, state))
    })
    .boxed()
}

async fn next_mapped_event(state: &mut MapState) -> Option<Result<JsonValue, Thrown>> {
    loop {
        let event = match state.source.next().await? {
            Ok(event) => event,
            Err(error) => return Some(Err(error)),
        };
        if let Some(callback) = &state.on_provider_stream_event {
            if let Err(error) = callback(&event, &state.model).await {
                // Keep callback failures out of Codex's WebSocket retry and SSE fallback path.
                return Some(Err(provider_stream_event_callback_error(&error)));
            }
        }
        let Some(event_type) = event.get("type").and_then(JsonValue::as_str) else {
            continue;
        };
        if event_type.is_empty() {
            continue;
        }

        if event_type == "error" {
            let (code, message) = extract_codex_event_error(&event);
            let detail = message
                .filter(|message| !message.is_empty())
                .or_else(|| code.clone().filter(|code| !code.is_empty()))
                .unwrap_or_else(|| json_stringify(&event));
            return Some(Err(codex_api_error(format!("Codex error: {detail}"), code)));
        }

        if event_type == "response.failed" {
            let error = event
                .get("response")
                .and_then(|response| response.get("error"));
            let code = error
                .and_then(|error| error.get("code"))
                .and_then(JsonValue::as_str)
                .map(str::to_owned);
            let message = error
                .and_then(|error| error.get("message"))
                .and_then(JsonValue::as_str)
                .filter(|message| !message.is_empty())
                .unwrap_or("Codex response failed");
            return Some(Err(codex_api_error(message.to_owned(), code)));
        }

        if matches!(
            event_type,
            "response.done" | "response.completed" | "response.incomplete"
        ) {
            let response = event.get("response");
            if let Some(end_turn) = response
                .and_then(|response| response.get("end_turn"))
                .and_then(JsonValue::as_bool)
            {
                *state
                    .effects
                    .end_turn
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner) = Some(end_turn);
            }
            let mut mapped = event.as_object().cloned().unwrap_or_default();
            mapped.insert(
                "type".into(),
                JsonValue::String("response.completed".into()),
            );
            let normalized = match response {
                // TS `response ? { ...response, status } : response`: any truthy value spreads.
                Some(response) if js_truthy(response) => {
                    let mut normalized = response.as_object().cloned().unwrap_or_default();
                    match normalize_codex_status(response.get("status")) {
                        Some(status) => normalized.insert("status".into(), status),
                        // `status: undefined` is dropped from the serialized object.
                        None => normalized.shift_remove("status"),
                    };
                    Some(JsonValue::Object(normalized))
                }
                Some(response) => Some(response.clone()),
                None => None,
            };
            match normalized {
                Some(normalized) => mapped.insert("response".into(), normalized),
                None => mapped.shift_remove("response"),
            };
            state.finished_after_terminal();
            return Some(Ok(JsonValue::Object(mapped)));
        }

        return Some(Ok(event));
    }
}

impl MapState {
    fn finished_after_terminal(&mut self) {
        self.finished = true;
    }
}

fn js_truthy(value: &JsonValue) -> bool {
    match value {
        JsonValue::Null => false,
        JsonValue::Bool(flag) => *flag,
        JsonValue::Number(number) => number.as_f64().is_some_and(|n| n != 0.0 && !n.is_nan()),
        JsonValue::String(text) => !text.is_empty(),
        JsonValue::Array(_) | JsonValue::Object(_) => true,
    }
}

/// TS `startWebSocketOutputOnFirstEvent`: run `on_start` before the first
/// event is handed on.
pub(crate) fn start_output_on_first_event(
    source: EventSource,
    on_start: impl FnOnce() + Send + 'static,
) -> EventSource {
    let mut on_start = Some(on_start);
    source
        .map(move |item| {
            if item.is_ok() {
                if let Some(on_start) = on_start.take() {
                    on_start();
                }
            }
            item
        })
        .boxed()
}

/// Emits `start` with the output snapshot once across transports (TS
/// `startEmitted` plus `stream.push({ type: "start", partial: output })`).
#[derive(Clone)]
pub(crate) struct StartEmitter {
    emitted: Arc<AtomicBool>,
    stream: AssistantMessageEventStream,
}

impl StartEmitter {
    pub(crate) fn new(stream: AssistantMessageEventStream) -> Self {
        Self {
            emitted: Arc::new(AtomicBool::new(false)),
            stream,
        }
    }

    /// Push `start` unless it was already pushed.
    pub(crate) fn emit(&self, partial: &AssistantMessage) {
        if !self.emitted.swap(true, Ordering::SeqCst) {
            self.stream.push(AssistantMessageEvent::Start {
                partial: partial.clone(),
            });
        }
    }
}

// ---------------------------------------------------------------------------
// SSE parsing
// ---------------------------------------------------------------------------

/// Streaming UTF-8 decoding with replacement characters (TS `TextDecoder`
/// with `{ stream: true }`).
#[derive(Debug, Default)]
pub(crate) struct Utf8StreamDecoder {
    pending: Vec<u8>,
}

impl Utf8StreamDecoder {
    /// Decode `chunk`, keeping an incomplete trailing sequence for later.
    pub(crate) fn decode(&mut self, chunk: &[u8]) -> String {
        self.pending.extend_from_slice(chunk);
        let mut out = String::new();
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
                    if let Some(len) = error.error_len() {
                        out.push('\u{FFFD}');
                        rest = &after[len..];
                    } else {
                        rest = after;
                        break;
                    }
                }
            }
        }
        self.pending = rest.to_vec();
        out
    }

    /// Flush at end of input (TS `decoder.decode()`).
    pub(crate) fn finish(&mut self) -> String {
        if self.pending.is_empty() {
            return String::new();
        }
        self.pending.clear();
        "\u{FFFD}".to_owned()
    }
}

struct SseState {
    body: BoxStream<'static, Result<Bytes, Thrown>>,
    signal: Option<AbortSignal>,
    decoder: Utf8StreamDecoder,
    buffer: String,
    ready: VecDeque<Result<JsonValue, Thrown>>,
    done: bool,
}

/// TS `parseSSE`: `data:` frames of the response body as JSON values.
/// Dropping the stream cancels the body.
pub(crate) fn parse_sse(
    body: impl Stream<Item = Result<Bytes, Thrown>> + Send + 'static,
    signal: Option<AbortSignal>,
) -> EventSource {
    let state = SseState {
        body: body.boxed(),
        signal,
        decoder: Utf8StreamDecoder::default(),
        buffer: String::new(),
        ready: VecDeque::new(),
        done: false,
    };
    futures::stream::unfold(Some(state), |state| async move {
        let mut state = state?;
        loop {
            if let Some(item) = state.ready.pop_front() {
                let failed = item.is_err();
                return Some((item, (!failed).then_some(state)));
            }
            if state.done {
                return None;
            }
            if let Err(error) = read_sse_chunk(&mut state).await {
                return Some((Err(error), None));
            }
        }
    })
    .boxed()
}

fn is_aborted(signal: Option<&AbortSignal>) -> bool {
    signal.is_some_and(AbortSignal::aborted)
}

async fn read_sse_chunk(state: &mut SseState) -> Result<(), Thrown> {
    if is_aborted(state.signal.as_ref()) {
        return Err(aborted_error());
    }
    let next = match &state.signal {
        Some(signal) => {
            let token = signal.cancellation_token();
            tokio::select! {
                () = token.cancelled() => return Err(aborted_error()),
                next = state.body.next() => next,
            }
        }
        None => state.body.next().await,
    };
    if is_aborted(state.signal.as_ref()) {
        return Err(aborted_error());
    }
    let done = match next {
        Some(Ok(chunk)) => {
            let text = state.decoder.decode(&chunk);
            state.buffer.push_str(&text);
            false
        }
        Some(Err(error)) => return Err(error),
        None => {
            let text = state.decoder.finish();
            state.buffer.push_str(&text);
            // Treat EOF as terminating the residual SSE frame.
            if !js_trim(&state.buffer).is_empty() {
                state.buffer.push_str("\n\n");
            }
            true
        }
    };

    while let Some(index) = state.buffer.find("\n\n") {
        let chunk: String = state.buffer[..index].to_owned();
        state.buffer.drain(..index + 2);

        let data_lines: Vec<&str> = chunk
            .split('\n')
            .filter(|line| line.starts_with("data:"))
            .map(|line| js_trim(&line[5..]))
            .collect();
        if !data_lines.is_empty() {
            let joined = data_lines.join("\n");
            let data = js_trim(&joined);
            if !data.is_empty() && data != "[DONE]" {
                match serde_json::from_str::<JsonValue>(data) {
                    Ok(event) => state.ready.push_back(Ok(event)),
                    Err(cause) => {
                        state.ready.push_back(Err(codex_protocol_error(format!(
                            "Invalid Codex SSE JSON: {cause}"
                        ))));
                        break;
                    }
                }
            }
        }
    }

    state.done = done;
    Ok(())
}
