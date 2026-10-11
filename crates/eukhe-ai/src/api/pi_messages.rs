//! The `pi-messages` wire API. Port of `api/pi-messages.ts`.
//!
//! Streams pi's own message protocol directly to a backend: the request is a
//! single POST of `{ model, context, options }` to `<baseUrl>/messages`, the
//! response is an SSE stream of serialized assistant-message events plus a
//! terminal `done`/`error` event. This is the wire protocol spoken by the
//! Radius gateway, but any backend implementing it can be used, e.g. via a
//! models.json custom provider with `"api": "pi-messages"`.
//!
//! API-specific options (TS `PiMessagesOptions`) arrive in
//! [`ProviderStreamOptions::extra`]: `reasoning` (a thinking level),
//! `toolChoice` (`"auto" | "none" | "required" | { type: "function",
//! function: { name } }`), and `debug` (ask the backend for debug metadata,
//! e.g. routing response headers). They are forwarded as the JSON given.

use std::collections::HashMap;
use std::sync::{Arc, LazyLock};

use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, AssistantMessageDiagnostic, AssistantMessageEvent,
    CacheRetention, DiagnosticCode, DoneReason, ErrorReason, JsonObject, JsonValue, Model,
    ProviderEnv, ProviderResponse, StopReason, TextContent, ThinkingContent, ToolCall,
    TranscriptContext, Usage,
};
use futures::future::BoxFuture;
use reqwest::header::{HeaderMap, HeaderName, HeaderValue};
use serde::Deserialize;

use super::ProviderStreams;
use crate::types::{ProviderStreamOptions, SimpleStreamOptions, StreamOptions};
use crate::utils::diagnostics::{
    append_assistant_message_diagnostic, create_assistant_message_diagnostic, thrown, ErrorObject,
    Thrown,
};
use crate::utils::event_stream::AssistantMessageEventStream;
use crate::utils::headers::{headers_to_record, provider_headers_to_record};
use crate::utils::js::{js_trim, json_stringify, utf16_len, utf16_prefix};
use crate::utils::json_parse::{json_parse, parse_streaming_json_object};
use crate::utils::now_ms;
use crate::utils::provider_env::get_provider_env_value;

/// The process-wide client behind the default `fetch` (TS `globalThis.fetch`).
static CLIENT: LazyLock<reqwest::Client> = LazyLock::new(reqwest::Client::new);

const MAX_DIAGNOSTIC_STRING_LENGTH: usize = 8192;

/// TS `PiMessagesOptions`: the shared stream options plus the pi-messages
/// keys of [`ProviderStreamOptions::extra`].
#[derive(Clone, Default)]
struct PiMessagesOptions {
    stream: StreamOptions,
    reasoning: Option<JsonValue>,
    tool_choice: Option<JsonValue>,
    debug: bool,
}

impl PiMessagesOptions {
    fn from_provider_options(options: ProviderStreamOptions) -> Self {
        let ProviderStreamOptions { stream, mut extra } = options;
        Self {
            stream,
            reasoning: extra.remove("reasoning"),
            tool_choice: extra.remove("toolChoice"),
            debug: extra.remove("debug").is_some_and(|debug| is_truthy(&debug)),
        }
    }
}

/// JS truthiness of a JSON value.
fn is_truthy(value: &JsonValue) -> bool {
    match value {
        JsonValue::Null => false,
        JsonValue::Bool(flag) => *flag,
        JsonValue::Number(number) => number.as_f64().is_some_and(|n| n != 0.0 && !n.is_nan()),
        JsonValue::String(text) => !text.is_empty(),
        JsonValue::Array(_) | JsonValue::Object(_) => true,
    }
}

/// TS `PiMessagesRewriteImpact`: impact summary of a server-side message
/// rewrite (e.g. a gateway policy), kept as the JSON object sent.
type PiMessagesRewriteImpact = JsonObject;

/// TS `PiMessagesEvent`: a serialized assistant-message event as sent by a
/// pi-messages backend.
#[derive(Debug, Deserialize)]
#[serde(tag = "type", rename_all_fields = "camelCase")]
enum PiMessagesEvent {
    #[serde(rename = "start")]
    Start,
    #[serde(rename = "text_start")]
    TextStart { content_index: usize },
    #[serde(rename = "text_delta")]
    TextDelta { content_index: usize, delta: String },
    #[serde(rename = "text_end")]
    TextEnd {
        content_index: usize,
        content: String,
        content_signature: Option<String>,
    },
    #[serde(rename = "thinking_start")]
    ThinkingStart { content_index: usize },
    #[serde(rename = "thinking_delta")]
    ThinkingDelta { content_index: usize, delta: String },
    #[serde(rename = "thinking_end")]
    ThinkingEnd {
        content_index: usize,
        content: String,
        content_signature: Option<String>,
        redacted: Option<bool>,
    },
    #[serde(rename = "toolcall_start")]
    ToolCallStart {
        content_index: usize,
        id: String,
        tool_name: String,
    },
    #[serde(rename = "toolcall_delta")]
    ToolCallDelta { content_index: usize, delta: String },
    #[serde(rename = "toolcall_end")]
    ToolCallEnd {
        content_index: usize,
        tool_call: JsonObject,
    },
    #[serde(rename = "done")]
    Done {
        reason: DoneReason,
        usage: Usage,
        response_id: Option<String>,
        provider_thinking_level: Option<String>,
        rewrite: Option<PiMessagesRewriteImpact>,
    },
    #[serde(rename = "error")]
    Error {
        reason: ErrorReason,
        usage: Usage,
        error_message: Option<String>,
        response_id: Option<String>,
        provider_thinking_level: Option<String>,
        rewrite: Option<PiMessagesRewriteImpact>,
    },
}

/// A failure of one pi-messages request (TS `catch (error)`).
enum PiMessagesFailure {
    /// TS `PiMessagesResponseError`: a non-2xx response, with its
    /// `diagnosticDetails`.
    Response {
        error: Thrown,
        diagnostic_details: JsonObject,
    },
    /// Any other thrown value.
    Thrown(Thrown),
}

impl From<Thrown> for PiMessagesFailure {
    fn from(error: Thrown) -> Self {
        Self::Thrown(error)
    }
}

/// TS `new Error(message)`.
fn error(message: impl Into<String>) -> PiMessagesFailure {
    PiMessagesFailure::Thrown(ErrorObject::new(message).thrown())
}

/// A thrown JS `TypeError`.
fn type_error(message: impl Into<String>) -> Thrown {
    ErrorObject::named("TypeError", message).thrown()
}

/// TS `parsePiMessagesErrorBody`: the parsed body when it is an object whose
/// `error` is a non-array object.
fn parse_pi_messages_error_body(body: &str) -> Option<JsonObject> {
    match json_parse(body).ok()? {
        JsonValue::Object(parsed) if parsed.get("error").is_some_and(JsonValue::is_object) => {
            Some(parsed)
        }
        _ => None,
    }
}

fn truncate_diagnostic_string(value: &str) -> String {
    if utf16_len(value) > MAX_DIAGNOSTIC_STRING_LENGTH {
        format!("{}…", utf16_prefix(value, MAX_DIAGNOSTIC_STRING_LENGTH))
    } else {
        value.to_owned()
    }
}

fn error_string_field<'a>(error_body: Option<&'a JsonObject>, key: &str) -> Option<&'a str> {
    error_body?.get("error")?.get(key)?.as_str()
}

/// TS `createPiMessagesResponseError`.
fn create_pi_messages_response_error(
    model: &Model,
    url: &reqwest::Url,
    status: u16,
    status_text: &str,
    body: &str,
) -> PiMessagesFailure {
    let error_body = parse_pi_messages_error_body(body);
    let message = error_string_field(error_body.as_ref(), "message");
    let code = error_string_field(error_body.as_ref(), "code");
    let suffix = message.unwrap_or(body);
    let code_suffix = code
        .filter(|code| !code.is_empty())
        .map(|code| format!(" ({code})"))
        .unwrap_or_default();
    let mut error = ErrorObject::named(
        "PiMessagesResponseError",
        format!("{status} {status_text}: {suffix}{code_suffix}"),
    );
    if let Some(code) = code {
        error = error.with_code(DiagnosticCode::String(code.to_owned()));
    }

    let mut details = JsonObject::new();
    details.insert("version".into(), 1.into());
    details.insert("provider".into(), model.provider.as_str().into());
    details.insert("model".into(), model.id.clone().into());
    details.insert("url".into(), url.to_string().into());
    details.insert("status".into(), status.into());
    details.insert("statusText".into(), status_text.into());
    match &error_body {
        Some(parsed) => {
            if let Some(inner) = parsed.get("error") {
                details.insert("error".into(), inner.clone());
            }
        }
        None => {
            details.insert("body".into(), truncate_diagnostic_string(body).into());
        }
    }
    details.insert("timestampMs".into(), now_ms().into());
    PiMessagesFailure::Response {
        error: error.thrown(),
        diagnostic_details: details,
    }
}

fn append_rewrite_diagnostic(message: &mut AssistantMessage, rewrite: Option<JsonObject>) {
    let Some(rewrite) = rewrite else {
        return;
    };
    append_assistant_message_diagnostic(
        message,
        AssistantMessageDiagnostic {
            kind: "pi_messages_rewrite".to_owned(),
            timestamp: now_ms(),
            error: None,
            details: Some(rewrite),
        },
    );
}

fn create_empty_message(model: &Model, stop_reason: StopReason) -> AssistantMessage {
    AssistantMessage {
        content: Vec::new(),
        api: model.api.clone(),
        provider: model.provider.clone(),
        model: model.id.clone(),
        response_model: None,
        response_id: None,
        provider_thinking_level: None,
        thinking_level: None,
        diagnostics: None,
        usage: Usage::default(),
        stop_reason,
        deferred: None,
        error_message: None,
        raw_stop_reason: None,
        end_turn: None,
        timestamp: now_ms(),
        duration_ms: None,
    }
}

/// TS `createEventConverter`: folds wire events into the partial message.
struct EventConverter {
    partial: AssistantMessage,
    tool_json: HashMap<usize, String>,
}

/// TS `Cannot read properties of undefined` for a missing content block.
fn missing_block(property: &str) -> Thrown {
    type_error(format!(
        "Cannot read properties of undefined (reading '{property}')"
    ))
}

impl EventConverter {
    fn new(model: &Model) -> Self {
        Self {
            partial: create_empty_message(model, StopReason::Pending),
            tool_json: HashMap::new(),
        }
    }

    /// TS `partial.content[index] = block`. JS arrays may grow sparse; a
    /// Rust transcript cannot hold holes, so an index past the end fails.
    fn set_block(&mut self, index: usize, block: AssistantContentBlock) -> Result<(), Thrown> {
        let content = &mut self.partial.content;
        match index.cmp(&content.len()) {
            std::cmp::Ordering::Less => content[index] = block,
            std::cmp::Ordering::Equal => content.push(block),
            std::cmp::Ordering::Greater => {
                return Err(type_error(format!(
                    "content index {index} is past the end of the partial message"
                )));
            }
        }
        Ok(())
    }

    fn text_block(&mut self, index: usize) -> Result<&mut TextContent, Thrown> {
        match self.partial.content.get_mut(index) {
            Some(AssistantContentBlock::Text(text)) => Ok(text),
            Some(AssistantContentBlock::Thinking(_) | AssistantContentBlock::ToolCall(_)) => Err(
                type_error(format!("content block {index} is not a text block")),
            ),
            None => Err(missing_block("text")),
        }
    }

    fn thinking_block(&mut self, index: usize) -> Result<&mut ThinkingContent, Thrown> {
        match self.partial.content.get_mut(index) {
            Some(AssistantContentBlock::Thinking(thinking)) => Ok(thinking),
            Some(AssistantContentBlock::Text(_) | AssistantContentBlock::ToolCall(_)) => Err(
                type_error(format!("content block {index} is not a thinking block")),
            ),
            None => Err(missing_block("thinking")),
        }
    }

    fn tool_call_block(&mut self, index: usize) -> Result<&mut ToolCall, Thrown> {
        match self.partial.content.get_mut(index) {
            Some(AssistantContentBlock::ToolCall(call)) => Ok(call),
            Some(AssistantContentBlock::Text(_) | AssistantContentBlock::Thinking(_)) => Err(
                type_error(format!("content block {index} is not a tool call block")),
            ),
            None => Err(missing_block("arguments")),
        }
    }

    #[allow(clippy::too_many_lines)] // One arm per wire event, mirroring the TS switch.
    fn convert(&mut self, event: PiMessagesEvent) -> Result<AssistantMessageEvent, Thrown> {
        let partial = |this: &Self| this.partial.clone();
        Ok(match event {
            PiMessagesEvent::Done {
                reason,
                usage,
                response_id,
                provider_thinking_level,
                rewrite,
            } => {
                self.partial.stop_reason = reason.into();
                self.partial.usage = usage;
                self.partial.response_id = response_id;
                if provider_thinking_level.is_some() {
                    self.partial.provider_thinking_level = provider_thinking_level;
                }
                append_rewrite_diagnostic(&mut self.partial, rewrite);
                AssistantMessageEvent::Done {
                    reason,
                    message: partial(self),
                }
            }
            PiMessagesEvent::Error {
                reason,
                usage,
                error_message,
                response_id,
                provider_thinking_level,
                rewrite,
            } => {
                self.partial.stop_reason = reason.into();
                self.partial.usage = usage;
                self.partial.error_message = error_message;
                self.partial.response_id = response_id;
                if provider_thinking_level.is_some() {
                    self.partial.provider_thinking_level = provider_thinking_level;
                }
                append_rewrite_diagnostic(&mut self.partial, rewrite);
                AssistantMessageEvent::Error {
                    reason,
                    error: partial(self),
                }
            }
            PiMessagesEvent::Start => AssistantMessageEvent::Start {
                partial: partial(self),
            },
            PiMessagesEvent::TextStart { content_index } => {
                self.set_block(
                    content_index,
                    AssistantContentBlock::Text(TextContent::new("")),
                )?;
                AssistantMessageEvent::TextStart {
                    content_index,
                    partial: partial(self),
                }
            }
            PiMessagesEvent::TextDelta {
                content_index,
                delta,
            } => {
                self.text_block(content_index)?.text.push_str(&delta);
                AssistantMessageEvent::TextDelta {
                    content_index,
                    delta,
                    partial: partial(self),
                }
            }
            PiMessagesEvent::TextEnd {
                content_index,
                content,
                content_signature,
            } => {
                let block = self.text_block(content_index)?;
                block.text.clone_from(&content);
                block.text_signature = content_signature;
                AssistantMessageEvent::TextEnd {
                    content_index,
                    content,
                    partial: partial(self),
                }
            }
            PiMessagesEvent::ThinkingStart { content_index } => {
                self.set_block(
                    content_index,
                    AssistantContentBlock::Thinking(ThinkingContent::default()),
                )?;
                AssistantMessageEvent::ThinkingStart {
                    content_index,
                    partial: partial(self),
                }
            }
            PiMessagesEvent::ThinkingDelta {
                content_index,
                delta,
            } => {
                self.thinking_block(content_index)?
                    .thinking
                    .push_str(&delta);
                AssistantMessageEvent::ThinkingDelta {
                    content_index,
                    delta,
                    partial: partial(self),
                }
            }
            PiMessagesEvent::ThinkingEnd {
                content_index,
                content,
                content_signature,
                redacted,
            } => {
                let block = self.thinking_block(content_index)?;
                block.thinking.clone_from(&content);
                block.thinking_signature = content_signature;
                block.redacted = redacted;
                AssistantMessageEvent::ThinkingEnd {
                    content_index,
                    content,
                    partial: partial(self),
                }
            }
            PiMessagesEvent::ToolCallStart {
                content_index,
                id,
                tool_name,
            } => {
                self.set_block(
                    content_index,
                    AssistantContentBlock::ToolCall(ToolCall {
                        id,
                        name: tool_name,
                        arguments: JsonObject::new(),
                        thought_signature: None,
                        namespace: None,
                    }),
                )?;
                self.tool_json.insert(content_index, String::new());
                AssistantMessageEvent::ToolCallStart {
                    content_index,
                    partial: partial(self),
                }
            }
            PiMessagesEvent::ToolCallDelta {
                content_index,
                delta,
            } => {
                let json = format!(
                    "{}{delta}",
                    self.tool_json
                        .get(&content_index)
                        .map_or("", String::as_str)
                );
                self.tool_call_block(content_index)?.arguments =
                    parse_streaming_json_object(Some(&json));
                self.tool_json.insert(content_index, json);
                AssistantMessageEvent::ToolCallDelta {
                    content_index,
                    delta,
                    partial: partial(self),
                }
            }
            PiMessagesEvent::ToolCallEnd {
                content_index,
                tool_call,
            } => {
                // TS `Object.assign(block, event.toolCall)`.
                let block = self.tool_call_block(content_index)?;
                let JsonValue::Object(mut merged) =
                    serde_json::to_value(&*block).map_err(thrown)?
                else {
                    return Err(type_error("tool call block is not an object"));
                };
                merged.extend(tool_call);
                *block = serde_json::from_value(JsonValue::Object(merged)).map_err(thrown)?;
                let tool_call = block.clone();
                self.tool_json.remove(&content_index);
                AssistantMessageEvent::ToolCallEnd {
                    content_index,
                    tool_call,
                    partial: partial(self),
                }
            }
        })
    }
}

/// TS `parsePiMessagesEvent`: the first `data:` line of one SSE event.
fn parse_pi_messages_event(raw: &str) -> Result<Option<JsonValue>, Thrown> {
    let data = raw
        .split('\n')
        .find(|line| line.starts_with("data:"))
        .map(|line| js_trim(&line[5..]));
    match data {
        Some(data) if !data.is_empty() && data != "[DONE]" => {
            json_parse(data).map(Some).map_err(thrown)
        }
        Some(_) | None => Ok(None),
    }
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
                    if let Some(length) = error.error_len() {
                        out.push('\u{FFFD}');
                        rest = &after[length..];
                    } else {
                        rest = after;
                        break;
                    }
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

/// TS `readPiMessagesEvents`: the raw JSON events of the SSE body.
struct PiMessagesEventReader {
    response: reqwest::Response,
    signal: Option<eukhe_chord::context::AbortSignal>,
    decoder: Utf8Decoder,
    buffer: String,
    body_done: bool,
}

impl PiMessagesEventReader {
    /// The next parsed event, `None` at the end of the body.
    async fn next_event(&mut self) -> Result<Option<JsonValue>, Thrown> {
        loop {
            while let Some(split) = self.buffer.find("\n\n") {
                let raw = self.buffer[..split].to_owned();
                self.buffer.drain(..split + 2);
                if let Some(event) = parse_pi_messages_event(&raw)? {
                    return Ok(Some(event));
                }
            }
            if self.body_done {
                if js_trim(&self.buffer).is_empty() {
                    return Ok(None);
                }
                let raw = std::mem::take(&mut self.buffer);
                return parse_pi_messages_event(&raw);
            }
            let chunk = match &self.signal {
                Some(signal) => {
                    signal.throw_if_aborted()?;
                    tokio::select! {
                        reason = signal.cancelled() => return Err(reason),
                        chunk = self.response.chunk() => chunk,
                    }
                }
                None => self.response.chunk().await,
            }
            .map_err(|error| type_error(format!("terminated: {error}")))?;
            if let Some(bytes) = chunk {
                self.decoder.decode(&bytes, &mut self.buffer);
            } else {
                self.decoder.finish(&mut self.buffer);
                self.body_done = true;
            }
            self.buffer = self.buffer.replace("\r\n", "\n");
        }
    }
}

/// TS `resolveCacheRetention`: backend defaults apply when unset; only the
/// legacy `PI_CACHE_RETENTION=long` env opt-in is mapped.
fn resolve_cache_retention(
    cache_retention: Option<CacheRetention>,
    env: Option<&ProviderEnv>,
) -> Option<CacheRetention> {
    if cache_retention.is_some() {
        return cache_retention;
    }
    (get_provider_env_value("PI_CACHE_RETENTION", env).as_deref() == Some("long"))
        .then_some(CacheRetention::Long)
}

/// TS `new URL(...)` of the base URL without trailing slashes plus `/messages`,
/// `searchParams.set("debug", "1")` when requested.
fn messages_url(base_url: &str, debug: bool) -> Result<reqwest::Url, Thrown> {
    let mut url = reqwest::Url::parse(&format!("{}/messages", base_url.trim_end_matches('/')))
        .map_err(|_| type_error("Invalid URL"))?;
    if debug {
        let retained: Vec<(String, String)> = url
            .query_pairs()
            .filter(|(name, _)| name != "debug")
            .map(|(name, value)| (name.into_owned(), value.into_owned()))
            .collect();
        url.query_pairs_mut()
            .clear()
            .extend_pairs(retained)
            .append_pair("debug", "1");
    }
    Ok(url)
}

/// Request headers: the defaults spread with the caller's headers (an
/// object literal, so keys are exact-case), then combined per name like a
/// fetch `Headers` init.
fn request_headers(api_key: &str, options: &StreamOptions) -> Result<HeaderMap, Thrown> {
    let mut record: Vec<(String, String)> = vec![
        ("authorization".to_owned(), format!("Bearer {api_key}")),
        ("accept".to_owned(), "text/event-stream".to_owned()),
        ("content-type".to_owned(), "application/json".to_owned()),
    ];
    for (name, value) in
        provider_headers_to_record(&[options.request.headers.as_ref()]).unwrap_or_default()
    {
        match record.iter_mut().find(|(existing, _)| *existing == name) {
            Some(entry) => entry.1 = value,
            None => record.push((name, value)),
        }
    }
    let mut combined: Vec<(HeaderName, String)> = Vec::new();
    for (name, value) in record {
        let name = HeaderName::from_bytes(name.as_bytes())
            .map_err(|_| type_error(format!("Invalid header name: {name}")))?;
        match combined.iter_mut().find(|(existing, _)| *existing == name) {
            Some(entry) => {
                entry.1.push_str(", ");
                entry.1.push_str(&value);
            }
            None => combined.push((name, value)),
        }
    }
    let mut headers = HeaderMap::new();
    for (name, value) in combined {
        let value = HeaderValue::from_str(&value)
            .map_err(|_| type_error(format!("Invalid header value for {name}")))?;
        headers.insert(name, value);
    }
    Ok(headers)
}

/// TS `JSON.stringify(payload)` input: `{ model, context, options }` with
/// undefined options omitted.
fn build_payload(
    model: &Model,
    context: &TranscriptContext,
    options: &PiMessagesOptions,
) -> Result<JsonValue, Thrown> {
    let stream = &options.stream;
    let mut request_options = JsonObject::new();
    if let Some(temperature) = stream.temperature {
        request_options.insert(
            "temperature".into(),
            crate::utils::js::js_number_value(temperature),
        );
    }
    if let Some(max_tokens) = stream.max_tokens {
        request_options.insert("maxTokens".into(), max_tokens.into());
    }
    if let Some(reasoning) = &options.reasoning {
        request_options.insert("reasoning".into(), reasoning.clone());
    }
    if let Some(retention) =
        resolve_cache_retention(stream.cache_retention, stream.request.env.as_ref())
    {
        request_options.insert(
            "cacheRetention".into(),
            serde_json::to_value(retention).map_err(thrown)?,
        );
    }
    if let Some(session_id) = &stream.session_id {
        request_options.insert("sessionId".into(), session_id.clone().into());
    }
    if let Some(tool_choice) = &options.tool_choice {
        request_options.insert("toolChoice".into(), tool_choice.clone());
    }
    let mut payload = JsonObject::new();
    payload.insert("model".into(), model.id.clone().into());
    payload.insert(
        "context".into(),
        serde_json::to_value(context).map_err(thrown)?,
    );
    payload.insert("options".into(), JsonValue::Object(request_options));
    Ok(JsonValue::Object(payload))
}

fn default_fetch(
    request: reqwest::Request,
) -> BoxFuture<'static, Result<reqwest::Response, Thrown>> {
    Box::pin(async move {
        CLIENT
            .execute(request)
            .await
            .map_err(|error| type_error(format!("fetch failed: {error}")))
    })
}

/// The request body of TS `stream`, up to the first terminal event.
async fn run_stream(
    model: &Model,
    context: &TranscriptContext,
    options: &PiMessagesOptions,
    converter: &mut EventConverter,
    target: &AssistantMessageEventStream,
) -> Result<(), PiMessagesFailure> {
    let request_options = &options.stream.request;
    let Some(api_key) = request_options
        .api_key
        .as_deref()
        .filter(|key| !key.is_empty())
    else {
        return Err(error(format!(
            "No API key provided for provider \"{}\"",
            model.provider
        )));
    };

    let url = messages_url(&model.base_url, options.debug)?;
    let mut payload = build_payload(model, context, options)?;
    if let Some(on_payload) = &request_options.on_payload {
        if let Some(next) = on_payload(payload.clone(), model).await? {
            payload = next;
        }
    }

    let mut request = reqwest::Request::new(reqwest::Method::POST, url.clone());
    *request.headers_mut() = request_headers(api_key, &options.stream)?;
    *request.body_mut() = Some(json_stringify(&payload).into());
    let exchange = match &request_options.fetch {
        Some(fetch) => fetch(request),
        None => default_fetch(request),
    };
    let signal = request_options.signal.clone();
    let response = match &signal {
        Some(signal) => {
            signal.throw_if_aborted()?;
            tokio::select! {
                reason = signal.cancelled() => return Err(reason.into()),
                response = exchange => response?,
            }
        }
        None => exchange.await?,
    };

    if let Some(on_response) = &request_options.on_response {
        on_response(
            ProviderResponse {
                status: response.status().as_u16(),
                headers: headers_to_record(response.headers()),
            },
            model,
        )
        .await?;
    }

    let status = response.status();
    if !status.is_success() {
        let body = response
            .text()
            .await
            .map_err(|error| type_error(format!("terminated: {error}")))?;
        return Err(create_pi_messages_response_error(
            model,
            &url,
            status.as_u16(),
            status.canonical_reason().unwrap_or_default(),
            &body,
        ));
    }

    let mut reader = PiMessagesEventReader {
        response,
        signal,
        decoder: Utf8Decoder::default(),
        buffer: String::new(),
        body_done: false,
    };
    while let Some(raw_event) = reader.next_event().await? {
        if let Some(observer) = &options.stream.on_provider_stream_event {
            observer(&raw_event, model).await?;
        }
        let pi_event: PiMessagesEvent = serde_json::from_value(raw_event).map_err(thrown)?;
        let event = converter.convert(pi_event)?;
        let terminal = matches!(
            event,
            AssistantMessageEvent::Done { .. } | AssistantMessageEvent::Error { .. }
        );
        target.push(event);
        if terminal {
            return Ok(());
        }
    }

    Err(error(format!(
        "{} stream ended without a terminal event",
        model.provider
    )))
}

/// TS `createErrorEvent`: a fresh error message (the partial is dropped).
fn create_error_event(
    model: &Model,
    failure: &PiMessagesFailure,
    aborted: bool,
) -> AssistantMessageEvent {
    let reason = if aborted {
        ErrorReason::Aborted
    } else {
        ErrorReason::Error
    };
    let mut message = create_empty_message(model, reason.into());
    let error = match failure {
        PiMessagesFailure::Response { error, .. } | PiMessagesFailure::Thrown(error) => error,
    };
    message.error_message = Some(error.to_string());
    if let (
        false,
        PiMessagesFailure::Response {
            error,
            diagnostic_details,
        },
    ) = (aborted, failure)
    {
        append_assistant_message_diagnostic(
            &mut message,
            create_assistant_message_diagnostic(
                "pi_messages_response_failure",
                error,
                Some(diagnostic_details.clone()),
            ),
        );
    }
    AssistantMessageEvent::Error {
        reason,
        error: message,
    }
}

/// Streams a request with pi-messages options (TS `stream`). Must be called
/// inside a tokio runtime.
#[must_use]
pub fn stream(
    model: &Model,
    context: &TranscriptContext,
    options: ProviderStreamOptions,
) -> AssistantMessageEventStream {
    let stream = AssistantMessageEventStream::new();
    let options = PiMessagesOptions::from_provider_options(options);
    let model = model.clone();
    let context = context.clone();
    let target = stream.clone();
    tokio::spawn(async move {
        let mut converter = EventConverter::new(&model);
        if let Err(failure) = run_stream(&model, &context, &options, &mut converter, &target).await
        {
            let aborted = options
                .stream
                .request
                .signal
                .as_ref()
                .is_some_and(eukhe_chord::context::AbortSignal::aborted);
            target.push(create_error_event(&model, &failure, aborted));
        }
        target.end(None);
    });
    stream
}

/// TS `streamSimple`: the simple options with `reasoning` and `toolChoice`
/// forwarded. TS also forwards an untyped `debug` key; Rust
/// [`SimpleStreamOptions`] has no extra keys, so it is never set here.
#[must_use]
pub fn stream_simple(
    model: &Model,
    context: &TranscriptContext,
    options: SimpleStreamOptions,
) -> AssistantMessageEventStream {
    let mut extra = JsonObject::new();
    if let Some(reasoning) = options.reasoning {
        extra.insert("reasoning".into(), reasoning.as_str().into());
    }
    if let Some(tool_choice) = options.tool_choice {
        extra.insert("toolChoice".into(), tool_choice.as_str().into());
    }
    stream(
        model,
        context,
        ProviderStreamOptions {
            stream: options.stream,
            extra,
        },
    )
}

/// The `pi-messages` API module.
#[must_use]
pub fn streams() -> ProviderStreams {
    ProviderStreams {
        stream: Arc::new(stream),
        stream_simple: Arc::new(stream_simple),
        fetch_deferred: None,
        cancel_deferred: None,
    }
}
