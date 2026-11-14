//! Sending the request with provider retries, and folding the Anthropic
//! stream events into the assistant message (the `for await` loop of TS
//! `stream` and `mapStopReason`).

use std::collections::HashMap;
use std::sync::{Mutex, PoisonError};

use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, AssistantMessageDiagnostic, AssistantMessageEvent,
    JsonObject, JsonValue, Model, StopReason, StreamFailureKind, TextContent, ThinkingContent,
    Tool, ToolCall, Usage,
};
use reqwest::header::HeaderMap;

use super::client::{RequestFailure, RequestOptions, SdkClient};
use super::params::from_claude_code_name;
use super::sse::{AnthropicEvents, EventStreamError};
use super::{model_compat, AnthropicOptions, StreamFailure};
use crate::models::calculate_cost;
use crate::utils::diagnostics::{append_assistant_message_diagnostic, ErrorObject, Thrown};
use crate::utils::event_stream::AssistantMessageEventStream;
use crate::utils::json_parse::{
    parse_json_with_repair, parse_streaming_json_object, parse_tool_call_arguments,
};
use crate::utils::now_ms;
use crate::utils::provider_retry::{retry_provider_request, ProviderRetryOptions};
use crate::utils::stream_failure::{
    classify_stream_failure, stream_failure_from_stop_reason, stream_failure_message,
    truncate_raw_payload, ConnectionErrorKind, ConnectionErrorProfile, ProviderConnectionError,
    ProviderError, StreamFailureError, StreamFailureInfo,
};

fn header_map_to_hash(headers: &HeaderMap) -> HashMap<String, String> {
    headers
        .iter()
        .filter_map(|(name, value)| {
            value
                .to_str()
                .ok()
                .map(|value| (name.as_str().to_owned(), value.to_owned()))
        })
        .collect()
}

/// The eukhe stream-failure classification of a request failure.
fn request_diagnostic(failure: &RequestFailure) -> ProviderError {
    if let Some((status, body, headers)) = &failure.http {
        return ProviderError::from_http_status_body(*status, body, header_map_to_hash(headers));
    }
    if let Some(connection) = &failure.connection {
        return ProviderError::Connection(ProviderConnectionError {
            kind: if connection.timeout {
                ConnectionErrorKind::Timeout
            } else {
                ConnectionErrorKind::Connect
            },
            profile: ConnectionErrorProfile::Sdk,
            cause: connection.cause.clone(),
        });
    }
    ProviderError::Message(failure.thrown.to_string())
}

/// TS `retryProviderRequest(() => client.beta.messages.create(...).asResponse(), ...)`.
pub(crate) async fn send_with_retries(
    client: &SdkClient,
    params: JsonObject,
    options: &AnthropicOptions,
) -> Result<reqwest::Response, StreamFailure> {
    let request = &options.stream.request;
    let request_options = RequestOptions {
        signal: request.signal.clone(),
        timeout_ms: request.timeout_ms,
    };
    let last_failure: Mutex<Option<(Thrown, ProviderError)>> = Mutex::new(None);
    let result = retry_provider_request(
        || async {
            match client
                .create_message_stream(params.clone(), &request_options)
                .await
            {
                Ok(response) => Ok(response),
                Err(failure) => {
                    let diagnostic = request_diagnostic(&failure);
                    *last_failure.lock().unwrap_or_else(PoisonError::into_inner) =
                        Some((failure.thrown.clone(), diagnostic));
                    Err(failure.thrown)
                }
            }
        },
        &ProviderRetryOptions {
            max_retries: request.max_retries,
            max_retry_delay_ms: request.max_retry_delay_ms,
            signal: request.signal.clone(),
            no_retry_statuses: Vec::new(),
        },
    )
    .await;
    result.map_err(|thrown| {
        let diagnostic = last_failure
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .take()
            .filter(|(source, _)| std::sync::Arc::ptr_eq(source, &thrown))
            .map_or_else(
                || ProviderError::Message(thrown.to_string()),
                |(_, diagnostic)| diagnostic,
            );
        StreamFailure {
            thrown,
            diagnostic: Box::new(diagnostic),
        }
    })
}

/// An in-stream `error` event as a classified failure (eukhe addition).
fn sse_error_diagnostic(data: &str, request_id: Option<&str>) -> ProviderError {
    let mut error_type: Option<String> = None;
    let mut detail: Option<String> = None;
    let mut request_id = request_id.map(str::to_owned);
    match parse_json_with_repair(data) {
        Ok(parsed) => {
            if let Some(error) = parsed.get("error") {
                error_type = error
                    .get("type")
                    .and_then(JsonValue::as_str)
                    .map(str::to_owned);
                detail = error
                    .get("message")
                    .and_then(JsonValue::as_str)
                    .map(str::to_owned);
            }
            if let Some(id) = parsed.get("request_id").and_then(JsonValue::as_str) {
                request_id = Some(id.to_owned());
            }
        }
        Err(_) => detail = Some(data.to_owned()),
    }
    let info = StreamFailureInfo {
        kind: classify_stream_failure(error_type.as_deref(), None),
        provider_error_type: error_type,
        status: None,
        request_id,
        retry_after_ms: None,
        raw: Some(truncate_raw_payload(data)),
        repeated: None,
        idle_timeout_ms: None,
    };
    let message = stream_failure_message(&info, detail.as_deref());
    ProviderError::StreamFailure(StreamFailureError { message, info })
}

fn event_failure(error: &EventStreamError, request_id: Option<&str>) -> StreamFailure {
    let thrown = match error {
        EventStreamError::Thrown(thrown) => thrown.clone(),
        EventStreamError::SseError(_)
        | EventStreamError::Parse(_)
        | EventStreamError::EndedBeforeStop => ErrorObject::new(error.message()).thrown(),
    };
    let diagnostic = match error {
        EventStreamError::SseError(data) => sse_error_diagnostic(data, request_id),
        EventStreamError::EndedBeforeStop => ProviderError::StreamFailure(StreamFailureError {
            message: error.message(),
            info: StreamFailureInfo {
                kind: StreamFailureKind::MalformedResponse,
                request_id: request_id.map(str::to_owned),
                ..StreamFailureInfo::unknown()
            },
        }),
        EventStreamError::Parse(message) => ProviderError::Message(message.clone()),
        EventStreamError::Thrown(thrown) => ProviderError::Message(thrown.to_string()),
    };
    StreamFailure {
        thrown,
        diagnostic: Box::new(diagnostic),
    }
}

/// A stop reason [`map_stop_reason`] does not know.
#[derive(Debug, thiserror::Error)]
#[error("Unhandled stop reason: {reason}")]
struct UnhandledStopReason {
    reason: String,
}

/// TS `mapStopReason`.
fn map_stop_reason(
    reason: &str,
    stop_details: Option<&JsonValue>,
) -> Result<(StopReason, Option<String>), UnhandledStopReason> {
    match reason {
        "end_turn" | "pause_turn" | "stop_sequence" => Ok((StopReason::Stop, None)),
        "max_tokens" => Ok((StopReason::Length, None)),
        "tool_use" => Ok((StopReason::ToolUse, None)),
        "refusal" => {
            let explanation = stop_details
                .and_then(|details| details.get("explanation"))
                .and_then(JsonValue::as_str)
                .filter(|text| !text.is_empty())
                .unwrap_or("The model refused to complete the request");
            Ok((StopReason::Error, Some(explanation.to_owned())))
        }
        "sensitive" => Ok((
            StopReason::Error,
            Some("Provider stopped with: sensitive".to_owned()),
        )),
        other => Err(UnhandledStopReason {
            reason: other.to_owned(),
        }),
    }
}

/// JS `===` between two (possibly undefined) JSON values.
fn js_strict_equal(left: Option<&JsonValue>, right: Option<&JsonValue>) -> bool {
    match (left, right) {
        (None, None) | (Some(JsonValue::Null), Some(JsonValue::Null)) => true,
        (Some(JsonValue::Bool(a)), Some(JsonValue::Bool(b))) => a == b,
        (Some(JsonValue::Number(a)), Some(JsonValue::Number(b))) => a.as_f64() == b.as_f64(),
        (Some(JsonValue::String(a)), Some(JsonValue::String(b))) => a == b,
        _ => false,
    }
}

/// JS string concatenation of a property value (`undefined` → "undefined").
fn js_concat(value: Option<&JsonValue>) -> String {
    match value {
        None => "undefined".to_owned(),
        Some(JsonValue::String(text)) => text.clone(),
        Some(other) => crate::utils::js::js_to_string(other),
    }
}

/// JS `x || 0` / `x != null` on a token count.
fn token_count(value: Option<&JsonValue>) -> Option<u64> {
    let number = value?.as_f64()?;
    // Token counts are non-negative integers on the wire.
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    Some(number.max(0.0) as u64)
}

fn type_error(property: &str) -> StreamFailure {
    StreamFailure::plain(
        ErrorObject::named(
            "TypeError",
            format!("Cannot read properties of undefined (reading '{property}')"),
        )
        .thrown(),
    )
}

/// Streaming scratch kept beside `output.content`: the wire `index` (TS
/// deletes it at `content_block_stop`) and the tool-call `partialJson`.
#[derive(Default)]
struct BlockScratch {
    index: Vec<Option<JsonValue>>,
    partial_json: Vec<String>,
}

impl BlockScratch {
    fn find(&self, index: Option<&JsonValue>) -> Option<usize> {
        self.index
            .iter()
            .position(|candidate| js_strict_equal(candidate.as_ref(), index))
    }
}

fn update_total_and_cost(output: &mut AssistantMessage, usage_model: &Model) {
    let usage = &mut output.usage;
    usage.total_tokens = usage.input + usage.output + usage.cache_read + usage.cache_write;
    calculate_cost(usage_model, usage);
}

/// The token counts one wire `usage` object reports (`None`: absent).
struct WireUsage {
    input: Option<u64>,
    output: Option<u64>,
    cache_read: Option<u64>,
    cache_write: Option<u64>,
    cache_write_1h: Option<u64>,
    reasoning: Option<u64>,
}

impl WireUsage {
    fn read(usage: &JsonValue) -> Self {
        Self {
            input: token_count(usage.get("input_tokens")),
            output: token_count(usage.get("output_tokens")),
            cache_read: token_count(usage.get("cache_read_input_tokens")),
            cache_write: token_count(usage.get("cache_creation_input_tokens")),
            cache_write_1h: token_count(
                usage
                    .get("cache_creation")
                    .and_then(|creation| creation.get("ephemeral_1h_input_tokens")),
            ),
            reasoning: token_count(
                usage
                    .get("output_tokens_details")
                    .and_then(|details| details.get("thinking_tokens")),
            ),
        }
    }

    /// `message_start`: every count is replaced, an absent one by 0; the
    /// reasoning split keeps its value.
    fn replace(self, usage: &mut Usage) {
        usage.input = self.input.unwrap_or(0);
        usage.output = self.output.unwrap_or(0);
        usage.cache_read = self.cache_read.unwrap_or(0);
        usage.cache_write = self.cache_write.unwrap_or(0);
        usage.cache_write_1h = Some(self.cache_write_1h.unwrap_or(0));
    }

    /// `message_delta`: only the reported counts overwrite.
    fn overwrite(self, usage: &mut Usage) {
        usage.input = self.input.unwrap_or(usage.input);
        usage.output = self.output.unwrap_or(usage.output);
        usage.cache_read = self.cache_read.unwrap_or(usage.cache_read);
        usage.cache_write = self.cache_write.unwrap_or(usage.cache_write);
        usage.cache_write_1h = self.cache_write_1h.or(usage.cache_write_1h);
        usage.reasoning = self.reasoning.or(usage.reasoning);
    }
}

/// The model that bills the response: an allowed fallback model the
/// server answered with bills at its own cost; anything else bills as the
/// requested model.
fn billed_model(model: &Model, response_model: Option<&str>) -> Model {
    response_model
        .filter(|response_model| *response_model != model.id)
        .and_then(|response_model| {
            let fallback = model_compat(model)?
                .allowed_fallback_models
                .as_ref()?
                .iter()
                .find(|fallback| {
                    fallback.provider == model.provider && fallback.model == response_model
                })?;
            Some(Model {
                id: response_model.to_owned(),
                cost: fallback.cost.clone(),
                ..model.clone()
            })
        })
        .unwrap_or_else(|| model.clone())
}

/// What a `content_block_start` opens.
enum BlockStart {
    Block(AssistantContentBlock),
    /// The server's model-fallback marker, valid only before any output.
    Fallback,
    /// A block type the stream does not carry.
    Unknown,
}

/// A partial event to emit, by content index; its kind follows the block
/// at that index.
enum Emission {
    Start(usize),
    Delta(usize, String),
    End(usize),
}

/// The assistant message being folded from the stream, and the state kept
/// beside it between events.
struct EventFold<'a> {
    model: &'a Model,
    is_oauth: bool,
    current_tools: &'a [Tool],
    output: &'a mut AssistantMessage,
    /// The model whose prices bill the usage ([`billed_model`]).
    usage_model: Model,
    input_transformations: Option<Vec<JsonValue>>,
    scratch: BlockScratch,
}

impl EventFold<'_> {
    /// Fold one wire event into the message; the partial event it emits.
    fn apply(&mut self, event: &JsonValue) -> Result<Option<Emission>, StreamFailure> {
        match event.get("type").and_then(JsonValue::as_str) {
            Some("message_start") => self.message_start(event).map(|()| None),
            Some("content_block_start") => self.content_block_start(event),
            Some("content_block_delta") => Ok(self.content_block_delta(event)),
            Some("content_block_stop") => Ok(self.content_block_stop(event)),
            Some("message_delta") => self.message_delta(event).map(|()| None),
            _ => Ok(None),
        }
    }

    /// Keep the `input_transformations` array `holder` carries, if any.
    fn note_input_transformations(&mut self, holder: &JsonValue) {
        if let Some(JsonValue::Array(transformations)) = holder.get("input_transformations") {
            self.input_transformations = Some(transformations.clone());
        }
    }

    fn message_start(&mut self, event: &JsonValue) -> Result<(), StreamFailure> {
        let Some(message) = event.get("message") else {
            return Err(type_error("id"));
        };
        if let Some(id) = message.get("id").and_then(JsonValue::as_str) {
            self.output.response_id = Some(id.to_owned());
        }
        self.note_input_transformations(message);
        let response_model = message.get("model").and_then(JsonValue::as_str);
        if response_model != Some(self.model.id.as_str()) {
            self.output.response_model = response_model.map(str::to_owned);
        }
        self.usage_model = billed_model(self.model, response_model);
        let Some(usage) = message.get("usage") else {
            return Err(type_error("input_tokens"));
        };
        WireUsage::read(usage).replace(&mut self.output.usage);
        update_total_and_cost(self.output, &self.usage_model);
        Ok(())
    }

    fn block_start(&self, block: &JsonValue) -> BlockStart {
        let text = |key: &str| block.get(key).and_then(JsonValue::as_str);
        match text("type") {
            Some("fallback") => BlockStart::Fallback,
            Some("text") => BlockStart::Block(AssistantContentBlock::Text(TextContent::new(
                text("text").unwrap_or(""),
            ))),
            Some("thinking") => {
                BlockStart::Block(AssistantContentBlock::Thinking(ThinkingContent {
                    thinking: text("thinking").unwrap_or("").to_owned(),
                    thinking_signature: Some(text("signature").unwrap_or("").to_owned()),
                    redacted: None,
                }))
            }
            Some("redacted_thinking") => {
                BlockStart::Block(AssistantContentBlock::Thinking(ThinkingContent {
                    thinking: "[Reasoning redacted]".to_owned(),
                    thinking_signature: text("data").map(str::to_owned),
                    redacted: Some(true),
                }))
            }
            Some("tool_use") => {
                let name = text("name").unwrap_or("");
                BlockStart::Block(AssistantContentBlock::ToolCall(ToolCall {
                    id: text("id").unwrap_or("").to_owned(),
                    name: if self.is_oauth {
                        from_claude_code_name(name, self.current_tools)
                    } else {
                        name.to_owned()
                    },
                    arguments: match block.get("input") {
                        Some(JsonValue::Object(input)) => input.clone(),
                        _ => JsonObject::new(),
                    },
                    ..ToolCall::default()
                }))
            }
            _ => BlockStart::Unknown,
        }
    }

    fn content_block_start(
        &mut self,
        event: &JsonValue,
    ) -> Result<Option<Emission>, StreamFailure> {
        let Some(block) = event.get("content_block") else {
            return Err(type_error("type"));
        };
        match self.block_start(block) {
            BlockStart::Fallback if !self.output.content.is_empty() => Err(StreamFailure::message(
                "Anthropic performed an unsupported mid-output model fallback",
            )),
            BlockStart::Fallback | BlockStart::Unknown => Ok(None),
            BlockStart::Block(block) => {
                self.output.content.push(block);
                self.scratch.index.push(event.get("index").cloned());
                self.scratch.partial_json.push(String::new());
                Ok(Some(Emission::Start(self.output.content.len() - 1)))
            }
        }
    }

    fn content_block_delta(&mut self, event: &JsonValue) -> Option<Emission> {
        let delta = event.get("delta");
        let position = self.scratch.find(event.get("index"))?;
        let field = |key: &str| js_concat(delta.and_then(|delta| delta.get(key)));
        let delta_type = delta
            .and_then(|delta| delta.get("type"))
            .and_then(JsonValue::as_str);
        match (delta_type, &mut self.output.content[position]) {
            (Some("text_delta"), AssistantContentBlock::Text(block)) => {
                let text = field("text");
                block.text.push_str(&text);
                Some(Emission::Delta(position, text))
            }
            (Some("thinking_delta"), AssistantContentBlock::Thinking(block)) => {
                let text = field("thinking");
                block.thinking.push_str(&text);
                Some(Emission::Delta(position, text))
            }
            (Some("input_json_delta"), AssistantContentBlock::ToolCall(block)) => {
                let text = field("partial_json");
                let partial_json = &mut self.scratch.partial_json[position];
                partial_json.push_str(&text);
                block.arguments = parse_streaming_json_object(Some(partial_json));
                Some(Emission::Delta(position, text))
            }
            (Some("signature_delta"), AssistantContentBlock::Thinking(block)) => {
                let signature = block.thinking_signature.get_or_insert_with(String::new);
                signature.push_str(&field("signature"));
                None
            }
            _ => None,
        }
    }

    fn content_block_stop(&mut self, event: &JsonValue) -> Option<Emission> {
        let position = self.scratch.find(event.get("index"))?;
        self.scratch.index[position] = None;
        if let AssistantContentBlock::ToolCall(block) = &mut self.output.content[position] {
            let partial_json = std::mem::take(&mut self.scratch.partial_json[position]);
            block.arguments = parse_tool_call_arguments(Some(&partial_json));
        }
        Some(Emission::End(position))
    }

    fn message_delta(&mut self, event: &JsonValue) -> Result<(), StreamFailure> {
        self.note_input_transformations(event);
        let delta = event.get("delta");
        if let Some(reason) = delta
            .and_then(|delta| delta.get("stop_reason"))
            .and_then(JsonValue::as_str)
            .filter(|reason| !reason.is_empty())
        {
            self.output.raw_stop_reason = Some(reason.to_owned());
            let (stop_reason, error_message) =
                map_stop_reason(reason, delta.and_then(|delta| delta.get("stop_details")))
                    .map_err(|error| StreamFailure::message(error.to_string()))?;
            self.output.stop_reason = stop_reason;
            if let Some(error_message) = error_message {
                self.output.error_message = Some(error_message);
            }
        }
        if let Some(usage) = event.get("usage").filter(|usage| usage.is_object()) {
            WireUsage::read(usage).overwrite(&mut self.output.usage);
        }
        update_total_and_cost(self.output, &self.usage_model);
        Ok(())
    }
}

/// Push `emission` to the stream with a snapshot of `output`.
fn emit(stream: &AssistantMessageEventStream, output: &AssistantMessage, emission: Emission) {
    stream.push_partial(output, |partial| match emission {
        Emission::Start(content_index) => match &output.content[content_index] {
            AssistantContentBlock::Text(_) => AssistantMessageEvent::TextStart {
                content_index,
                partial,
            },
            AssistantContentBlock::Thinking(_) => AssistantMessageEvent::ThinkingStart {
                content_index,
                partial,
            },
            AssistantContentBlock::ToolCall(_) => AssistantMessageEvent::ToolCallStart {
                content_index,
                partial,
            },
        },
        Emission::Delta(content_index, delta) => match &output.content[content_index] {
            AssistantContentBlock::Text(_) => AssistantMessageEvent::TextDelta {
                content_index,
                delta,
                partial,
            },
            AssistantContentBlock::Thinking(_) => AssistantMessageEvent::ThinkingDelta {
                content_index,
                delta,
                partial,
            },
            AssistantContentBlock::ToolCall(_) => AssistantMessageEvent::ToolCallDelta {
                content_index,
                delta,
                partial,
            },
        },
        Emission::End(content_index) => match &output.content[content_index] {
            AssistantContentBlock::Text(block) => AssistantMessageEvent::TextEnd {
                content_index,
                content: block.text.clone(),
                partial,
            },
            AssistantContentBlock::Thinking(block) => AssistantMessageEvent::ThinkingEnd {
                content_index,
                content: block.thinking.clone(),
                partial,
            },
            AssistantContentBlock::ToolCall(block) => AssistantMessageEvent::ToolCallEnd {
                content_index,
                tool_call: block.clone(),
                partial,
            },
        },
    });
}

/// The failure a finished stream's stop reason reports: none at all, or
/// an error or aborted stop.
fn check_stop_reason(
    output: &AssistantMessage,
    request_id: Option<&str>,
) -> Result<(), StreamFailure> {
    match output.stop_reason {
        StopReason::Pending => Err(StreamFailure::message(
            "Anthropic stream ended without a stop reason",
        )),
        StopReason::Aborted | StopReason::Error => {
            let message = output
                .error_message
                .clone()
                .filter(|message| !message.is_empty())
                .unwrap_or_else(|| "An unknown error occurred".to_owned());
            Err(StreamFailure {
                thrown: ErrorObject::new(message).thrown(),
                diagnostic: Box::new(ProviderError::StreamFailure(
                    stream_failure_from_stop_reason(output.raw_stop_reason.as_deref(), request_id),
                )),
            })
        }
        StopReason::Stop | StopReason::Length | StopReason::ToolUse | StopReason::Deferred => {
            Ok(())
        }
    }
}

/// The diagnostic recording the server's input transformations: the
/// `type`, `path` and `reason` of each.
fn input_transformations_diagnostic(
    transformations: &[JsonValue],
    timestamp: u64,
) -> AssistantMessageDiagnostic {
    let details: Vec<JsonValue> = transformations
        .iter()
        .map(|transformation| {
            let mut entry = JsonObject::new();
            for key in ["type", "path", "reason"] {
                if let Some(value) = transformation.get(key).filter(|value| !value.is_null()) {
                    entry.insert(key.to_owned(), value.clone());
                }
            }
            JsonValue::Object(entry)
        })
        .collect();
    let mut detail_object = JsonObject::new();
    detail_object.insert("transformations".into(), JsonValue::Array(details));
    AssistantMessageDiagnostic {
        kind: "anthropic_input_transformations".to_owned(),
        timestamp,
        error: None,
        details: Some(detail_object),
    }
}

/// The event loop of TS `stream`, from the first event to the final checks.
pub(crate) async fn consume(
    model: &Model,
    response: reqwest::Response,
    options: &AnthropicOptions,
    is_oauth: bool,
    current_tools: &[Tool],
    output: &mut AssistantMessage,
    stream: &AssistantMessageEventStream,
) -> Result<(), StreamFailure> {
    let request = &options.stream.request;
    let request_id = response
        .headers()
        .get("request-id")
        .or_else(|| response.headers().get("x-request-id"))
        .and_then(|value| value.to_str().ok())
        .map(str::to_owned);
    let mut fold = EventFold {
        model,
        is_oauth,
        current_tools,
        output,
        usage_model: model.clone(),
        input_transformations: None,
        scratch: BlockScratch::default(),
    };
    let mut events = AnthropicEvents::new(response, request.signal.clone());
    while let Some(event) = events
        .next()
        .await
        .map_err(|error| event_failure(&error, request_id.as_deref()))?
    {
        if let Some(observer) = &options.stream.on_provider_stream_event {
            observer(&event, model)
                .await
                .map_err(StreamFailure::plain)?;
        }
        if let Some(emission) = fold.apply(&event)? {
            emit(stream, fold.output, emission);
        }
    }
    let input_transformations = fold.input_transformations;

    if request
        .signal
        .as_ref()
        .is_some_and(eukhe_chord::context::AbortSignal::aborted)
    {
        return Err(StreamFailure::message("Request was aborted"));
    }
    check_stop_reason(output, request_id.as_deref())?;
    if let Some(transformations) = input_transformations.filter(|items| !items.is_empty()) {
        append_assistant_message_diagnostic(
            output,
            input_transformations_diagnostic(&transformations, now_ms()),
        );
    }
    Ok(())
}
