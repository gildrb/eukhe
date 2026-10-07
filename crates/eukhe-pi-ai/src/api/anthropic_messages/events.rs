//! Sending the request with provider retries, and folding the Anthropic
//! stream events into the assistant message (the `for await` loop of TS
//! `stream` and `mapStopReason`).

use std::collections::HashMap;
use std::sync::{Mutex, PoisonError};

use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, AssistantMessageEvent, JsonObject, JsonValue, Model,
    StopReason, TextContent, ThinkingContent, Tool, ToolCall,
};
use reqwest::header::HeaderMap;

use super::client::{RequestFailure, RequestOptions, SdkClient};
use super::params::from_claude_code_name;
use super::sse::{AnthropicEvents, EventStreamError};
use super::{model_compat, AnthropicOptions, StreamFailure};
use crate::models::calculate_cost;
use crate::utils::diagnostics::{append_assistant_message_diagnostic, ErrorObject, Thrown};
use crate::utils::event_stream::AssistantMessageEventStream;
use crate::utils::json_parse::{parse_json_with_repair, parse_streaming_json_object};
use crate::utils::now_ms;
use crate::utils::provider_retry::{retry_provider_request, ProviderRetryOptions};
use crate::utils::stream_failure::{
    classify_stream_failure, stream_failure_from_stop_reason, stream_failure_message,
    truncate_raw_payload, ConnectionErrorKind, ConnectionErrorProfile, ProviderConnectionError,
    ProviderError, StreamFailureError, StreamFailureInfo, StreamFailureKind,
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

/// TS `mapStopReason`.
fn map_stop_reason(
    reason: &str,
    stop_details: Option<&JsonValue>,
) -> Result<(StopReason, Option<String>), String> {
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
        other => Err(format!("Unhandled stop reason: {other}")),
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

/// The event loop of TS `stream`, from the first event to the final checks.
#[allow(clippy::too_many_lines)] // 1:1 port of the TS event loop.
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
    let mut usage_model = model.clone();
    let mut input_transformations: Option<Vec<JsonValue>> = None;
    let mut scratch = BlockScratch::default();
    let mut events = AnthropicEvents::new(response, request.signal.clone());

    loop {
        let event = match events.next().await {
            Ok(Some(event)) => event,
            Ok(None) => break,
            Err(error) => return Err(event_failure(&error, request_id.as_deref())),
        };
        if let Some(observer) = &options.stream.on_provider_stream_event {
            observer(&event, model)
                .await
                .map_err(StreamFailure::plain)?;
        }
        match event.get("type").and_then(JsonValue::as_str) {
            Some("message_start") => {
                let Some(message) = event.get("message") else {
                    return Err(type_error("id"));
                };
                if let Some(id) = message.get("id").and_then(JsonValue::as_str) {
                    output.response_id = Some(id.to_owned());
                }
                if let Some(JsonValue::Array(transformations)) =
                    message.get("input_transformations")
                {
                    input_transformations = Some(transformations.clone());
                }
                let response_model = message.get("model").and_then(JsonValue::as_str);
                if response_model != Some(model.id.as_str()) {
                    output.response_model = response_model.map(str::to_owned);
                }
                let fallback_cost = response_model
                    .filter(|response_model| *response_model != model.id)
                    .and_then(|response_model| {
                        model_compat(model)
                            .and_then(|compat| compat.allowed_fallback_models.as_ref())
                            .and_then(|fallbacks| {
                                fallbacks.iter().find(|fallback| {
                                    fallback.provider == model.provider
                                        && fallback.model == response_model
                                })
                            })
                            .map(|fallback| (response_model, fallback.cost.clone()))
                    });
                usage_model = match fallback_cost {
                    Some((response_model, cost)) => Model {
                        id: response_model.to_owned(),
                        cost,
                        ..model.clone()
                    },
                    None => model.clone(),
                };
                let Some(usage) = message.get("usage") else {
                    return Err(type_error("input_tokens"));
                };
                output.usage.input = token_count(usage.get("input_tokens")).unwrap_or(0);
                output.usage.output = token_count(usage.get("output_tokens")).unwrap_or(0);
                output.usage.cache_read =
                    token_count(usage.get("cache_read_input_tokens")).unwrap_or(0);
                output.usage.cache_write =
                    token_count(usage.get("cache_creation_input_tokens")).unwrap_or(0);
                output.usage.cache_write_1h = Some(
                    token_count(
                        usage
                            .get("cache_creation")
                            .and_then(|creation| creation.get("ephemeral_1h_input_tokens")),
                    )
                    .unwrap_or(0),
                );
                update_total_and_cost(output, &usage_model);
            }
            Some("content_block_start") => {
                let Some(block) = event.get("content_block") else {
                    return Err(type_error("type"));
                };
                let index = event.get("index").cloned();
                let new_block = match block.get("type").and_then(JsonValue::as_str) {
                    Some("fallback") => {
                        if !output.content.is_empty() {
                            return Err(StreamFailure::message(
                                "Anthropic performed an unsupported mid-output model fallback",
                            ));
                        }
                        continue;
                    }
                    Some("text") => AssistantContentBlock::Text(TextContent::new(
                        block.get("text").and_then(JsonValue::as_str).unwrap_or(""),
                    )),
                    Some("thinking") => AssistantContentBlock::Thinking(ThinkingContent {
                        thinking: block
                            .get("thinking")
                            .and_then(JsonValue::as_str)
                            .unwrap_or("")
                            .to_owned(),
                        thinking_signature: Some(
                            block
                                .get("signature")
                                .and_then(JsonValue::as_str)
                                .unwrap_or("")
                                .to_owned(),
                        ),
                        redacted: None,
                    }),
                    Some("redacted_thinking") => AssistantContentBlock::Thinking(ThinkingContent {
                        thinking: "[Reasoning redacted]".to_owned(),
                        thinking_signature: block
                            .get("data")
                            .and_then(JsonValue::as_str)
                            .map(str::to_owned),
                        redacted: Some(true),
                    }),
                    Some("tool_use") => {
                        let name = block.get("name").and_then(JsonValue::as_str).unwrap_or("");
                        AssistantContentBlock::ToolCall(ToolCall {
                            id: block
                                .get("id")
                                .and_then(JsonValue::as_str)
                                .unwrap_or("")
                                .to_owned(),
                            name: if is_oauth {
                                from_claude_code_name(name, current_tools)
                            } else {
                                name.to_owned()
                            },
                            arguments: match block.get("input") {
                                Some(JsonValue::Object(input)) => input.clone(),
                                _ => JsonObject::new(),
                            },
                            ..ToolCall::default()
                        })
                    }
                    _ => continue,
                };
                output.content.push(new_block);
                scratch.index.push(index);
                scratch.partial_json.push(String::new());
                let content_index = output.content.len() - 1;
                let partial = output.clone();
                stream.push(match &output.content[content_index] {
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
                });
            }
            Some("content_block_delta") => {
                let delta = event.get("delta");
                let Some(position) = scratch.find(event.get("index")) else {
                    continue;
                };
                match delta
                    .and_then(|delta| delta.get("type"))
                    .and_then(JsonValue::as_str)
                {
                    Some("text_delta") => {
                        if let AssistantContentBlock::Text(block) = &mut output.content[position] {
                            let text = js_concat(delta.and_then(|delta| delta.get("text")));
                            block.text.push_str(&text);
                            stream.push(AssistantMessageEvent::TextDelta {
                                content_index: position,
                                delta: text,
                                partial: output.clone(),
                            });
                        }
                    }
                    Some("thinking_delta") => {
                        if let AssistantContentBlock::Thinking(block) =
                            &mut output.content[position]
                        {
                            let text = js_concat(delta.and_then(|delta| delta.get("thinking")));
                            block.thinking.push_str(&text);
                            stream.push(AssistantMessageEvent::ThinkingDelta {
                                content_index: position,
                                delta: text,
                                partial: output.clone(),
                            });
                        }
                    }
                    Some("input_json_delta") => {
                        if let AssistantContentBlock::ToolCall(block) =
                            &mut output.content[position]
                        {
                            let text = js_concat(delta.and_then(|delta| delta.get("partial_json")));
                            let partial_json = &mut scratch.partial_json[position];
                            partial_json.push_str(&text);
                            block.arguments = parse_streaming_json_object(Some(partial_json));
                            stream.push(AssistantMessageEvent::ToolCallDelta {
                                content_index: position,
                                delta: text,
                                partial: output.clone(),
                            });
                        }
                    }
                    Some("signature_delta") => {
                        if let AssistantContentBlock::Thinking(block) =
                            &mut output.content[position]
                        {
                            let signature =
                                block.thinking_signature.get_or_insert_with(String::new);
                            signature.push_str(&js_concat(
                                delta.and_then(|delta| delta.get("signature")),
                            ));
                        }
                    }
                    _ => {}
                }
            }
            Some("content_block_stop") => {
                let Some(position) = scratch.find(event.get("index")) else {
                    continue;
                };
                scratch.index[position] = None;
                if let AssistantContentBlock::ToolCall(block) = &mut output.content[position] {
                    let partial_json = std::mem::take(&mut scratch.partial_json[position]);
                    block.arguments = parse_streaming_json_object(Some(&partial_json));
                }
                let partial = output.clone();
                stream.push(match &output.content[position] {
                    AssistantContentBlock::Text(block) => AssistantMessageEvent::TextEnd {
                        content_index: position,
                        content: block.text.clone(),
                        partial,
                    },
                    AssistantContentBlock::Thinking(block) => AssistantMessageEvent::ThinkingEnd {
                        content_index: position,
                        content: block.thinking.clone(),
                        partial,
                    },
                    AssistantContentBlock::ToolCall(block) => AssistantMessageEvent::ToolCallEnd {
                        content_index: position,
                        tool_call: block.clone(),
                        partial,
                    },
                });
            }
            Some("message_delta") => {
                if let Some(JsonValue::Array(transformations)) = event.get("input_transformations")
                {
                    input_transformations = Some(transformations.clone());
                }
                let delta = event.get("delta");
                if let Some(reason) = delta
                    .and_then(|delta| delta.get("stop_reason"))
                    .and_then(JsonValue::as_str)
                    .filter(|reason| !reason.is_empty())
                {
                    output.raw_stop_reason = Some(reason.to_owned());
                    let (stop_reason, error_message) =
                        map_stop_reason(reason, delta.and_then(|delta| delta.get("stop_details")))
                            .map_err(StreamFailure::message)?;
                    output.stop_reason = stop_reason;
                    if let Some(error_message) = error_message {
                        output.error_message = Some(error_message);
                    }
                }
                if let Some(usage) = event.get("usage").filter(|usage| usage.is_object()) {
                    if let Some(count) = token_count(usage.get("input_tokens")) {
                        output.usage.input = count;
                    }
                    if let Some(count) = token_count(usage.get("output_tokens")) {
                        output.usage.output = count;
                    }
                    if let Some(count) = token_count(usage.get("cache_read_input_tokens")) {
                        output.usage.cache_read = count;
                    }
                    if let Some(count) = token_count(usage.get("cache_creation_input_tokens")) {
                        output.usage.cache_write = count;
                    }
                    if let Some(count) = token_count(
                        usage
                            .get("cache_creation")
                            .and_then(|creation| creation.get("ephemeral_1h_input_tokens")),
                    ) {
                        output.usage.cache_write_1h = Some(count);
                    }
                    if let Some(count) = token_count(
                        usage
                            .get("output_tokens_details")
                            .and_then(|details| details.get("thinking_tokens")),
                    ) {
                        output.usage.reasoning = Some(count);
                    }
                }
                update_total_and_cost(output, &usage_model);
            }
            _ => {}
        }
    }

    if request
        .signal
        .as_ref()
        .is_some_and(eukhe_chord::context::AbortSignal::aborted)
    {
        return Err(StreamFailure::message("Request was aborted"));
    }
    match output.stop_reason {
        StopReason::Pending => {
            return Err(StreamFailure::message(
                "Anthropic stream ended without a stop reason",
            ));
        }
        StopReason::Aborted | StopReason::Error => {
            let message = output
                .error_message
                .clone()
                .filter(|message| !message.is_empty())
                .unwrap_or_else(|| "An unknown error occurred".to_owned());
            return Err(StreamFailure {
                thrown: ErrorObject::new(message).thrown(),
                diagnostic: Box::new(ProviderError::StreamFailure(
                    stream_failure_from_stop_reason(
                        output.raw_stop_reason.as_deref(),
                        request_id.as_deref(),
                    ),
                )),
            });
        }
        StopReason::Stop | StopReason::Length | StopReason::ToolUse | StopReason::Deferred => {}
    }
    if let Some(transformations) = input_transformations.filter(|items| !items.is_empty()) {
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
        append_assistant_message_diagnostic(
            output,
            eukhe_types::pi_ai::AssistantMessageDiagnostic {
                kind: "anthropic_input_transformations".to_owned(),
                timestamp: now_ms(),
                error: None,
                details: Some(detail_object),
            },
        );
    }
    Ok(())
}
