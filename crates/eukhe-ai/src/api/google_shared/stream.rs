//! The request builder and stream loop of `google-generative-ai.ts` and
//! `google-vertex.ts`. The two TS modules carry identical copies of
//! `buildParams` and of the `stream` body (differing only in the API id and
//! two error texts); the Rust port keeps one implementation, parameterized
//! by [`GoogleApiKind`].

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};

use eukhe_chord::context::AbortSignal;
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, AssistantMessageEvent, DoneReason, ErrorReason,
    JsonObject, JsonValue, Model, StopReason, TextContent, ThinkingContent, ToolCall,
    TranscriptContext, Usage,
};
use serde_json::json;

use super::genai::{GenerateContentStream, GoogleGenAi};
use super::options::GoogleRequestOptions;
use super::{
    convert_messages, convert_tools, get_disabled_google_thinking_config, is_thinking_part,
    map_stop_reason, resolve_google_function_calling_mode, retain_thought_signature,
    retry_google_request, supports_google_strict_tool_sampling, to_google_sdk_thinking_level,
    GoogleRetryOptions, ToolSchemaField,
};
use crate::models::calculate_cost;
use crate::utils::diagnostics::{ErrorObject, Thrown};
use crate::utils::error_body::{format_provider_error, normalize_provider_error};
use crate::utils::event_stream::AssistantMessageEventStream;
use crate::utils::js::{js_to_string, json_stringify};
use crate::utils::now_ms;
use crate::utils::sanitize_unicode::sanitize_surrogates;
use crate::utils::stream_failure::{
    record_stream_failure, stream_failure_from_stop_reason, ProviderError,
};
use crate::utils::text::get_system_message_text;
use crate::utils::transcript::{
    collapse_system_messages, get_current_tools, get_initial_system_message,
};

/// Which Google wire API a stream serves.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum GoogleApiKind {
    GenerativeAi,
    Vertex,
}

/// Counters for generating unique tool call IDs (one per TS module).
static GENERATIVE_AI_TOOL_CALL_COUNTER: AtomicU64 = AtomicU64::new(0);
static VERTEX_TOOL_CALL_COUNTER: AtomicU64 = AtomicU64::new(0);

impl GoogleApiKind {
    const fn api(self) -> &'static str {
        match self {
            Self::GenerativeAi => "google-generative-ai",
            Self::Vertex => "google-vertex",
        }
    }

    const fn custom_fetch_message(self) -> &'static str {
        match self {
            Self::GenerativeAi => {
                "Custom fetch is not supported by the Google Generative AI adapter"
            }
            Self::Vertex => "Custom fetch is not supported by the Google Vertex adapter",
        }
    }

    const fn no_finish_reason_message(self) -> &'static str {
        match self {
            Self::GenerativeAi => "Google stream ended without a finish reason",
            Self::Vertex => "Google Vertex stream ended without a finish reason",
        }
    }

    fn next_tool_call_number(self) -> u64 {
        let counter = match self {
            Self::GenerativeAi => &GENERATIVE_AI_TOOL_CALL_COUNTER,
            Self::Vertex => &VERTEX_TOOL_CALL_COUNTER,
        };
        counter.fetch_add(1, Ordering::Relaxed) + 1
    }
}

/// TS `buildParams(model, context, options)`: the `GenerateContentParameters`
/// handed to `onPayload` and the SDK. The TS `config.abortSignal` is not
/// part of the JSON; the signal travels to the client separately.
///
/// # Errors
///
/// Tool constrained-sampling errors, unsupported thinking-level mappings, and
/// `Request aborted` when the signal has already aborted.
pub(crate) fn build_params(
    model: &Model,
    context: &TranscriptContext,
    options: &GoogleRequestOptions,
) -> Result<JsonValue, Thrown> {
    let contents = convert_messages(model, context);
    let initial_system_message = get_initial_system_message(context.messages());
    let current_tools = get_current_tools(context.messages());

    let mut config = JsonObject::new();
    if let Some(temperature) = options.stream.temperature {
        config.insert("temperature".into(), json!(temperature));
    }
    if let Some(max_tokens) = options.stream.max_tokens {
        config.insert("maxOutputTokens".into(), json!(max_tokens));
    }

    let supports_strict_mode = supports_google_strict_tool_sampling(&model.id);
    let function_calling_mode = if current_tools.is_empty() {
        None
    } else {
        resolve_google_function_calling_mode(
            &current_tools,
            options.tool_choice.as_deref(),
            supports_strict_mode,
        )?
    };
    let system_instruction = initial_system_message
        .map(get_system_message_text)
        .unwrap_or_default();
    if !system_instruction.is_empty() {
        config.insert(
            "systemInstruction".into(),
            sanitize_surrogates(&system_instruction).into_owned().into(),
        );
    }
    if !current_tools.is_empty() {
        let tools = convert_tools(
            &current_tools,
            ToolSchemaField::ParametersJsonSchema,
            supports_strict_mode,
        )?;
        config.insert(
            "tools".into(),
            tools.map_or(JsonValue::Null, JsonValue::Array),
        );
    }
    if let Some(mode) = function_calling_mode {
        config.insert(
            "toolConfig".into(),
            json!({ "functionCallingConfig": { "mode": mode.as_str() } }),
        );
    }

    match &options.thinking {
        Some(thinking) if thinking.enabled && model.reasoning => {
            let mut thinking_config = JsonObject::new();
            thinking_config.insert("includeThoughts".into(), true.into());
            if let Some(level) = thinking.level {
                thinking_config.insert(
                    "thinkingLevel".into(),
                    to_google_sdk_thinking_level(level).into(),
                );
            } else if let Some(budget) = thinking.budget_tokens {
                thinking_config.insert("thinkingBudget".into(), budget.into());
            }
            config.insert("thinkingConfig".into(), JsonValue::Object(thinking_config));
        }
        Some(thinking) if model.reasoning && !thinking.enabled => {
            config.insert(
                "thinkingConfig".into(),
                get_disabled_google_thinking_config(model)?,
            );
        }
        Some(_) | None => {}
    }

    if options.signal().is_some_and(AbortSignal::aborted) {
        return Err(ErrorObject::new("Request aborted").thrown());
    }

    Ok(json!({
        "model": model.id,
        "contents": contents,
        "config": JsonValue::Object(config),
    }))
}

/// Creates the SDK client for a request (TS `createClient...`).
pub(crate) type CreateClient =
    Box<dyn FnOnce(&Model, &GoogleRequestOptions) -> Result<GoogleGenAi, Thrown> + Send>;

/// A failure of the stream body: a thrown error, or an error finish reason
/// (kept apart for the eukhe stream-failure diagnostic).
enum StreamError {
    Thrown(Thrown),
    FinishReason { error: Thrown, raw: Option<String> },
}

impl From<Thrown> for StreamError {
    fn from(error: Thrown) -> Self {
        Self::Thrown(error)
    }
}

/// The open text/thinking block (always the last content block).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OpenBlock {
    Text,
    Thinking,
}

fn empty_output(kind: GoogleApiKind, model: &Model) -> AssistantMessage {
    AssistantMessage {
        content: Vec::new(),
        api: kind.api().to_owned(),
        provider: model.provider.clone(),
        model: model.id.clone(),
        response_model: None,
        response_id: None,
        provider_thinking_level: None,
        thinking_level: None,
        diagnostics: None,
        usage: Usage::default(),
        stop_reason: StopReason::Pending,
        deferred: None,
        error_message: None,
        raw_stop_reason: None,
        end_turn: None,
        timestamp: now_ms(),
        duration_ms: None,
    }
}

/// TS `stream(model, context, options)` of both Google modules.
pub(crate) fn run_google_stream(
    kind: GoogleApiKind,
    model: &Model,
    context: &TranscriptContext,
    options: Result<GoogleRequestOptions, Thrown>,
    create_client: CreateClient,
) -> AssistantMessageEventStream {
    let stream = AssistantMessageEventStream::new();
    let normalized_context = collapse_system_messages(context.clone());
    let model = model.clone();
    let events = stream.clone();
    tokio::spawn(async move {
        let mut output = empty_output(kind, &model);
        let signal = options
            .as_ref()
            .ok()
            .and_then(|options| options.signal().cloned());
        let result = match options {
            Ok(options) => {
                run(
                    kind,
                    &model,
                    &normalized_context,
                    &options,
                    create_client,
                    &mut output,
                    &events,
                )
                .await
            }
            Err(error) => Err(StreamError::Thrown(error)),
        };
        match result {
            Ok(()) => {
                let reason = match output.stop_reason {
                    StopReason::Length => DoneReason::Length,
                    StopReason::ToolUse => DoneReason::ToolUse,
                    StopReason::Deferred => DoneReason::Deferred,
                    StopReason::Stop
                    | StopReason::Pending
                    | StopReason::Error
                    | StopReason::Aborted => DoneReason::Stop,
                };
                events.push(AssistantMessageEvent::Done {
                    reason,
                    message: output,
                });
                events.end(None);
            }
            Err(error) => {
                let aborted = signal.as_ref().is_some_and(AbortSignal::aborted);
                output.stop_reason = if aborted {
                    StopReason::Aborted
                } else {
                    StopReason::Error
                };
                let (thrown_error, provider_error) = match error {
                    StreamError::Thrown(error) => {
                        let provider_error = provider_error_for(&error, aborted);
                        (error, provider_error)
                    }
                    StreamError::FinishReason { error, raw } => (
                        error,
                        ProviderError::StreamFailure(stream_failure_from_stop_reason(
                            raw.as_deref(),
                            None,
                        )),
                    ),
                };
                output.error_message = Some(format_provider_error(
                    &normalize_provider_error(&thrown_error),
                    None,
                ));
                // eukhe addition: the `provider_stream_failure` diagnostic.
                record_stream_failure(
                    (&model.provider, &model.id, &model.api),
                    &mut output,
                    &provider_error,
                );
                let reason = if aborted {
                    ErrorReason::Aborted
                } else {
                    ErrorReason::Error
                };
                events.push(AssistantMessageEvent::Error {
                    reason,
                    error: output,
                });
                events.end(None);
            }
        }
    });
    stream
}

/// eukhe addition: classify a thrown stream error for the stream-failure
/// diagnostic. `ApiError`s carry the HTTP status and the JSON error body as
/// their message.
fn provider_error_for(error: &Thrown, aborted: bool) -> ProviderError {
    if aborted {
        return ProviderError::Aborted;
    }
    if let Some(object) = error.downcast_ref::<ErrorObject>() {
        let status = object
            .status
            .clone()
            .flatten()
            .and_then(|status| status.as_u64())
            .and_then(|status| u16::try_from(status).ok());
        if let (Some(status), "ApiError") = (status, object.name.as_str()) {
            let mut provider_error =
                ProviderError::from_http_status_body(status, &object.message, HashMap::default());
            if let ProviderError::Http(http) = &mut provider_error {
                http.sdk_name = Some("ApiError".to_owned());
                http.body = None;
                http.request_id = None;
            }
            return provider_error;
        }
    }
    ProviderError::Message(error.to_string())
}

#[allow(clippy::too_many_arguments)] // The TS closure state, passed explicitly.
async fn run(
    kind: GoogleApiKind,
    model: &Model,
    context: &TranscriptContext,
    options: &GoogleRequestOptions,
    create_client: CreateClient,
    output: &mut AssistantMessage,
    stream: &AssistantMessageEventStream,
) -> Result<(), StreamError> {
    if options.stream.request.fetch.is_some() {
        return Err(ErrorObject::new(kind.custom_fetch_message())
            .thrown()
            .into());
    }
    let client = create_client(model, options)?;
    let mut params = build_params(model, context, options)?;
    if let Some(on_payload) = &options.stream.request.on_payload {
        if let Some(next) = on_payload(params.clone(), model).await? {
            params = next;
        }
    }
    let signal = options.signal();
    let retry_options = GoogleRetryOptions {
        max_retries: options.stream.request.max_retries,
        max_retry_delay_ms: options.stream.request.max_retry_delay_ms,
        signal: signal.cloned(),
    };
    let mut google_stream: GenerateContentStream = retry_google_request(
        || client.generate_content_stream(&params, signal),
        Some(&retry_options),
    )
    .await?;

    stream.push(AssistantMessageEvent::Start {
        partial: output.clone(),
    });
    let mut current: Option<OpenBlock> = None;
    while let Some(chunk) = google_stream.next().await {
        let chunk = chunk?;
        if let Some(observer) = &options.stream.on_provider_stream_event {
            observer(&chunk, model).await?;
        }
        handle_chunk(kind, model, &chunk, output, stream, &mut current)?;
    }
    close_block(output, stream, &mut current);

    if signal.is_some_and(AbortSignal::aborted) {
        return Err(ErrorObject::new("Request was aborted").thrown().into());
    }
    match output.stop_reason {
        StopReason::Pending => Err(ErrorObject::new(kind.no_finish_reason_message())
            .thrown()
            .into()),
        StopReason::Aborted | StopReason::Error => {
            let message = output.raw_stop_reason.as_ref().map_or_else(
                || "An unknown error occurred".to_owned(),
                |raw| format!("Provider stopped with: {raw}"),
            );
            Err(StreamError::FinishReason {
                error: ErrorObject::new(message).thrown(),
                raw: output.raw_stop_reason.clone(),
            })
        }
        StopReason::Stop | StopReason::Length | StopReason::ToolUse | StopReason::Deferred => {
            Ok(())
        }
    }
}

/// Emit the `*_end` event of the open text/thinking block.
fn close_block(
    output: &AssistantMessage,
    stream: &AssistantMessageEventStream,
    current: &mut Option<OpenBlock>,
) {
    let Some(open) = current.take() else {
        return;
    };
    let index = output.content.len() - 1;
    let event = match (open, &output.content[index]) {
        (OpenBlock::Text, AssistantContentBlock::Text(text)) => AssistantMessageEvent::TextEnd {
            content_index: index,
            content: text.text.clone(),
            partial: output.clone(),
        },
        (OpenBlock::Thinking, AssistantContentBlock::Thinking(thinking)) => {
            AssistantMessageEvent::ThinkingEnd {
                content_index: index,
                content: thinking.thinking.clone(),
                partial: output.clone(),
            }
        }
        _ => return,
    };
    stream.push(event);
}

/// JS truthiness of a JSON value.
fn truthy(value: Option<&JsonValue>) -> bool {
    match value {
        None | Some(JsonValue::Null) => false,
        Some(JsonValue::Bool(flag)) => *flag,
        Some(JsonValue::Number(number)) => number.as_f64().is_some_and(|n| n != 0.0 && !n.is_nan()),
        Some(JsonValue::String(text)) => !text.is_empty(),
        Some(JsonValue::Array(_) | JsonValue::Object(_)) => true,
    }
}

/// `value || 0` for a token count.
fn count(object: &JsonValue, key: &str) -> u64 {
    object.get(key).and_then(JsonValue::as_u64).unwrap_or(0)
}

/// `text += value` / the event `delta` of a part's `text`.
fn part_text(value: &JsonValue) -> String {
    match value {
        JsonValue::String(text) => text.clone(),
        other => js_to_string(other),
    }
}

fn handle_chunk(
    kind: GoogleApiKind,
    model: &Model,
    chunk: &JsonValue,
    output: &mut AssistantMessage,
    stream: &AssistantMessageEventStream,
    current: &mut Option<OpenBlock>,
) -> Result<(), Thrown> {
    // `output.responseId ||= chunk.responseId`.
    if output.response_id.as_deref().is_none_or(str::is_empty) {
        output.response_id = chunk
            .get("responseId")
            .and_then(JsonValue::as_str)
            .map(str::to_owned);
    }
    let candidate = chunk
        .get("candidates")
        .and_then(JsonValue::as_array)
        .and_then(|candidates| candidates.first());
    let parts = candidate
        .and_then(|candidate| candidate.get("content"))
        .and_then(|content| content.get("parts"));
    if truthy(parts) {
        let Some(parts) = parts.and_then(JsonValue::as_array) else {
            return Err(
                ErrorObject::named("TypeError", "candidate.content.parts is not iterable").thrown(),
            );
        };
        for part in parts {
            handle_part(kind, part, output, stream, current);
        }
    }

    if let Some(candidate) = candidate {
        if truthy(candidate.get("finishReason")) {
            let finish_reason = part_text(&candidate["finishReason"]);
            output.stop_reason = map_stop_reason(&finish_reason)?;
            output.raw_stop_reason = Some(finish_reason);
            let has_tool_call = output
                .content
                .iter()
                .any(|block| matches!(block, AssistantContentBlock::ToolCall(_)));
            if has_tool_call && output.stop_reason == StopReason::Stop {
                output.stop_reason = StopReason::ToolUse;
            }
        }
    }

    if let Some(usage) = chunk
        .get("usageMetadata")
        .filter(|usage| truthy(Some(usage)))
    {
        let cached = count(usage, "cachedContentTokenCount");
        let thoughts = count(usage, "thoughtsTokenCount");
        output.usage = Usage {
            input: count(usage, "promptTokenCount").saturating_sub(cached),
            output: count(usage, "candidatesTokenCount") + thoughts,
            cache_read: cached,
            cache_write: 0,
            cache_write_1h: None,
            reasoning: Some(thoughts),
            total_tokens: count(usage, "totalTokenCount"),
            cost: eukhe_types::pi_ai::UsageCost::default(),
        };
        calculate_cost(model, &mut output.usage);
    }
    Ok(())
}

fn handle_part(
    kind: GoogleApiKind,
    part: &JsonValue,
    output: &mut AssistantMessage,
    stream: &AssistantMessageEventStream,
    current: &mut Option<OpenBlock>,
) {
    let signature = part.get("thoughtSignature").and_then(JsonValue::as_str);
    if let Some(text) = part.get("text") {
        let text = part_text(text);
        let is_thinking = is_thinking_part(part.get("thought"), signature);
        let wanted = if is_thinking {
            OpenBlock::Thinking
        } else {
            OpenBlock::Text
        };
        if *current != Some(wanted) {
            close_block(output, stream, current);
            if is_thinking {
                output
                    .content
                    .push(AssistantContentBlock::Thinking(ThinkingContent::default()));
                stream.push(AssistantMessageEvent::ThinkingStart {
                    content_index: output.content.len() - 1,
                    partial: output.clone(),
                });
            } else {
                output
                    .content
                    .push(AssistantContentBlock::Text(TextContent::new("")));
                stream.push(AssistantMessageEvent::TextStart {
                    content_index: output.content.len() - 1,
                    partial: output.clone(),
                });
            }
            *current = Some(wanted);
        }
        let index = output.content.len() - 1;
        match &mut output.content[index] {
            AssistantContentBlock::Thinking(thinking) => {
                thinking.thinking.push_str(&text);
                thinking.thinking_signature =
                    retain_thought_signature(thinking.thinking_signature.take(), signature);
                stream.push(AssistantMessageEvent::ThinkingDelta {
                    content_index: index,
                    delta: text,
                    partial: output.clone(),
                });
            }
            AssistantContentBlock::Text(block) => {
                block.text.push_str(&text);
                block.text_signature =
                    retain_thought_signature(block.text_signature.take(), signature);
                stream.push(AssistantMessageEvent::TextDelta {
                    content_index: index,
                    delta: text,
                    partial: output.clone(),
                });
            }
            AssistantContentBlock::ToolCall(_) => {}
        }
    }

    let function_call = part.get("functionCall");
    if let Some(function_call) = function_call.filter(|call| truthy(Some(call))) {
        close_block(output, stream, current);
        push_tool_call(kind, function_call, signature, output, stream);
    }
}

/// A `functionCall` part: a complete tool call with its three events.
fn push_tool_call(
    kind: GoogleApiKind,
    function_call: &JsonValue,
    signature: Option<&str>,
    output: &mut AssistantMessage,
    stream: &AssistantMessageEventStream,
) {
    // Generate a unique ID if none is provided or it is a duplicate.
    let provided_id = function_call
        .get("id")
        .filter(|id| truthy(Some(id)))
        .map(part_text);
    let needs_new_id = provided_id.as_ref().is_none_or(|provided| {
        output.content.iter().any(
            |block| matches!(block, AssistantContentBlock::ToolCall(call) if call.id == *provided),
        )
    });
    let name_value = function_call.get("name");
    let tool_call_id = match provided_id {
        Some(provided) if !needs_new_id => provided,
        _ => format!(
            "{}_{}_{}",
            name_value.map_or_else(|| "undefined".to_owned(), part_text),
            now_ms(),
            kind.next_tool_call_number()
        ),
    };
    let tool_call = ToolCall {
        id: tool_call_id,
        name: if truthy(name_value) {
            name_value.map(part_text).unwrap_or_default()
        } else {
            String::new()
        },
        arguments: function_call
            .get("args")
            .and_then(JsonValue::as_object)
            .cloned()
            .unwrap_or_default(),
        thought_signature: signature.filter(|s| !s.is_empty()).map(str::to_owned),
        namespace: None,
    };
    let delta = json_stringify(&JsonValue::Object(tool_call.arguments.clone()));
    output
        .content
        .push(AssistantContentBlock::ToolCall(tool_call.clone()));
    let index = output.content.len() - 1;
    stream.push(AssistantMessageEvent::ToolCallStart {
        content_index: index,
        partial: output.clone(),
    });
    stream.push(AssistantMessageEvent::ToolCallDelta {
        content_index: index,
        delta,
        partial: output.clone(),
    });
    stream.push(AssistantMessageEvent::ToolCallEnd {
        content_index: index,
        tool_call,
        partial: output.clone(),
    });
}
