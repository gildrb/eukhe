//! `OpenAI` Chat Completions wire API (`openai-completions`). Port of
//! `api/openai-completions.ts`.
//!
//! API-specific stream options arrive in [`ProviderStreamOptions::extra`]
//! under their TS names: `toolChoice`, `reasoningEffort`, `thinkingBudgets`
//! (see [`OpenAICompletionsOptions`]).
//!
//! eukhe additions on top of v1.0.4: the `prime-inference` gateway
//! detection (compat), explicit prompt-cache breakpoints on marked user text
//! blocks under the Anthropic cache-control format with the four-mark
//! budget, the `service_tier` request field and response-tier pricing, and
//! the `provider_stream_failure` diagnostic on failed streams.

mod compat;
mod convert;
mod params;
mod streaming;
#[cfg(test)]
mod tests;

use std::sync::Arc;

use eukhe_chord::context::AbortSignal;
use futures::StreamExt;
use serde::de::DeserializeOwned;

use self::compat::{get_compat, ResolvedCompat};
use self::params::{build_params, resolve_cache_retention};
use self::streaming::StreamState;
use super::cache_breakpoints::excess_breakpoints_error;
use super::constrained_sampling::create_grammar_tool_input_properties;
use super::github_copilot_headers::{build_copilot_dynamic_headers, has_copilot_vision_input};
use super::openai_responses::apply_service_tier_pricing;
use super::openai_sdk::{
    stream_failure_of, OpenAiClient, OpenAiClientConfig, OpenAiClientKind, OpenAiRequestOptions,
};
use super::simple_options::build_base_options;
use super::ProviderStreams;
use crate::models::clamp_thinking_level;
use crate::types::{
    AssistantMessage, AssistantMessageEvent, CacheControlFormat, CacheRetention, DoneReason,
    ErrorReason, JsonValue, Model, ModelThinkingLevel, ProviderHeaders, ProviderResponse,
    ProviderStreamOptions, SimpleStreamOptions, StopReason, StreamOptions, ThinkingBudgets,
    ThinkingLevel, TranscriptContext, Usage,
};
use crate::utils::diagnostics::{ErrorObject, SdkValue, Thrown};
use crate::utils::error_body::{format_provider_error, normalize_provider_error};
use crate::utils::event_stream::AssistantMessageEventStream;
use crate::utils::headers::headers_to_record;
use crate::utils::js::js_to_string;
use crate::utils::now_ms;
use crate::utils::pi_user_agent::get_pi_user_agent;
use crate::utils::provider_retry::{retry_provider_request, ProviderRetryOptions};
use crate::utils::stream_failure::{
    record_stream_failure, stream_drop_failure, OpenStreamBlock, ProviderError, StreamFailureError,
};
use crate::utils::transcript::{get_declared_tools, resolve_transcript};

/// TS `OpenAICompletionsOptions`: the shared stream options plus the
/// completions-specific fields.
#[derive(Debug, Clone, Default)]
pub struct OpenAICompletionsOptions {
    pub stream: StreamOptions,
    /// `ChatCompletionToolChoiceOption`: `"auto"`, `"none"`, `"required"`, or
    /// `{ type: "function", function: { name } }`.
    pub tool_choice: Option<JsonValue>,
    pub reasoning_effort: Option<ThinkingLevel>,
    /// Token budgets per thinking level. Used with
    /// `compat.thinkingTokenBudgetField`/`supportsThinkingTokenBudget` or a
    /// `{ "$var": "thinking.budget" }` chat-template value.
    pub thinking_budgets: Option<ThinkingBudgets>,
}

/// An invalid API-specific option in [`ProviderStreamOptions::extra`].
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("Invalid openai-completions option \"{key}\": {message}")]
pub struct InvalidOptionError {
    pub key: String,
    pub message: String,
}

fn extra_option<T: DeserializeOwned>(
    options: &ProviderStreamOptions,
    key: &str,
) -> Result<Option<T>, InvalidOptionError> {
    match options.extra.get(key) {
        None | Some(JsonValue::Null) => Ok(None),
        Some(value) => serde_json::from_value(value.clone())
            .map(Some)
            .map_err(|error| InvalidOptionError {
                key: key.to_owned(),
                message: error.to_string(),
            }),
    }
}

impl OpenAICompletionsOptions {
    /// Read the completions keys from `options.extra`.
    ///
    /// # Errors
    ///
    /// A present key whose value has the wrong shape.
    pub fn from_provider_options(
        options: ProviderStreamOptions,
    ) -> Result<Self, InvalidOptionError> {
        let tool_choice = options.extra.get("toolChoice").cloned();
        let reasoning_effort = extra_option(&options, "reasoningEffort")?;
        let thinking_budgets = extra_option(&options, "thinkingBudgets")?;
        Ok(Self {
            stream: options.stream,
            tool_choice,
            reasoning_effort,
            thinking_budgets,
        })
    }
}

fn has_header(headers: Option<&ProviderHeaders>, name: &str) -> bool {
    headers.is_some_and(|headers| {
        headers.iter().any(|(key, value)| {
            key.eq_ignore_ascii_case(name)
                && value
                    .as_deref()
                    .is_some_and(|value| !crate::utils::js::js_trim(value).is_empty())
        })
    })
}

/// TS `getClientApiKey`.
fn get_client_api_key(
    provider: &str,
    api_key: Option<&str>,
    headers: Option<&ProviderHeaders>,
) -> Result<String, Thrown> {
    if let Some(api_key) = api_key.filter(|key| !key.is_empty()) {
        return Ok(api_key.to_owned());
    }
    if has_header(headers, "authorization") || has_header(headers, "cf-aig-authorization") {
        return Ok("unused".to_owned());
    }
    Err(ErrorObject::new(format!("No API key for provider: {provider}")).thrown())
}

/// TS `createClient`: the SDK client with pi's default headers.
fn create_client(
    model: &Model,
    context: &TranscriptContext,
    api_key: String,
    options_headers: Option<&ProviderHeaders>,
    fetch: Option<crate::types::FetchFunction>,
    session_id: Option<&str>,
    compat: &ResolvedCompat,
) -> OpenAiClient {
    let mut headers = ProviderHeaders::new();
    headers.insert("User-Agent".into(), Some(get_pi_user_agent().to_owned()));
    for (name, value) in model.headers.iter().flatten() {
        headers.insert(name.clone(), Some(value.clone()));
    }
    if model.provider == "github-copilot" {
        let has_images = has_copilot_vision_input(context.messages());
        for (name, value) in build_copilot_dynamic_headers(context.messages(), has_images) {
            headers.insert(name, Some(value));
        }
    }

    if let Some(session_id) = session_id.filter(|id| !id.is_empty()) {
        if compat.send_session_affinity_headers {
            use crate::types::SessionAffinityFormat;
            match compat.session_affinity_format {
                SessionAffinityFormat::OpenRouter => {
                    headers.insert("x-session-id".into(), Some(session_id.to_owned()));
                }
                SessionAffinityFormat::OpenAI | SessionAffinityFormat::OpenAINoSession => {
                    if compat.session_affinity_format == SessionAffinityFormat::OpenAI {
                        headers.insert("session_id".into(), Some(session_id.to_owned()));
                    }
                    headers.insert("x-client-request-id".into(), Some(session_id.to_owned()));
                    headers.insert("x-session-affinity".into(), Some(session_id.to_owned()));
                }
            }
        }
    }

    // Merge options headers last so they can override defaults.
    for (name, value) in options_headers.into_iter().flatten() {
        headers.insert(name.clone(), value.clone());
    }

    OpenAiClient::new(OpenAiClientConfig {
        kind: OpenAiClientKind::OpenAI,
        api_key,
        base_url: model.base_url.clone(),
        default_headers: headers,
        default_query: Vec::new(),
        fetch,
    })
}

fn empty_output(model: &Model) -> AssistantMessage {
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
        stop_reason: StopReason::Pending,
        deferred: None,
        error_message: None,
        raw_stop_reason: None,
        end_turn: None,
        timestamp: now_ms(),
    }
}

fn aborted(signal: Option<&AbortSignal>) -> bool {
    signal.is_some_and(AbortSignal::aborted)
}

/// TS `stream` with typed options.
///
/// Must be called inside a tokio runtime.
#[must_use]
pub fn stream_with_options(
    model: &Model,
    context: &TranscriptContext,
    options: OpenAICompletionsOptions,
) -> AssistantMessageEventStream {
    let compat = get_compat(model);
    // eukhe addition: too many explicit cache breakpoints fail before the request is built.
    if compat.cache_control_format == Some(CacheControlFormat::Anthropic) {
        if let Some(error) = excess_breakpoints_error(model, context.messages()) {
            return error;
        }
    }
    let stream = AssistantMessageEventStream::new();
    let normalized_context =
        resolve_transcript(context.clone(), compat.supports_mid_convo_system_messages);
    let model = model.clone();
    let target = stream.clone();
    tokio::spawn(async move {
        run(&model, &normalized_context, &options, &compat, &target).await;
    });
    stream
}

/// The failure a run ends with: the thrown error plus the classification
/// the eukhe stream-failure diagnostic records.
struct RunError {
    error: Thrown,
    /// eukhe addition: set when the stream ended without its stop signal.
    stream_drop: Option<OpenStreamBlock>,
}

impl From<Thrown> for RunError {
    fn from(error: Thrown) -> Self {
        Self {
            error,
            stream_drop: None,
        }
    }
}

fn error_message(message: &str) -> Thrown {
    ErrorObject::new(message).thrown()
}

async fn run(
    model: &Model,
    context: &TranscriptContext,
    options: &OpenAICompletionsOptions,
    compat: &ResolvedCompat,
    stream: &AssistantMessageEventStream,
) {
    let request = &options.stream.request;
    let setup = get_client_api_key(
        &model.provider,
        request.api_key.as_deref(),
        request.headers.as_ref(),
    )
    .and_then(|api_key| {
        create_grammar_tool_input_properties(
            Some(&get_declared_tools(context.messages())),
            compat.supports_openai_grammar_tools,
        )
        .map(|properties| (api_key, properties))
        .map_err(Thrown::from)
    });
    let (api_key, grammar_tool_input_properties) = match setup {
        Ok(setup) => setup,
        Err(error) => {
            let mut output = empty_output(model);
            fail(model, options, &mut output, &error.into(), stream);
            return;
        }
    };
    let mut state = StreamState::new(
        empty_output(model),
        stream,
        model,
        &grammar_tool_input_properties,
    );
    let result = run_stream(
        model,
        context,
        options,
        compat,
        api_key,
        &grammar_tool_input_properties,
        &mut state,
    )
    .await;
    match result {
        Ok(()) => {
            let reason = match state.output.stop_reason {
                StopReason::Length => DoneReason::Length,
                StopReason::ToolUse => DoneReason::ToolUse,
                StopReason::Deferred => DoneReason::Deferred,
                StopReason::Stop
                | StopReason::Pending
                | StopReason::Error
                | StopReason::Aborted => DoneReason::Stop,
            };
            let message = state.output.clone();
            stream.push(AssistantMessageEvent::Done {
                reason,
                message: message.clone(),
            });
            stream.end(Some(message));
        }
        Err(error) => {
            state.apply_streamed_reasoning_details();
            let mut output = std::mem::replace(&mut state.output, empty_output(model));
            fail(model, options, &mut output, &error, stream);
        }
    }
}

/// The TS `catch` block: settle the message as `error`/`aborted` and emit
/// the error event.
fn fail(
    model: &Model,
    options: &OpenAICompletionsOptions,
    output: &mut AssistantMessage,
    run_error: &RunError,
    stream: &AssistantMessageEventStream,
) {
    let error = &run_error.error;
    let is_aborted = aborted(options.stream.request.signal.as_ref());
    output.stop_reason = if is_aborted {
        StopReason::Aborted
    } else {
        StopReason::Error
    };
    let mut message = format_provider_error(&normalize_provider_error(error), None);
    // Some providers via OpenRouter give additional information in this
    // field; append it only when the normalized message lacks it.
    if let Some(raw) = raw_error_metadata(error) {
        if !message.contains(&raw) {
            message.push('\n');
            message.push_str(&raw);
        }
    }
    output.error_message = Some(message.clone());

    // eukhe addition: the `provider_stream_failure` diagnostic.
    let provider_error = to_provider_error(
        error,
        &message,
        is_aborted,
        run_error.stream_drop,
        output.raw_stop_reason.as_deref(),
    );
    record_stream_failure(
        (&model.provider, &model.id, &model.api),
        output,
        &provider_error,
    );

    let reason = if is_aborted {
        ErrorReason::Aborted
    } else {
        ErrorReason::Error
    };
    stream.push(AssistantMessageEvent::Error {
        reason,
        error: output.clone(),
    });
    stream.end(Some(output.clone()));
}

/// `error?.error?.metadata?.raw` when truthy, as `String(raw)`.
fn raw_error_metadata(error: &Thrown) -> Option<String> {
    let object = error.downcast_ref::<ErrorObject>()?;
    let Some(SdkValue::Json(body)) = &object.error else {
        return None;
    };
    let raw = body.get("metadata")?.get("raw")?;
    convert::js_truthy(Some(raw)).then(|| js_to_string(raw))
}

/// eukhe addition: the stream-failure classification input for `error`.
/// A provider error stop (`finish_reason` such as `content_filter`)
/// classifies by its raw stop reason.
fn to_provider_error(
    error: &Thrown,
    message: &str,
    is_aborted: bool,
    stream_drop: Option<OpenStreamBlock>,
    raw_stop_reason: Option<&str>,
) -> ProviderError {
    if !is_aborted {
        if let Some(open_block) = stream_drop {
            return ProviderError::StreamFailure(StreamFailureError {
                message: message.to_owned(),
                info: stream_drop_failure(open_block).info,
            });
        }
    }
    let error_stop =
        raw_stop_reason.filter(|reason| streaming::map_stop_reason(reason).0 == StopReason::Error);
    stream_failure_of(error, is_aborted, error_stop, None)
}

/// The block a dropped stream was inside when it ended.
fn open_stream_block(output: &AssistantMessage) -> OpenStreamBlock {
    use crate::types::AssistantContentBlock;
    match output.content.last() {
        Some(AssistantContentBlock::Thinking(_)) => OpenStreamBlock::Thinking,
        Some(AssistantContentBlock::Text(_)) => OpenStreamBlock::Text,
        Some(AssistantContentBlock::ToolCall(_)) => OpenStreamBlock::ToolCall,
        None => OpenStreamBlock::None,
    }
}

// One linear request/stream body mirroring the TS `try` block.
#[allow(clippy::too_many_lines)]
async fn run_stream(
    model: &Model,
    context: &TranscriptContext,
    options: &OpenAICompletionsOptions,
    compat: &ResolvedCompat,
    api_key: String,
    grammar_tool_input_properties: &crate::types::IndexMap<String, String>,
    state: &mut StreamState<'_>,
) -> Result<(), RunError> {
    let stream_options = &options.stream;
    let request = &stream_options.request;
    let cache_retention =
        resolve_cache_retention(stream_options.cache_retention, request.env.as_ref());
    let cache_session_id = if cache_retention == CacheRetention::None {
        None
    } else {
        stream_options.session_id.as_deref()
    };
    let client = create_client(
        model,
        context,
        api_key,
        request.headers.as_ref(),
        request.fetch.clone(),
        cache_session_id,
        compat,
    );
    let mut params = JsonValue::Object(build_params(
        model,
        context,
        options,
        compat,
        cache_retention,
        grammar_tool_input_properties,
    )?);
    if let Some(on_payload) = &request.on_payload {
        if let Some(next) = on_payload(params.clone(), model).await? {
            params = next;
        }
    }
    let request_options = OpenAiRequestOptions {
        signal: request.signal.clone(),
        timeout_ms: request.timeout_ms,
    };
    let response = retry_provider_request(
        || client.post_stream("/chat/completions", &params, &request_options),
        &ProviderRetryOptions {
            max_retries: request.max_retries,
            max_retry_delay_ms: request.max_retry_delay_ms,
            signal: request.signal.clone(),
        },
    )
    .await?;
    if let Some(on_response) = &request.on_response {
        on_response(
            ProviderResponse {
                status: response.status,
                headers: headers_to_record(&response.headers),
            },
            model,
        )
        .await?;
    }
    state.push_start();

    let mut events = response.events;
    while let Some(chunk) = events.next().await {
        let chunk = chunk?;
        if let Some(on_event) = &stream_options.on_provider_stream_event {
            on_event(&chunk, model).await?;
        }
        state.handle_chunk(&chunk)?;
    }

    // eukhe addition: OpenAI prices non-default service tiers; gateways price
    // tiers per endpoint, so only the `openai` provider applies the table.
    if model.provider == "openai" {
        apply_service_tier_pricing(
            &mut state.output.usage,
            state.response_service_tier.as_deref(),
            &model.id,
        );
    }

    state.finish_blocks()?;
    if aborted(request.signal.as_ref()) || state.output.stop_reason == StopReason::Aborted {
        return Err(error_message("Request was aborted").into());
    }
    if !state.has_finish_reason && !compat.supports_finish_reason {
        state.output.stop_reason = if state
            .output
            .content
            .iter()
            .any(|block| matches!(block, crate::types::AssistantContentBlock::ToolCall(_)))
        {
            StopReason::ToolUse
        } else {
            StopReason::Stop
        };
    }
    if state.output.stop_reason == StopReason::Error {
        let message = state
            .output
            .error_message
            .clone()
            .filter(|message| !message.is_empty())
            .unwrap_or_else(|| "Provider returned an error stop reason".to_owned());
        return Err(error_message(&message).into());
    }
    if (compat.supports_finish_reason && !state.has_finish_reason)
        || state.output.stop_reason == StopReason::Pending
    {
        return Err(RunError {
            error: error_message("Stream ended without finish_reason"),
            stream_drop: Some(open_stream_block(&state.output)),
        });
    }
    Ok(())
}

/// TS `stream`: options in `extra` (`toolChoice`, `reasoningEffort`,
/// `thinkingBudgets`).
///
/// Must be called inside a tokio runtime.
#[must_use]
pub fn stream(
    model: &Model,
    context: &TranscriptContext,
    options: ProviderStreamOptions,
) -> AssistantMessageEventStream {
    match OpenAICompletionsOptions::from_provider_options(options) {
        Ok(options) => stream_with_options(model, context, options),
        Err(error) => {
            let stream = AssistantMessageEventStream::new();
            let mut output = empty_output(model);
            fail(
                model,
                &OpenAICompletionsOptions::default(),
                &mut output,
                &crate::utils::diagnostics::thrown(error).into(),
                &stream,
            );
            stream
        }
    }
}

/// TS `streamSimple`: provider-neutral options mapped onto
/// [`OpenAICompletionsOptions`].
///
/// TS throws synchronously when no API key is available; here the same
/// error ends the returned stream (the `stream` call reports it).
///
/// Must be called inside a tokio runtime.
#[must_use]
pub fn stream_simple(
    model: &Model,
    context: &TranscriptContext,
    options: SimpleStreamOptions,
) -> AssistantMessageEventStream {
    let api_key = options.stream.request.api_key.clone();
    let base = build_base_options(model, context, Some(&options), api_key.as_deref());
    let reasoning_effort = options
        .reasoning
        .map(|reasoning| clamp_thinking_level(model, reasoning.into()))
        .and_then(model_level_to_thinking_level);
    stream_with_options(
        model,
        context,
        OpenAICompletionsOptions {
            stream: base,
            tool_choice: options
                .tool_choice
                .map(|choice| JsonValue::String(choice.as_str().to_owned())),
            reasoning_effort,
            thinking_budgets: options.thinking_budgets,
        },
    )
}

/// `clampedReasoning === "off" ? undefined : clampedReasoning`.
const fn model_level_to_thinking_level(level: ModelThinkingLevel) -> Option<ThinkingLevel> {
    match level {
        ModelThinkingLevel::Off => None,
        ModelThinkingLevel::Minimal => Some(ThinkingLevel::Minimal),
        ModelThinkingLevel::Low => Some(ThinkingLevel::Low),
        ModelThinkingLevel::Medium => Some(ThinkingLevel::Medium),
        ModelThinkingLevel::High => Some(ThinkingLevel::High),
        ModelThinkingLevel::Xhigh => Some(ThinkingLevel::Xhigh),
        ModelThinkingLevel::Max => Some(ThinkingLevel::Max),
    }
}

/// The `openai-completions` module: TS `{ stream, streamSimple }`.
#[must_use]
pub fn streams() -> ProviderStreams {
    ProviderStreams {
        stream: Arc::new(stream),
        stream_simple: Arc::new(stream_simple),
        fetch_deferred: None,
        cancel_deferred: None,
    }
}
