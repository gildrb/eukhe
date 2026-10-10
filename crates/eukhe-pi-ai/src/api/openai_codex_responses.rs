//! The `openai-codex-responses` wire API (the `ChatGPT` Codex backend). Port of
//! `api/openai-codex-responses.ts`.
//!
//! Transports: WebSocket first (`transport` `auto`, `websocket`,
//! `websocket-cached`) with a session-scoped connection cache and
//! `previous_response_id` continuations, falling back to SSE before any
//! event was emitted; SSE directly for `transport: "sse"`.
//!
//! API-specific options arrive in [`ProviderStreamOptions::extra`] under
//! the TS `OpenAICodexResponsesOptions` names: `reasoningEffort`,
//! `reasoningSummary`, `serviceTier`, `textVerbosity`, `toolChoice`.
//!
//! eukhe additions kept on top of v1.0.4:
//! - `StreamOptions::service_tier` (eukhe addition) is the request service
//!   tier when `extra.serviceTier` is absent;
//! - terminal errors also record the `provider_stream_failure` diagnostic
//!   (eukhe addition, `utils::stream_failure`);
//! - the session-keyed WebSocket connection cache of the old eukhe port is
//!   the v1.0.4 `websocketSessionCache` (see `session_cache`).

mod errors;
mod events;
mod request;
mod session_cache;
mod sse;
mod tungstenite_socket;
mod websocket;

#[cfg(test)]
mod tests;

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use eukhe_chord::context::AbortSignal;
use eukhe_types::pi_ai::IndexMap;
use eukhe_types::pi_ai::{
    AssistantMessage, AssistantMessageEvent, DoneReason, ErrorReason, JsonObject, JsonValue, Model,
    ModelThinkingLevel, OpenAIResponsesCompat, StopReason, TranscriptContext, Transport, Usage,
    UsageCost,
};

use crate::api::constrained_sampling::create_grammar_tool_input_properties;
use crate::api::lazy::lazy_stream;
use crate::api::openai_prompt_cache::clamp_openai_prompt_cache_key;
use crate::api::openai_responses_shared::OpenAIResponsesStreamOptions;
use crate::api::simple_options::build_base_options;
use crate::api::ProviderStreams;
use crate::models::clamp_thinking_level;
use crate::types::{ProviderStreamOptions, SimpleStreamOptions, StreamOptions};
use crate::utils::diagnostics::{
    append_assistant_message_diagnostic, create_assistant_message_diagnostic, thrown, ErrorObject,
    Thrown,
};
use crate::utils::error_body::{format_provider_error, normalize_provider_error};
use crate::utils::event_stream::AssistantMessageEventStream;
use crate::utils::stream_failure::record_stream_failure;
use crate::utils::transcript::{get_declared_tools, resolve_transcript};
use crate::utils::uuid::uuidv7;

pub use session_cache::{
    close_openai_codex_websocket_sessions, get_openai_codex_websocket_debug_stats,
    reset_openai_codex_websocket_debug_stats, OpenAICodexWebSocketDebugStats,
};

use errors::{
    aborted_error, is_codex_non_transport_error, is_previous_response_not_found_error,
    is_websocket_connection_limit_reached_error, to_provider_error,
};
use events::StartEmitter;
use request::{
    apply_service_tier_pricing, build_request_body, build_sse_headers, build_websocket_headers,
    extract_account_id, resolve_codex_service_tier, resolve_codex_websocket_url,
};
use session_cache::{
    is_websocket_sse_fallback_active, process_websocket_stream, record_websocket_failure,
    record_websocket_sse_fallback, register_session_cleanup, WebSocketRequest,
};
use sse::{process_sse, SseRequest};

/// The API id.
const API: &str = "openai-codex-responses";
const DEFAULT_MAX_RETRY_DELAY_MS: f64 = 60_000.0;
/// Providers whose tool-call ids Codex accepts as-is.
const CODEX_TOOL_CALL_PROVIDERS: &[&str] = &["openai", "openai-codex", "opencode"];

/// `Date.now()` as a JS number (with the test clock offset, TS
/// `vi.setSystemTime`).
fn clock_ms() -> f64 {
    // Millisecond timestamps are far below 2^53.
    #[allow(clippy::cast_precision_loss)]
    let now = crate::utils::now_ms() as f64;
    now + test_clock::offset_ms()
}

#[cfg(test)]
mod test_clock {
    use std::sync::atomic::{AtomicU64, Ordering};

    static OFFSET_MS: AtomicU64 = AtomicU64::new(0);

    /// Move `Date.now()` forward by `ms` (TS `vi.setSystemTime`).
    pub(crate) fn set_offset_ms(ms: f64) {
        OFFSET_MS.store(ms.to_bits(), Ordering::SeqCst);
    }

    pub(super) fn offset_ms() -> f64 {
        f64::from_bits(OFFSET_MS.load(Ordering::SeqCst))
    }
}

#[cfg(not(test))]
mod test_clock {
    pub(super) const fn offset_ms() -> f64 {
        0.0
    }
}

/// TS `OpenAICodexResponsesOptions`: the shared options plus the Codex keys
/// read from [`ProviderStreamOptions::extra`]. A missing key is TS
/// `undefined`; values are kept as JSON like the TS passes them through.
#[derive(Debug, Clone, Default)]
pub(crate) struct CodexOptions {
    pub stream: StreamOptions,
    pub reasoning_effort: Option<JsonValue>,
    pub reasoning_summary: Option<JsonValue>,
    pub service_tier: Option<JsonValue>,
    pub text_verbosity: Option<JsonValue>,
    pub tool_choice: Option<JsonValue>,
    pub temperature: Option<f64>,
}

impl CodexOptions {
    fn from_provider_options(options: ProviderStreamOptions) -> Self {
        let ProviderStreamOptions { stream, extra } = options;
        let take = |name: &str| extra.get(name).cloned();
        let service_tier = take("serviceTier").or_else(|| {
            // eukhe addition: the shared `service_tier` option.
            stream
                .service_tier
                .map(|tier| JsonValue::String(tier.as_str().to_owned()))
        });
        Self {
            temperature: stream.temperature,
            reasoning_effort: take("reasoningEffort"),
            reasoning_summary: take("reasoningSummary"),
            service_tier,
            text_verbosity: take("textVerbosity"),
            tool_choice: take("toolChoice"),
            stream,
        }
    }

    /// The request service tier as the Responses processor reads it.
    fn service_tier_text(&self) -> Option<String> {
        self.service_tier
            .as_ref()
            .and_then(JsonValue::as_str)
            .map(str::to_owned)
    }

    fn aborted(&self) -> bool {
        self.stream
            .request
            .signal
            .as_ref()
            .is_some_and(AbortSignal::aborted)
    }
}

/// The model's Responses compat block.
fn responses_compat(model: &Model) -> Option<&OpenAIResponsesCompat> {
    model
        .compat
        .as_ref()
        .and_then(|compat| compat.as_openai_responses())
}

/// The processor options both transports pass (TS `{ serviceTier,
/// grammarToolInputProperties, resolveServiceTier, applyServiceTierPricing }`).
fn responses_stream_options(
    model: &Model,
    options: &CodexOptions,
    grammar_tool_input_properties: &IndexMap<String, String>,
) -> OpenAIResponsesStreamOptions {
    let model_id = model.id.clone();
    OpenAIResponsesStreamOptions {
        service_tier: options.service_tier_text(),
        grammar_tool_input_properties: Some(grammar_tool_input_properties.clone()),
        resolve_service_tier: Some(Arc::new(resolve_codex_service_tier)),
        apply_service_tier_pricing: Some(Arc::new(
            move |usage: &mut Usage, service_tier: Option<&str>| {
                apply_service_tier_pricing(usage, service_tier, &model_id);
            },
        )),
        ..OpenAIResponsesStreamOptions::default()
    }
}

/// TS `assertSuccessfulOutput`: the `done` reason of a successful output.
fn assert_successful_output(output: &AssistantMessage) -> Result<DoneReason, Thrown> {
    match output.stop_reason {
        StopReason::Pending => {
            Err(ErrorObject::new("Codex stream ended without a stop reason").thrown())
        }
        StopReason::Error | StopReason::Aborted => Err(ErrorObject::new(
            output
                .error_message
                .clone()
                .filter(|message| !message.is_empty())
                .unwrap_or_else(|| "An unknown error occurred".to_owned()),
        )
        .thrown()),
        StopReason::Stop => Ok(DoneReason::Stop),
        StopReason::Length => Ok(DoneReason::Length),
        StopReason::ToolUse => Ok(DoneReason::ToolUse),
        StopReason::Deferred => Ok(DoneReason::Deferred),
    }
}

/// TS `normalizeTimeoutMs`.
fn normalize_timeout_ms(value: Option<f64>) -> Result<Option<f64>, Thrown> {
    let Some(value) = value else {
        return Ok(None);
    };
    if !value.is_finite() || value < 0.0 {
        return Err(ErrorObject::new(format!(
            "Invalid timeoutMs: {}",
            crate::utils::js::number_to_js_string(value)
        ))
        .thrown());
    }
    Ok(Some(value.floor()))
}

/// The module's capability value.
#[must_use]
pub fn streams() -> ProviderStreams {
    register_session_cleanup();
    ProviderStreams {
        stream: Arc::new(stream),
        stream_simple: Arc::new(stream_simple),
        fetch_deferred: None,
        cancel_deferred: None,
    }
}

/// TS `stream`.
#[must_use]
pub fn stream(
    model: &Model,
    context: &TranscriptContext,
    options: ProviderStreamOptions,
) -> AssistantMessageEventStream {
    let event_stream = AssistantMessageEventStream::new();
    let compat = responses_compat(model);
    let normalized_context = resolve_transcript(
        context.clone(),
        compat.and_then(|compat| compat.supports_mid_convo_system_messages),
    );
    let options = CodexOptions::from_provider_options(options);
    let model = model.clone();
    let task_stream = event_stream.clone();
    tokio::spawn(async move {
        let mut output = AssistantMessage {
            content: Vec::new(),
            api: API.to_owned(),
            provider: model.provider.clone(),
            model: model.id.clone(),
            response_model: None,
            response_id: None,
            provider_thinking_level: None,
            thinking_level: None,
            diagnostics: None,
            usage: Usage {
                input: 0,
                output: 0,
                cache_read: 0,
                cache_write: 0,
                cache_write_1h: None,
                reasoning: None,
                total_tokens: 0,
                cost: UsageCost::default(),
            },
            stop_reason: StopReason::Pending,
            deferred: None,
            error_message: None,
            raw_stop_reason: None,
            end_turn: None,
            timestamp: crate::utils::now_ms(),
            duration_ms: None,
        };

        match run(
            &model,
            &normalized_context,
            &options,
            &mut output,
            &task_stream,
        )
        .await
        {
            Ok(reason) => {
                task_stream.push(AssistantMessageEvent::Done {
                    reason,
                    message: output,
                });
                task_stream.end(None);
            }
            Err(error) => {
                let aborted = options.aborted();
                output.stop_reason = if aborted {
                    StopReason::Aborted
                } else {
                    StopReason::Error
                };
                output.error_message = Some(format_provider_error(
                    &normalize_provider_error(&error),
                    None,
                ));
                // eukhe addition: the `provider_stream_failure` diagnostic.
                record_stream_failure(
                    (&model.provider, &model.id, &model.api),
                    &mut output,
                    &to_provider_error(&error, aborted),
                );
                task_stream.push(AssistantMessageEvent::Error {
                    reason: if aborted {
                        ErrorReason::Aborted
                    } else {
                        ErrorReason::Error
                    },
                    error: output,
                });
                task_stream.end(None);
            }
        }
    });
    event_stream
}

/// The `try` block of TS `stream`: returns the `done` reason.
#[allow(clippy::too_many_lines)] // One TS function body; split only where TS splits.
async fn run(
    model: &Model,
    context: &TranscriptContext,
    options: &CodexOptions,
    output: &mut AssistantMessage,
    stream: &AssistantMessageEventStream,
) -> Result<DoneReason, Thrown> {
    let request_options = &options.stream.request;
    let api_key = request_options
        .api_key
        .clone()
        .filter(|key| !key.is_empty())
        .ok_or_else(|| {
            ErrorObject::new(format!("No API key for provider: {}", model.provider)).thrown()
        })?;

    let account_id = extract_account_id(&api_key)?;
    let compat = responses_compat(model);
    let declared_tools = get_declared_tools(context.messages());
    let grammar_tool_input_properties = create_grammar_tool_input_properties(
        Some(&declared_tools),
        compat
            .and_then(|compat| compat.supports_openai_grammar_tools)
            .unwrap_or(false),
    )?;
    let cache_session_id = match options.stream.cache_retention {
        Some(eukhe_types::pi_ai::CacheRetention::None) => None,
        _ => options.stream.session_id.clone(),
    };
    let codex_session_id = clamp_openai_prompt_cache_key(cache_session_id.as_deref());
    let mut body = build_request_body(
        model,
        context,
        options,
        codex_session_id.as_deref(),
        &grammar_tool_input_properties,
    )?;
    if let Some(on_payload) = &request_options.on_payload {
        if let Some(next_body) = on_payload(body.clone(), model).await? {
            body = next_body;
        }
    }
    let websocket_request_id = match codex_session_id.as_deref() {
        Some(id) if !id.is_empty() => id.to_owned(),
        _ => uuidv7(None).map_err(thrown)?,
    };
    let sse_headers = build_sse_headers(
        model.headers.as_ref(),
        request_options.headers.as_ref(),
        &account_id,
        &api_key,
        codex_session_id.as_deref(),
    )?;
    let websocket_headers = build_websocket_headers(
        model.headers.as_ref(),
        request_options.headers.as_ref(),
        &account_id,
        &api_key,
        &websocket_request_id,
    )?;
    let body_json = crate::utils::js::json_stringify(&body);
    let http_timeout_ms = normalize_timeout_ms(request_options.timeout_ms)?;
    let websocket_connect_timeout_ms =
        normalize_timeout_ms(options.stream.websocket_connect_timeout_ms)?;
    let transport = options.stream.transport.unwrap_or(Transport::Auto);
    let start = StartEmitter::new(stream.clone());
    let cache_session_id = cache_session_id.as_deref();
    let websocket_disabled_for_session =
        transport != Transport::Sse && is_websocket_sse_fallback_active(cache_session_id);
    if websocket_disabled_for_session {
        record_websocket_sse_fallback(cache_session_id);
    }

    if transport != Transport::Sse && !websocket_disabled_for_session {
        let url = resolve_codex_websocket_url(Some(&model.base_url))?;
        let mut retried_websocket_connection_limit = false;
        let mut retried_missing_websocket_continuation = false;
        loop {
            let websocket_started = Arc::new(AtomicBool::new(false));
            let started = Arc::clone(&websocket_started);
            let result = process_websocket_stream(
                &WebSocketRequest {
                    url: &url,
                    body: &body,
                    headers: &websocket_headers,
                    model,
                    idle_timeout_ms: http_timeout_ms,
                    connect_timeout_ms: websocket_connect_timeout_ms,
                    cache_session_id,
                    account_id: &account_id,
                    grammar_tool_input_properties: &grammar_tool_input_properties,
                    options,
                },
                output,
                stream,
                &start,
                move || started.store(true, Ordering::SeqCst),
            )
            .await
            .and_then(|()| {
                if options.aborted() {
                    return Err(aborted_error());
                }
                assert_successful_output(output)
            });
            let error = match result {
                Ok(reason) => return Ok(reason),
                Err(error) => error,
            };
            let websocket_started = websocket_started.load(Ordering::SeqCst);
            let aborted = options.aborted();
            let connection_limit_before_start =
                !websocket_started && is_websocket_connection_limit_reached_error(&error);
            let previous_response_not_found = is_previous_response_not_found_error(&error);
            if !aborted && previous_response_not_found && !retried_missing_websocket_continuation {
                retried_missing_websocket_continuation = true;
                continue;
            }
            if !aborted && connection_limit_before_start && !retried_websocket_connection_limit {
                retried_websocket_connection_limit = true;
                continue;
            }
            if aborted || (is_codex_non_transport_error(&error) && !connection_limit_before_start) {
                return Err(error);
            }
            let mut details = JsonObject::new();
            details.insert(
                "configuredTransport".into(),
                JsonValue::String(transport.as_str().to_owned()),
            );
            if !websocket_started {
                details.insert(
                    "fallbackTransport".into(),
                    JsonValue::String("sse".to_owned()),
                );
            }
            details.insert("eventsEmitted".into(), JsonValue::Bool(websocket_started));
            details.insert(
                "phase".into(),
                JsonValue::String(
                    if websocket_started {
                        "after_message_stream_start"
                    } else {
                        "before_message_stream_start"
                    }
                    .to_owned(),
                ),
            );
            details.insert("requestBytes".into(), JsonValue::from(body_json.len()));
            append_assistant_message_diagnostic(
                output,
                create_assistant_message_diagnostic(
                    "provider_transport_failure",
                    &error,
                    Some(details),
                ),
            );
            record_websocket_failure(cache_session_id, &error);
            if websocket_started {
                return Err(error);
            }
            record_websocket_sse_fallback(cache_session_id);
            break;
        }
    }

    process_sse(
        SseRequest {
            model,
            headers: sse_headers,
            body_json: &body_json,
            http_timeout_ms,
            grammar_tool_input_properties: &grammar_tool_input_properties,
            options,
        },
        output,
        stream,
        &start,
    )
    .await?;

    if options.aborted() {
        return Err(aborted_error());
    }

    assert_successful_output(output)
}

/// TS `streamSimple`.
#[must_use]
#[allow(clippy::needless_pass_by_value)] // The `StreamSimpleFn` signature takes the options by value.
pub fn stream_simple(
    model: &Model,
    context: &TranscriptContext,
    options: SimpleStreamOptions,
) -> AssistantMessageEventStream {
    let api_key = options
        .stream
        .request
        .api_key
        .clone()
        .filter(|key| !key.is_empty());
    let Some(api_key) = api_key else {
        // TS throws synchronously; through the lazy API wrapper that becomes
        // the setup error event.
        let error =
            ErrorObject::new(format!("No API key for provider: {}", model.provider)).thrown();
        return lazy_stream(model, async move { Err(error) });
    };

    let base = build_base_options(model, context, Some(&options), Some(&api_key));
    let mut extra = JsonObject::new();
    if let Some(tool_choice) = options.tool_choice {
        extra.insert(
            "toolChoice".into(),
            JsonValue::String(tool_choice.as_str().to_owned()),
        );
    }
    let clamped_reasoning = options
        .reasoning
        .map(|reasoning| clamp_thinking_level(model, ModelThinkingLevel::from(reasoning)));
    if let Some(reasoning_effort) =
        clamped_reasoning.filter(|level| *level != ModelThinkingLevel::Off)
    {
        extra.insert(
            "reasoningEffort".into(),
            JsonValue::String(reasoning_effort.as_str().to_owned()),
        );
    }

    stream(
        model,
        context,
        ProviderStreamOptions {
            stream: base,
            extra,
        },
    )
}
