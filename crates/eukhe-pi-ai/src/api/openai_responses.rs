//! The `openai-responses` wire API. Port of `api/openai-responses.ts`.
//!
//! API-specific options (TS `OpenAIResponsesOptions`) are read from
//! [`ProviderStreamOptions::extra`]: `reasoningEffort`, `reasoningSummary`,
//! `serviceTier`, `toolChoice`.

use std::sync::Arc;

use serde_json::json;

use super::constrained_sampling::create_grammar_tool_input_properties;
use super::github_copilot_headers::{build_copilot_dynamic_headers, has_copilot_vision_input};
use super::openai_prompt_cache::clamp_openai_prompt_cache_key;
use super::openai_responses_shared::{
    apply_reasoning_context, convert_responses_messages, convert_responses_tools,
    process_responses_stream, ConvertResponsesMessagesOptions, ConvertResponsesToolsOptions,
    GrammarToolInputProperties, OpenAIResponsesStreamOptions,
};
use super::openai_sdk::{
    stream_failure_of, OpenAiClient, OpenAiClientConfig, OpenAiClientKind, OpenAiRequestOptions,
};
use super::simple_options::{build_base_options, resolve_sampling_params};
use super::ProviderStreams;
use crate::api::lazy::lazy_stream;
use crate::models::clamp_thinking_level;
use crate::types::{
    AssistantMessage, AssistantMessageEvent, CacheRetention, ErrorReason, JsonObject, JsonValue,
    Model, ModelThinkingLevel, ProviderEnv, ProviderHeaders, ProviderResponse,
    ProviderStreamOptions, SimpleStreamOptions, StopReason, ThinkingLevel, TranscriptContext,
    Usage,
};
use crate::utils::diagnostics::{ErrorObject, Thrown};
use crate::utils::error_body::{format_provider_error, normalize_provider_error};
use crate::utils::event_stream::AssistantMessageEventStream;
use crate::utils::headers::headers_to_record;
use crate::utils::now_ms;
use crate::utils::pi_user_agent::get_pi_user_agent;
use crate::utils::provider_env::get_provider_env_value;
use crate::utils::provider_retry::{retry_provider_request, ProviderRetryOptions};
use crate::utils::stream_failure::record_stream_failure;
use crate::utils::transcript::{get_declared_tools, resolve_transcript, resolve_transcript_tools};

const OPENAI_TOOL_CALL_PROVIDERS: &[&str] = &["openai", "openai-codex", "opencode"];
/// `OpenAI` Responses rejects `max_output_tokens` below 16.
pub(crate) const OPENAI_RESPONSES_MIN_OUTPUT_TOKENS: u64 = 16;
const CHATGPT_USAGE_URL: &str = "https://chatgpt.com/settings/usage";

/// `OpenAI` API keys start with `sk-`; a different credential sent directly
/// to `OpenAI` is a Sign in with `ChatGPT` access token.
fn is_chatgpt_sign_in(model: &Model, api_key: Option<&str>) -> bool {
    model.provider == "openai"
        && model.base_url == "https://api.openai.com/v1"
        && api_key.is_some_and(|key| !key.starts_with("sk-"))
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
pub(crate) fn get_client_api_key(
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

/// Session-affinity header format (TS `sessionAffinityFormat`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AffinityFormat {
    OpenAI,
    OpenAINoSession,
    OpenRouter,
}

fn detect_session_affinity_format(model: &Model) -> AffinityFormat {
    if model.provider == "openrouter" || model.base_url.contains("openrouter.ai") {
        AffinityFormat::OpenRouter
    } else {
        AffinityFormat::OpenAI
    }
}

/// Resolve cache retention preference. Defaults to "short" and uses
/// `PI_CACHE_RETENTION` for backward compatibility.
fn resolve_cache_retention(
    cache_retention: Option<CacheRetention>,
    env: Option<&ProviderEnv>,
) -> CacheRetention {
    if let Some(cache_retention) = cache_retention {
        return cache_retention;
    }
    if get_provider_env_value("PI_CACHE_RETENTION", env).as_deref() == Some("long") {
        return CacheRetention::Long;
    }
    CacheRetention::Short
}

/// TS `Required<OpenAIResponsesCompat>`.
#[derive(Debug, Clone, Copy)]
#[allow(clippy::struct_excessive_bools)] // Mirrors the TS compat record.
struct ResolvedCompat {
    supports_mid_convo_system_messages: bool,
    session_affinity_format: AffinityFormat,
    supports_long_cache_retention: bool,
    supports_strict_mode: bool,
    supports_openai_grammar_tools: bool,
    supports_additional_tools: bool,
    supports_tool_search: bool,
    supports_explicit_prompt_cache_mode: bool,
    supports_max_output_tokens: bool,
}

fn get_compat(model: &Model) -> ResolvedCompat {
    let compat = model
        .compat
        .as_ref()
        .and_then(crate::types::ModelCompat::as_openai_responses);
    let flag = |read: fn(&crate::types::OpenAIResponsesCompat) -> Option<bool>, default: bool| {
        compat.and_then(read).unwrap_or(default)
    };
    ResolvedCompat {
        supports_mid_convo_system_messages: flag(
            |compat| compat.supports_mid_convo_system_messages,
            false,
        ),
        session_affinity_format: compat
            .and_then(|compat| compat.session_affinity_format)
            .map_or_else(
                || detect_session_affinity_format(model),
                |format| match format {
                    crate::types::SessionAffinityFormat::OpenRouter => AffinityFormat::OpenRouter,
                    crate::types::SessionAffinityFormat::OpenAI => AffinityFormat::OpenAI,
                    crate::types::SessionAffinityFormat::OpenAINoSession => {
                        AffinityFormat::OpenAINoSession
                    }
                },
            ),
        supports_long_cache_retention: flag(|compat| compat.supports_long_cache_retention, true),
        supports_strict_mode: flag(|compat| compat.supports_strict_mode, false),
        supports_openai_grammar_tools: flag(|compat| compat.supports_openai_grammar_tools, false),
        supports_additional_tools: flag(|compat| compat.supports_additional_tools, false),
        supports_tool_search: flag(|compat| compat.supports_tool_search, false),
        supports_explicit_prompt_cache_mode: flag(
            |compat| compat.supports_explicit_prompt_cache_mode,
            false,
        ),
        supports_max_output_tokens: flag(|compat| compat.supports_max_output_tokens, true),
    }
}

fn get_prompt_cache_retention(
    compat: &ResolvedCompat,
    cache_retention: CacheRetention,
) -> Option<&'static str> {
    (cache_retention == CacheRetention::Long
        && compat.supports_long_cache_retention
        && !compat.supports_explicit_prompt_cache_mode)
        .then_some("24h")
}

fn get_prompt_cache_options(
    compat: &ResolvedCompat,
    cache_retention: CacheRetention,
) -> Option<JsonValue> {
    if !compat.supports_explicit_prompt_cache_mode {
        return None;
    }
    match cache_retention {
        CacheRetention::None => Some(json!({ "mode": "explicit" })),
        CacheRetention::Long if compat.supports_long_cache_retention => {
            Some(json!({ "ttl": "30m" }))
        }
        CacheRetention::Long | CacheRetention::Short => None,
    }
}

/// TS `OpenAIResponsesOptions` (the API-specific keys of the stream options).
#[derive(Debug, Clone, Default, PartialEq)]
pub struct OpenAIResponsesOptions {
    /// `reasoningEffort`.
    pub reasoning_effort: Option<ThinkingLevel>,
    /// `reasoningSummary` (`"auto" | "detailed" | "concise" | null`).
    pub reasoning_summary: Option<String>,
    /// `serviceTier`: the raw `service_tier` value (`null` is sent as is).
    pub service_tier: Option<JsonValue>,
    /// `toolChoice`: the raw `tool_choice` value.
    pub tool_choice: Option<JsonValue>,
}

impl OpenAIResponsesOptions {
    /// Reads the camelCase keys from API-specific stream options. A
    /// `reasoningEffort` that is not a thinking level is ignored.
    #[must_use]
    pub fn from_extra(extra: &JsonObject) -> Self {
        Self {
            reasoning_effort: extra
                .get("reasoningEffort")
                .and_then(|value| serde_json::from_value(value.clone()).ok()),
            reasoning_summary: extra
                .get("reasoningSummary")
                .and_then(JsonValue::as_str)
                .map(str::to_owned),
            service_tier: extra.get("serviceTier").cloned(),
            tool_choice: extra.get("toolChoice").cloned(),
        }
    }
}

/// Multipliers per <https://developers.openai.com/api/docs/pricing>.
fn get_service_tier_cost_multiplier(model_id: &str, service_tier: Option<&str>) -> f64 {
    match service_tier {
        Some("flex") => 0.5,
        Some("priority" | "fast") => {
            if model_id == "gpt-5.5" {
                2.5
            } else {
                2.0
            }
        }
        _ => 1.0,
    }
}

/// TS `applyServiceTierPricing`.
pub fn apply_service_tier_pricing(usage: &mut Usage, service_tier: Option<&str>, model_id: &str) {
    let multiplier = get_service_tier_cost_multiplier(model_id, service_tier);
    // The multiplier table is discrete; 1 is the no-op sentinel.
    #[allow(clippy::float_cmp)]
    if multiplier == 1.0 {
        return;
    }
    usage.cost.input *= multiplier;
    usage.cost.output *= multiplier;
    usage.cost.cache_read *= multiplier;
    usage.cost.cache_write *= multiplier;
    usage.cost.total =
        usage.cost.input + usage.cost.output + usage.cost.cache_read + usage.cost.cache_write;
}

/// The effective `serviceTier`: the API option, else the eukhe addition
/// [`StreamOptions::service_tier`](crate::types::StreamOptions) (never sent
/// to GitHub Copilot, which rejects the field itself with a 400).
fn effective_service_tier(
    model: &Model,
    options: &ProviderStreamOptions,
    api: &OpenAIResponsesOptions,
) -> Option<JsonValue> {
    api.service_tier.clone().or_else(|| {
        options
            .stream
            .service_tier
            .filter(|_| model.provider != "github-copilot")
            .map(|tier| json!(tier.as_str()))
    })
}

fn create_client(
    model: &Model,
    context: &TranscriptContext,
    api_key: String,
    options: &ProviderStreamOptions,
    session_id: Option<&str>,
) -> OpenAiClient {
    let compat = get_compat(model);
    let mut headers: ProviderHeaders = ProviderHeaders::new();
    headers.insert(
        "User-Agent".to_owned(),
        Some(get_pi_user_agent().to_owned()),
    );
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
        match compat.session_affinity_format {
            AffinityFormat::OpenRouter => {
                headers.insert("x-session-id".to_owned(), Some(session_id.to_owned()));
            }
            AffinityFormat::OpenAI => {
                headers.insert("session_id".to_owned(), Some(session_id.to_owned()));
                headers.insert(
                    "x-client-request-id".to_owned(),
                    Some(session_id.to_owned()),
                );
            }
            AffinityFormat::OpenAINoSession => {
                headers.insert(
                    "x-client-request-id".to_owned(),
                    Some(session_id.to_owned()),
                );
            }
        }
    }
    // Merge options headers last so they can override defaults.
    for (name, value) in options.stream.request.headers.iter().flatten() {
        headers.insert(name.clone(), value.clone());
    }
    OpenAiClient::new(OpenAiClientConfig {
        kind: OpenAiClientKind::OpenAI,
        api_key,
        base_url: model.base_url.clone(),
        default_headers: headers,
        default_query: Vec::new(),
        fetch: options.stream.request.fetch.clone(),
    })
}

#[allow(clippy::too_many_lines)] // One TS function.
fn build_params(
    model: &Model,
    context: &TranscriptContext,
    options: &ProviderStreamOptions,
    api: &OpenAIResponsesOptions,
    compat: &ResolvedCompat,
    grammar: &GrammarToolInputProperties,
) -> Result<JsonValue, Thrown> {
    let transcript_tools = resolve_transcript_tools(
        context.messages(),
        compat.supports_additional_tools || compat.supports_tool_search,
    );
    let tool_options = ConvertResponsesToolsOptions {
        strict: None,
        supports_strict_mode: Some(compat.supports_strict_mode),
        supports_openai_grammar_tools: Some(compat.supports_openai_grammar_tools),
        tool_search_result: None,
    };
    let messages = convert_responses_messages(
        model,
        context,
        OPENAI_TOOL_CALL_PROVIDERS,
        &ConvertResponsesMessagesOptions {
            include_system_prompt: None,
            grammar_tool_input_properties: Some(grammar.clone()),
            supports_mid_convo_system_messages: Some(compat.supports_mid_convo_system_messages),
            supports_additional_tools: Some(compat.supports_additional_tools),
            supports_tool_search: Some(compat.supports_tool_search),
            tool_options: Some(tool_options),
            explicit_cache_breakpoints: true,
        },
    )?;

    let stream_options = &options.stream;
    let cache_retention = resolve_cache_retention(
        stream_options.cache_retention,
        stream_options.request.env.as_ref(),
    );
    // Sign in with ChatGPT rejects these request fields.
    let omit_unsupported_fields =
        is_chatgpt_sign_in(model, stream_options.request.api_key.as_deref());
    let mut params = JsonObject::new();
    params.insert("model".to_owned(), json!(model.id));
    params.insert("input".to_owned(), JsonValue::Array(messages));
    params.insert("stream".to_owned(), json!(true));
    if cache_retention != CacheRetention::None {
        if let Some(key) = clamp_openai_prompt_cache_key(stream_options.session_id.as_deref()) {
            params.insert("prompt_cache_key".to_owned(), json!(key));
        }
    }
    if !omit_unsupported_fields {
        if let Some(retention) = get_prompt_cache_retention(compat, cache_retention) {
            params.insert("prompt_cache_retention".to_owned(), json!(retention));
        }
        if let Some(cache_options) = get_prompt_cache_options(compat, cache_retention) {
            params.insert("prompt_cache_options".to_owned(), cache_options);
        }
    }
    params.insert("store".to_owned(), json!(false));

    if let Some(max_tokens) = stream_options.max_tokens.filter(|tokens| *tokens != 0) {
        if compat.supports_max_output_tokens && !omit_unsupported_fields {
            params.insert(
                "max_output_tokens".to_owned(),
                json!(max_tokens.max(OPENAI_RESPONSES_MIN_OUTPUT_TOKENS)),
            );
        }
    }
    if let Some(temperature) = stream_options.temperature {
        if !omit_unsupported_fields {
            params.insert("temperature".to_owned(), json!(temperature));
        }
    }
    if let Some(service_tier) = effective_service_tier(model, options, api) {
        params.insert("service_tier".to_owned(), service_tier);
    }
    if !transcript_tools.request_tools.is_empty() {
        params.insert(
            "tools".to_owned(),
            JsonValue::Array(convert_responses_tools(
                &transcript_tools.request_tools,
                &ConvertResponsesToolsOptions {
                    strict: None,
                    supports_strict_mode: Some(compat.supports_strict_mode),
                    supports_openai_grammar_tools: Some(compat.supports_openai_grammar_tools),
                    tool_search_result: None,
                },
            )?),
        );
    }
    if let Some(tool_choice) = &api.tool_choice {
        params.insert("tool_choice".to_owned(), tool_choice.clone());
    }

    let reasoning_effort = reasoning_effort_of(api);
    if model.reasoning {
        if let Some(effort) = reasoning_effort {
            insert_reasoning(model, api, effort, &mut params);
        } else if model.provider != "github-copilot" {
            insert_reasoning_off(model, &mut params);
        }
        if model.provider == "xai" {
            params.insert("include".to_owned(), json!(["reasoning.encrypted_content"]));
        }
    }

    // Last so model and request sampling parameters override named request fields.
    let sampling_level = reasoning_effort.map_or(ModelThinkingLevel::Off, ModelThinkingLevel::from);
    if let Some(sampling_params) = resolve_sampling_params(
        model,
        sampling_level,
        stream_options.sampling_params.as_ref(),
    ) {
        params.extend(sampling_params);
    }
    // eukhe addition: keep earlier turns' reasoning in the cached prefix.
    apply_reasoning_context(model, &mut params);

    Ok(JsonValue::Object(params))
}

/// `options.reasoningEffort ?? (options.reasoningSummary ? "medium" : undefined)`.
pub(crate) fn reasoning_effort_of(api: &OpenAIResponsesOptions) -> Option<ThinkingLevel> {
    api.reasoning_effort.or_else(|| {
        api.reasoning_summary
            .as_deref()
            .filter(|summary| !summary.is_empty())
            .map(|_| ThinkingLevel::Medium)
    })
}

/// The `reasoning` (and `include`) of a request with a reasoning effort.
pub(crate) fn insert_reasoning(
    model: &Model,
    api: &OpenAIResponsesOptions,
    effort: ThinkingLevel,
    params: &mut JsonObject,
) {
    let effort = match api.reasoning_effort {
        Some(requested) => model
            .thinking_level_map
            .as_ref()
            .and_then(|map| map.get(&ModelThinkingLevel::from(requested)))
            .and_then(Clone::clone)
            .unwrap_or_else(|| requested.as_str().to_owned()),
        None => effort.as_str().to_owned(),
    };
    let summary = api
        .reasoning_summary
        .as_deref()
        .filter(|summary| !summary.is_empty())
        .unwrap_or("auto");
    params.insert(
        "reasoning".to_owned(),
        json!({ "effort": effort, "summary": summary }),
    );
    params.insert("include".to_owned(), json!(["reasoning.encrypted_content"]));
}

/// The `reasoning` of a request without a reasoning effort: the model's
/// `off` level (default `"none"`), unless the map marks `off` unsupported.
pub(crate) fn insert_reasoning_off(model: &Model, params: &mut JsonObject) {
    let off = model
        .thinking_level_map
        .as_ref()
        .and_then(|map| map.get(&ModelThinkingLevel::Off));
    match off {
        Some(None) => {}
        Some(Some(value)) => {
            params.insert("reasoning".to_owned(), json!({ "effort": value }));
        }
        None => {
            params.insert("reasoning".to_owned(), json!({ "effort": "none" }));
        }
    }
}

fn new_output(model: &Model) -> AssistantMessage {
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

/// The done reason of a successful stream.
pub(crate) fn done_reason(stop_reason: StopReason) -> Option<crate::types::DoneReason> {
    use crate::types::DoneReason;
    match stop_reason {
        StopReason::Stop => Some(DoneReason::Stop),
        StopReason::Length => Some(DoneReason::Length),
        StopReason::ToolUse => Some(DoneReason::ToolUse),
        StopReason::Deferred => Some(DoneReason::Deferred),
        StopReason::Pending | StopReason::Error | StopReason::Aborted => None,
    }
}

/// The checks after the stream processor, shared with the Azure API.
pub(crate) fn finish_checks(
    output: &AssistantMessage,
    aborted: bool,
    pending_message: &str,
) -> Result<crate::types::DoneReason, Thrown> {
    if aborted {
        return Err(ErrorObject::new("Request was aborted").thrown());
    }
    if output.stop_reason == StopReason::Pending {
        return Err(ErrorObject::new(pending_message).thrown());
    }
    if matches!(output.stop_reason, StopReason::Aborted | StopReason::Error) {
        let message = output
            .error_message
            .clone()
            .filter(|message| !message.is_empty())
            .unwrap_or_else(|| "An unknown error occurred".to_owned());
        return Err(ErrorObject::new(message).thrown());
    }
    done_reason(output.stop_reason)
        .ok_or_else(|| ErrorObject::new("An unknown error occurred").thrown())
}

/// The catch block shared with the Azure API: settles the message as
/// `error`/`aborted` with `error_message`, records the eukhe stream-failure
/// diagnostic, and ends the stream.
pub(crate) fn fail_stream(
    stream: &AssistantMessageEventStream,
    mut output: AssistantMessage,
    error: &Thrown,
    aborted: bool,
    error_message: String,
    request_id: Option<&str>,
) {
    output.stop_reason = if aborted {
        StopReason::Aborted
    } else {
        StopReason::Error
    };
    let failure = stream_failure_of(
        error,
        aborted,
        output.raw_stop_reason.as_deref(),
        request_id,
    );
    output.error_message = Some(error_message);
    // eukhe addition: provider stream-failure diagnostics.
    let (provider, model_id, api) = (
        output.provider.clone(),
        output.model.clone(),
        output.api.clone(),
    );
    record_stream_failure((&provider, &model_id, &api), &mut output, &failure);
    stream.push(AssistantMessageEvent::Error {
        reason: if aborted {
            ErrorReason::Aborted
        } else {
            ErrorReason::Error
        },
        error: output.clone(),
    });
    stream.end(Some(output));
}

async fn run(
    model: &Model,
    context: &TranscriptContext,
    options: &ProviderStreamOptions,
    output: &mut AssistantMessage,
    stream: &AssistantMessageEventStream,
    request_id: &mut Option<String>,
) -> Result<crate::types::DoneReason, Thrown> {
    let request = &options.stream.request;
    let api = OpenAIResponsesOptions::from_extra(&options.extra);
    let api_key = get_client_api_key(
        &model.provider,
        request.api_key.as_deref(),
        request.headers.as_ref(),
    )?;
    let cache_retention =
        resolve_cache_retention(options.stream.cache_retention, request.env.as_ref());
    let cache_session_id = if cache_retention == CacheRetention::None {
        None
    } else {
        options.stream.session_id.as_deref()
    };
    let compat = get_compat(model);
    let grammar = create_grammar_tool_input_properties(
        Some(&get_declared_tools(context.messages())),
        compat.supports_openai_grammar_tools,
    )?;
    let client = create_client(model, context, api_key, options, cache_session_id);
    let mut params = build_params(model, context, options, &api, &compat, &grammar)?;
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
        || client.post_stream("/responses", &params, &request_options),
        &ProviderRetryOptions {
            max_retries: request.max_retries,
            max_retry_delay_ms: request.max_retry_delay_ms,
            signal: request.signal.clone(),
        },
    )
    .await?;
    *request_id = response
        .headers
        .get("x-request-id")
        .and_then(|value| value.to_str().ok())
        .map(str::to_owned);
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
    stream.push(AssistantMessageEvent::Start {
        partial: output.clone(),
    });

    let model_id = model.id.clone();
    let stream_options = OpenAIResponsesStreamOptions {
        on_provider_stream_event: options.stream.on_provider_stream_event.clone(),
        service_tier: effective_service_tier(model, options, &api)
            .and_then(|tier| tier.as_str().map(str::to_owned)),
        grammar_tool_input_properties: Some(grammar),
        resolve_service_tier: None,
        apply_service_tier_pricing: Some(Arc::new(move |usage, service_tier| {
            apply_service_tier_pricing(usage, service_tier, &model_id);
        })),
    };
    process_responses_stream(response.events, output, stream, model, &stream_options).await?;

    let aborted = request
        .signal
        .as_ref()
        .is_some_and(eukhe_chord::context::AbortSignal::aborted);
    finish_checks(
        output,
        aborted,
        "OpenAI Responses stream ended without a stop reason",
    )
}

/// TS `stream`: the `openai-responses` stream function.
#[must_use]
pub fn stream(
    model: &Model,
    context: &TranscriptContext,
    options: ProviderStreamOptions,
) -> AssistantMessageEventStream {
    let stream = AssistantMessageEventStream::new();
    let normalized_context = resolve_transcript(
        context.clone(),
        Some(get_compat(model).supports_mid_convo_system_messages),
    );
    let model = model.clone();
    let target = stream.clone();
    tokio::spawn(async move {
        let mut output = new_output(&model);
        let mut request_id = None;
        let result = run(
            &model,
            &normalized_context,
            &options,
            &mut output,
            &target,
            &mut request_id,
        )
        .await;
        match result {
            Ok(reason) => {
                target.push(AssistantMessageEvent::Done {
                    reason,
                    message: output.clone(),
                });
                target.end(Some(output));
            }
            Err(error) => {
                let aborted = options
                    .stream
                    .request
                    .signal
                    .as_ref()
                    .is_some_and(eukhe_chord::context::AbortSignal::aborted);
                let prefix = if model.provider == "openai" {
                    "OpenAI API error".to_owned()
                } else {
                    format!("{} API error", model.provider)
                };
                let error_message =
                    format_provider_error(&normalize_provider_error(&error), Some(&prefix));
                // Sign in with ChatGPT shares the subscription's usage limit with other apps.
                let error_message =
                    if error_message.contains("subscription_sharing_usage_limit_exceeded") {
                        format!("{error_message}\nCheck your ChatGPT usage: {CHATGPT_USAGE_URL}")
                    } else {
                        error_message
                    };
                fail_stream(
                    &target,
                    output,
                    &error,
                    aborted,
                    error_message,
                    request_id.as_deref(),
                );
            }
        }
    });
    stream
}

/// TS `streamSimple`.
#[must_use]
#[allow(clippy::needless_pass_by_value)] // Signature fixed by `StreamSimpleFn`.
pub fn stream_simple(
    model: &Model,
    context: &TranscriptContext,
    options: SimpleStreamOptions,
) -> AssistantMessageEventStream {
    if let Err(error) = get_client_api_key(
        &model.provider,
        options.stream.request.api_key.as_deref(),
        options.stream.request.headers.as_ref(),
    ) {
        // TS throws synchronously; the stream contract encodes it.
        return lazy_stream(model, async move { Err(error) });
    }
    let api_key = options.stream.request.api_key.clone();
    let base = build_base_options(model, context, Some(&options), api_key.as_deref());
    let mut extra = JsonObject::new();
    if let Some(tool_choice) = options.tool_choice {
        extra.insert("toolChoice".to_owned(), json!(tool_choice.as_str()));
    }
    if let Some(reasoning) = options.reasoning {
        let clamped = clamp_thinking_level(model, ModelThinkingLevel::from(reasoning));
        if clamped != ModelThinkingLevel::Off {
            extra.insert("reasoningEffort".to_owned(), json!(clamped.as_str()));
        }
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

/// The `openai-responses` module: TS exports `stream` and `streamSimple`.
#[must_use]
pub fn streams() -> ProviderStreams {
    ProviderStreams {
        stream: Arc::new(stream),
        stream_simple: Arc::new(stream_simple),
        fetch_deferred: None,
        cancel_deferred: None,
    }
}
