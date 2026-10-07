//! The `anthropic-messages` wire API: port of `api/anthropic-messages.ts`.
//!
//! Submodules: [`client`] emulates the `@anthropic-ai/sdk` request path the
//! TS module drives, [`federation`] the SDK's workload identity federation,
//! [`params`] builds the request body, [`sse`] decodes the event stream,
//! and [`events`] folds stream events into the assistant message.
//!
//! eukhe additions on top of v1.0.4:
//! - explicit prompt-cache breakpoints (`TextContent::cache_breakpoint`):
//!   marked user text blocks carry `cache_control`, the optional marks share
//!   the four-mark budget, and over-marked transcripts fail before sending
//!   (see [`crate::api::cache_breakpoints`]);
//! - provider stream-failure diagnostics: failed streams carry a
//!   `provider_stream_failure` diagnostic
//!   ([`crate::utils::stream_failure::record_stream_failure`]).

mod client;
mod events;
mod federation;
mod params;
mod sse;

use std::sync::Arc;

use eukhe_types::pi_ai::{
    AnthropicMessagesCompat, AnthropicSessionAffinityFormat, AssistantMessage,
    AssistantMessageEvent, CacheRetention, DoneReason, ErrorReason, JsonObject, JsonValue, Model,
    ModelCompat, ModelThinkingLevel, ProviderHeaders, StopReason, ThinkingLevel, ToolChoice,
    TranscriptContext, Usage,
};
use serde::Deserialize;

use self::client::{ClientAuth, SdkClient};
use self::federation::{get_anthropic_federation, has_request_auth, AnthropicFederationConfig};
use super::ProviderStreams;
use crate::api::cache_breakpoints::excess_breakpoints_error;
use crate::api::github_copilot_headers::{build_copilot_dynamic_headers, has_copilot_vision_input};
use crate::api::simple_options::{
    adjust_max_tokens_for_thinking, build_base_options, clamp_max_tokens_to_context,
};
use crate::types::{FetchFunction, ProviderStreamOptions, SimpleStreamOptions, StreamOptions};
use crate::utils::diagnostics::{ErrorObject, Thrown};
use crate::utils::event_stream::AssistantMessageEventStream;
use crate::utils::now_ms;
use crate::utils::pi_user_agent::get_pi_user_agent;
use crate::utils::stream_failure::record_stream_failure;
use crate::utils::transcript::{get_current_tools, resolve_transcript};

/// The API id.
pub const API_ID: &str = "anthropic-messages";

/// Stealth mode: the Claude Code version mimicked with OAuth tokens.
const CLAUDE_CODE_VERSION: &str = "2.1.280";

/// The Claude Code identity system block required with OAuth tokens.
const CLAUDE_CODE_SYSTEM_PROMPT: &str = "You are Claude Code, Anthropic's official CLI for Claude.";

/// TS `AnthropicEffort` (`"low" | "medium" | "high" | "xhigh" | "max"`).
/// Kept as the wire string: TS casts `thinkingLevelMap` values to it unchecked.
pub type AnthropicEffort = String;

/// TS `AnthropicThinkingDisplay` (`"summarized" | "omitted"`), as the wire string.
pub type AnthropicThinkingDisplay = String;

/// TS `AnthropicOptions.toolChoice`: `"auto" | "any" | "none" | { type: "tool", name }`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AnthropicToolChoice {
    Auto,
    Any,
    None,
    /// `{ type: "tool", name }`: force a specific tool.
    Tool {
        name: String,
    },
}

/// Construction options of an [`AnthropicClient`] (the SDK constructor
/// options pi passes).
#[derive(Clone, Default)]
pub struct AnthropicClientOptions {
    pub base_url: String,
    /// Sent as `X-Api-Key`.
    pub api_key: Option<String>,
    /// Sent as `Authorization: Bearer`.
    pub auth_token: Option<String>,
    pub default_headers: ProviderHeaders,
    pub fetch: Option<FetchFunction>,
}

/// A pre-built client (TS `AnthropicOptions.client`): skips internal client
/// construction, e.g. to target another host sharing the Messages API.
#[derive(Clone)]
pub struct AnthropicClient {
    inner: SdkClient,
}

impl AnthropicClient {
    /// TS `new Anthropic(options)`.
    #[must_use]
    pub fn new(options: AnthropicClientOptions) -> Self {
        Self {
            inner: SdkClient {
                base_url: options.base_url,
                auth: ClientAuth::Static {
                    api_key: options.api_key,
                    auth_token: options.auth_token,
                },
                default_headers: options.default_headers,
                fetch: options.fetch,
            },
        }
    }
}

impl std::fmt::Debug for AnthropicClient {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("AnthropicClient")
            .field("base_url", &self.inner.base_url)
            .finish_non_exhaustive()
    }
}

/// TS `AnthropicOptions`: the shared stream options plus the API-specific
/// keys (`extra` keys `thinkingEnabled`, `thinkingBudgetTokens`, `effort`,
/// `thinkingDisplay`, `interleavedThinking`, `toolChoice`).
#[derive(Debug, Clone, Default)]
pub struct AnthropicOptions {
    pub stream: StreamOptions,
    /// Enable extended thinking (adaptive or budget-based by model).
    pub thinking_enabled: Option<bool>,
    /// Token budget for budget-based thinking. Default 1024.
    pub thinking_budget_tokens: Option<u64>,
    /// Effort level for adaptive thinking models.
    pub effort: Option<AnthropicEffort>,
    /// How thinking content is returned. Default `"summarized"`.
    pub thinking_display: Option<AnthropicThinkingDisplay>,
    /// Request the interleaved thinking beta on non-adaptive models. Default true.
    pub interleaved_thinking: Option<bool>,
    pub tool_choice: Option<AnthropicToolChoice>,
    /// Pre-built client; skips internal client construction.
    pub client: Option<AnthropicClient>,
}

/// The `extra` keys of [`ProviderStreamOptions`] this API reads.
#[derive(Deserialize, Default)]
#[serde(rename_all = "camelCase")]
struct ExtraOptions {
    thinking_enabled: Option<bool>,
    thinking_budget_tokens: Option<u64>,
    effort: Option<String>,
    thinking_display: Option<String>,
    interleaved_thinking: Option<bool>,
    tool_choice: Option<JsonValue>,
}

/// Invalid API-specific options.
#[derive(Debug, Clone, thiserror::Error)]
#[error("Invalid anthropic-messages options: {0}")]
pub struct InvalidAnthropicOptions(String);

fn parse_tool_choice(value: &JsonValue) -> Result<AnthropicToolChoice, InvalidAnthropicOptions> {
    match value {
        JsonValue::String(choice) => match choice.as_str() {
            "auto" => Ok(AnthropicToolChoice::Auto),
            "any" => Ok(AnthropicToolChoice::Any),
            "none" => Ok(AnthropicToolChoice::None),
            other => Err(InvalidAnthropicOptions(format!(
                "unknown toolChoice \"{other}\""
            ))),
        },
        other => match (
            other.get("type").and_then(JsonValue::as_str),
            other.get("name").and_then(JsonValue::as_str),
        ) {
            (Some("tool"), Some(name)) => Ok(AnthropicToolChoice::Tool {
                name: name.to_owned(),
            }),
            _ => Err(InvalidAnthropicOptions(format!(
                "toolChoice must be \"auto\", \"any\", \"none\", or {{ type: \"tool\", name }}, got {other}"
            ))),
        },
    }
}

impl AnthropicOptions {
    /// Read the API-specific keys from [`ProviderStreamOptions::extra`].
    ///
    /// # Errors
    ///
    /// A known key holding a value of the wrong type.
    pub fn from_provider_options(
        options: ProviderStreamOptions,
    ) -> Result<Self, InvalidAnthropicOptions> {
        let extra: ExtraOptions = serde_json::from_value(JsonValue::Object(options.extra))
            .map_err(|error| InvalidAnthropicOptions(error.to_string()))?;
        Ok(Self {
            stream: options.stream,
            thinking_enabled: extra.thinking_enabled,
            thinking_budget_tokens: extra.thinking_budget_tokens,
            effort: extra.effort,
            thinking_display: extra.thinking_display,
            interleaved_thinking: extra.interleaved_thinking,
            tool_choice: extra
                .tool_choice
                .filter(|value| !value.is_null())
                .as_ref()
                .map(parse_tool_choice)
                .transpose()?,
            client: None,
        })
    }
}

/// The model's Anthropic compat block, when it has one.
pub(crate) fn model_compat(model: &Model) -> Option<&AnthropicMessagesCompat> {
    match &model.compat {
        Some(ModelCompat::AnthropicMessages(compat)) => Some(compat),
        _ => None,
    }
}

/// TS `getAnthropicCompat`: compat flags with their defaults.
#[allow(clippy::struct_excessive_bools)] // Mirrors the TS compat object.
pub(crate) struct ResolvedCompat {
    pub(crate) supports_eager_tool_input_streaming: bool,
    pub(crate) supports_long_cache_retention: bool,
    pub(crate) send_session_affinity_headers: bool,
    pub(crate) session_affinity_format: Option<AnthropicSessionAffinityFormat>,
    pub(crate) supports_cache_control_on_tools: bool,
    pub(crate) supports_temperature: bool,
    pub(crate) allow_empty_signature: bool,
    pub(crate) supports_strict_tools: bool,
    pub(crate) supports_mid_convo_system_messages: bool,
    pub(crate) supports_mid_convo_tool_changes: bool,
}

pub(crate) fn get_anthropic_compat(model: &Model) -> ResolvedCompat {
    let is_open_router = model.provider == "openrouter" || model.base_url.contains("openrouter.ai");
    let compat = model_compat(model);
    let flag = |get: fn(&AnthropicMessagesCompat) -> Option<bool>, default: bool| {
        compat.and_then(get).unwrap_or(default)
    };
    ResolvedCompat {
        supports_eager_tool_input_streaming: flag(|c| c.supports_eager_tool_input_streaming, true),
        supports_long_cache_retention: flag(|c| c.supports_long_cache_retention, true),
        send_session_affinity_headers: flag(|c| c.send_session_affinity_headers, is_open_router),
        session_affinity_format: compat
            .and_then(|c| c.session_affinity_format)
            .or(is_open_router.then_some(AnthropicSessionAffinityFormat::OpenRouter)),
        supports_cache_control_on_tools: flag(|c| c.supports_cache_control_on_tools, true),
        supports_temperature: flag(|c| c.supports_temperature, true),
        allow_empty_signature: flag(|c| c.allow_empty_signature, false),
        supports_strict_tools: flag(|c| c.supports_strict_tools, false),
        supports_mid_convo_system_messages: flag(|c| c.supports_mid_convo_system_messages, false),
        supports_mid_convo_tool_changes: flag(|c| c.supports_mid_convo_tool_changes, false),
    }
}

fn supports_mid_convo_effort(model: &Model) -> bool {
    model_compat(model).and_then(|compat| compat.supports_mid_convo_effort) == Some(true)
}

/// TS `mergeHeaders` (`Object.assign`: case-sensitive keys, a repeated key
/// keeps its first position) after `{ "User-Agent": getPiUserAgent() }`.
fn merge_client_headers(sources: &[Option<&ProviderHeaders>]) -> ProviderHeaders {
    let mut merged = ProviderHeaders::new();
    merged.insert("User-Agent".into(), Some(get_pi_user_agent().to_owned()));
    for headers in sources.iter().flatten() {
        for (name, value) in *headers {
            merged.insert(name.clone(), value.clone());
        }
    }
    merged
}

fn to_provider_headers<'a>(
    headers: impl IntoIterator<Item = (&'a String, &'a String)>,
) -> ProviderHeaders {
    headers
        .into_iter()
        .map(|(name, value)| (name.clone(), Some(value.clone())))
        .collect()
}

fn browser_headers() -> ProviderHeaders {
    let mut headers = ProviderHeaders::new();
    headers.insert("accept".into(), Some("application/json".into()));
    headers.insert(
        "anthropic-dangerous-direct-browser-access".into(),
        Some("true".into()),
    );
    headers
}

/// TS `isOAuthToken`.
fn is_oauth_token(api_key: &str) -> bool {
    api_key.contains("sk-ant-oat")
}

/// Inputs of [`create_client`] (TS `createClient` parameters).
struct ClientInputs<'a> {
    api_key: Option<&'a str>,
    options_headers: Option<&'a ProviderHeaders>,
    fetch: Option<&'a FetchFunction>,
    dynamic_headers: Option<&'a ProviderHeaders>,
    session_id: Option<&'a str>,
    federation: Option<&'a AnthropicFederationConfig>,
}

/// TS `createClient`: the client and whether the key is an OAuth token.
fn create_client(model: &Model, inputs: &ClientInputs<'_>) -> (SdkClient, bool) {
    let model_headers = model.headers.as_ref().map(to_provider_headers);
    let fetch = inputs.fetch.cloned();
    if model.provider == "github-copilot" {
        let client = SdkClient {
            base_url: model.base_url.clone(),
            auth: ClientAuth::Static {
                api_key: None,
                auth_token: inputs.api_key.map(str::to_owned),
            },
            default_headers: merge_client_headers(&[
                Some(&browser_headers()),
                model_headers.as_ref(),
                inputs.dynamic_headers,
                inputs.options_headers,
            ]),
            fetch,
        };
        return (client, false);
    }

    if let Some(api_key) = inputs.api_key.filter(|key| is_oauth_token(key)) {
        let mut identity = browser_headers();
        identity.insert(
            "user-agent".into(),
            Some(format!("claude-cli/{CLAUDE_CODE_VERSION}")),
        );
        identity.insert("x-app".into(), Some("cli".into()));
        let client = SdkClient {
            base_url: model.base_url.clone(),
            auth: ClientAuth::Static {
                api_key: None,
                auth_token: Some(api_key.to_owned()),
            },
            default_headers: merge_client_headers(&[
                Some(&identity),
                model_headers.as_ref(),
                inputs.options_headers,
            ]),
            fetch,
        };
        return (client, true);
    }

    let compat = get_anthropic_compat(model);
    let mut session_affinity = ProviderHeaders::new();
    if let Some(session_id) = inputs.session_id.filter(|id| !id.is_empty()) {
        if compat.send_session_affinity_headers {
            let header = match compat.session_affinity_format {
                Some(AnthropicSessionAffinityFormat::OpenRouter) => "x-session-id",
                None => "x-session-affinity",
            };
            session_affinity.insert(header.into(), Some(session_id.to_owned()));
        }
    }
    let default_headers = merge_client_headers(&[
        Some(&browser_headers()),
        Some(&session_affinity),
        model_headers.as_ref(),
        inputs.options_headers,
    ]);
    if let Some(federation) = inputs.federation {
        let auth = federation::federation_auth(&model.base_url, federation, inputs.fetch);
        let client = SdkClient {
            base_url: model.base_url.clone(),
            auth: ClientAuth::Federation(auth),
            default_headers,
            fetch,
        };
        return (client, false);
    }
    let client = SdkClient {
        base_url: model.base_url.clone(),
        auth: ClientAuth::Static {
            api_key: inputs.api_key.map(str::to_owned),
            auth_token: None,
        },
        default_headers,
        fetch,
    };
    (client, false)
}

/// The failure of a stream: the TS thrown error, plus the provider error
/// the eukhe stream-failure diagnostic classifies.
pub(crate) struct StreamFailure {
    pub(crate) thrown: Thrown,
    pub(crate) diagnostic: Box<crate::utils::stream_failure::ProviderError>,
}

impl StreamFailure {
    pub(crate) fn plain(thrown: Thrown) -> Self {
        let diagnostic = Box::new(crate::utils::stream_failure::ProviderError::Message(
            thrown.to_string(),
        ));
        Self { thrown, diagnostic }
    }

    pub(crate) fn message(text: impl Into<String>) -> Self {
        Self::plain(ErrorObject::new(text).thrown())
    }
}

fn empty_output(model: &Model, provider_thinking_level: Option<String>) -> AssistantMessage {
    AssistantMessage {
        content: Vec::new(),
        api: model.api.clone(),
        provider: model.provider.clone(),
        model: model.id.clone(),
        response_model: None,
        response_id: None,
        provider_thinking_level,
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

/// A stream that fails before the request starts.
fn error_stream(model: &Model, message: String) -> AssistantMessageEventStream {
    let mut output = empty_output(model, None);
    output.stop_reason = StopReason::Error;
    output.error_message = Some(message);
    let stream = AssistantMessageEventStream::new();
    stream.push(AssistantMessageEvent::Error {
        reason: ErrorReason::Error,
        error: output.clone(),
    });
    stream.end(Some(output));
    stream
}

/// TS `stream` with [`ProviderStreamOptions`]: API-specific keys come from
/// `extra`.
#[must_use]
pub fn stream(
    model: &Model,
    context: &TranscriptContext,
    options: ProviderStreamOptions,
) -> AssistantMessageEventStream {
    match AnthropicOptions::from_provider_options(options) {
        Ok(options) => stream_anthropic(model, context, options),
        Err(error) => error_stream(model, error.to_string()),
    }
}

/// TS `stream` with typed [`AnthropicOptions`]. Must be called inside a
/// tokio runtime.
#[must_use]
pub fn stream_anthropic(
    model: &Model,
    context: &TranscriptContext,
    options: AnthropicOptions,
) -> AssistantMessageEventStream {
    if let Some(error) = excess_breakpoints_error(model, context.messages()) {
        return error;
    }
    let stream = AssistantMessageEventStream::new();
    let normalized = resolve_transcript(
        context.clone(),
        Some(get_anthropic_compat(model).supports_mid_convo_system_messages),
    );
    let model = model.clone();
    let target = stream.clone();
    tokio::spawn(async move {
        let provider_thinking_level = supports_mid_convo_effort(&model)
            .then(|| options.effort.clone().unwrap_or_else(|| "high".to_owned()));
        let mut output = empty_output(&model, provider_thinking_level);
        let result = run(&model, &normalized, &options, &mut output, &target).await;
        let signal = options.stream.request.signal.as_ref();
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
                target.push(AssistantMessageEvent::Done {
                    reason,
                    message: output.clone(),
                });
                target.end(Some(output));
            }
            Err(failure) => {
                let aborted = signal.is_some_and(eukhe_chord::context::AbortSignal::aborted);
                output.stop_reason = if aborted {
                    StopReason::Aborted
                } else {
                    StopReason::Error
                };
                output.error_message = Some(failure.thrown.to_string());
                let diagnostic = if aborted {
                    crate::utils::stream_failure::ProviderError::Aborted
                } else {
                    *failure.diagnostic
                };
                record_stream_failure(
                    (&model.provider, &model.id, &model.api),
                    &mut output,
                    &diagnostic,
                );
                target.push(AssistantMessageEvent::Error {
                    reason: if aborted {
                        ErrorReason::Aborted
                    } else {
                        ErrorReason::Error
                    },
                    error: output.clone(),
                });
                target.end(Some(output));
            }
        }
    });
    stream
}

/// The request and stream loop of TS `stream`.
async fn run(
    model: &Model,
    context: &TranscriptContext,
    options: &AnthropicOptions,
    output: &mut AssistantMessage,
    stream: &AssistantMessageEventStream,
) -> Result<(), StreamFailure> {
    let request = &options.stream.request;
    let (client, is_oauth) = if let Some(client) = &options.client {
        (client.inner.clone(), false)
    } else {
        let api_key = request.api_key.as_deref();
        let federation = get_anthropic_federation(
            model,
            api_key,
            request.headers.as_ref(),
            request.env.as_ref(),
        );
        if federation.is_none() && !has_request_auth(api_key, request.headers.as_ref()) {
            return Err(StreamFailure::message(format!(
                "No API key for provider: {}",
                model.provider
            )));
        }
        let copilot_headers = (model.provider == "github-copilot").then(|| {
            let has_images = has_copilot_vision_input(context.messages());
            to_provider_headers(&build_copilot_dynamic_headers(
                context.messages(),
                has_images,
            ))
        });
        let cache_retention =
            params::resolve_cache_retention(options.stream.cache_retention, request.env.as_ref());
        let cache_session_id = if cache_retention == CacheRetention::None {
            None
        } else {
            options.stream.session_id.as_deref()
        };
        create_client(
            model,
            &ClientInputs {
                api_key,
                options_headers: request.headers.as_ref(),
                fetch: request.fetch.as_ref(),
                dynamic_headers: copilot_headers.as_ref(),
                session_id: cache_session_id,
                federation: federation.as_ref(),
            },
        )
    };
    let mut params = params::build_params(model, context.messages(), is_oauth, options)
        .map_err(StreamFailure::plain)?;
    if let Some(on_payload) = &request.on_payload {
        let next = on_payload(JsonValue::Object(params.clone()), model)
            .await
            .map_err(StreamFailure::plain)?;
        if let Some(next) = next {
            // TS `{ ...nextParams, stream: true }`.
            params = match next {
                JsonValue::Object(object) => object,
                _ => JsonObject::new(),
            };
            params.insert("stream".into(), true.into());
        }
    }
    let response = events::send_with_retries(&client, params, options).await?;
    if let Some(on_response) = &request.on_response {
        on_response(
            crate::types::ProviderResponse {
                status: response.status().as_u16(),
                headers: crate::utils::headers::headers_to_record(response.headers()),
            },
            model,
        )
        .await
        .map_err(StreamFailure::plain)?;
    }
    stream.push(AssistantMessageEvent::Start {
        partial: output.clone(),
    });
    let current_tools = get_current_tools(context.messages());
    events::consume(
        model,
        response,
        options,
        is_oauth,
        &current_tools,
        output,
        stream,
    )
    .await
}

/// TS `mapThinkingLevelToEffort`.
fn map_thinking_level_to_effort(model: &Model, level: ThinkingLevel) -> AnthropicEffort {
    if let Some(Some(mapped)) = model
        .thinking_level_map
        .as_ref()
        .and_then(|map| map.get(&ModelThinkingLevel::from(level)))
    {
        return mapped.clone();
    }
    match level {
        ThinkingLevel::Minimal | ThinkingLevel::Low => "low",
        ThinkingLevel::Medium => "medium",
        ThinkingLevel::High | ThinkingLevel::Xhigh | ThinkingLevel::Max => "high",
    }
    .to_owned()
}

/// TS `streamSimple`. TS throws the missing-key error synchronously; here
/// it terminates the returned stream.
#[must_use]
pub fn stream_simple(
    model: &Model,
    context: &TranscriptContext,
    options: &SimpleStreamOptions,
) -> AssistantMessageEventStream {
    let request = &options.stream.request;
    if get_anthropic_federation(
        model,
        request.api_key.as_deref(),
        request.headers.as_ref(),
        request.env.as_ref(),
    )
    .is_none()
        && !has_request_auth(request.api_key.as_deref(), request.headers.as_ref())
    {
        return error_stream(
            model,
            format!("No API key for provider: {}", model.provider),
        );
    }

    let base = build_base_options(model, context, Some(options), request.api_key.as_deref());
    let tool_choice = options.tool_choice.map(|choice| match choice {
        ToolChoice::Auto => AnthropicToolChoice::Auto,
        ToolChoice::None => AnthropicToolChoice::None,
    });
    let Some(reasoning) = options.reasoning else {
        return stream_anthropic(
            model,
            context,
            AnthropicOptions {
                stream: base,
                thinking_enabled: Some(false),
                tool_choice,
                ..AnthropicOptions::default()
            },
        );
    };

    if model_compat(model).and_then(|compat| compat.force_adaptive_thinking) == Some(true) {
        let effort = map_thinking_level_to_effort(model, reasoning);
        return stream_anthropic(
            model,
            context,
            AnthropicOptions {
                stream: base,
                thinking_enabled: Some(true),
                effort: Some(effort),
                tool_choice,
                ..AnthropicOptions::default()
            },
        );
    }

    let adjusted = adjust_max_tokens_for_thinking(
        base.max_tokens,
        model.max_tokens,
        reasoning,
        options.thinking_budgets.as_ref(),
    );
    let max_tokens = clamp_max_tokens_to_context(model, context, adjusted.max_tokens);
    let thinking_budget = adjusted
        .thinking_budget
        .min(max_tokens.saturating_sub(1024));
    stream_anthropic(
        model,
        context,
        AnthropicOptions {
            stream: StreamOptions {
                max_tokens: Some(max_tokens),
                ..base
            },
            thinking_enabled: Some(true),
            thinking_budget_tokens: Some(thinking_budget),
            tool_choice,
            ..AnthropicOptions::default()
        },
    )
}

/// The `anthropic-messages` module (no deferred responses).
#[must_use]
pub fn streams() -> ProviderStreams {
    ProviderStreams {
        stream: Arc::new(stream),
        stream_simple: Arc::new(|model, context, options| stream_simple(model, context, &options)),
        fetch_deferred: None,
        cancel_deferred: None,
    }
}
