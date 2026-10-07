//! The `bedrock-converse-stream` wire API: Amazon Bedrock's `ConverseStream`
//! operation. Port of `api/bedrock-converse-stream.ts` (and
//! `bedrock-provider.ts`, the statically importable module object).
//!
//! The TS module drives `@aws-sdk/client-bedrock-runtime`; this port speaks
//! the same wire protocol directly (see [`client`] for the slice of the SDK
//! it reproduces: endpoint rules, `SigV4` or bearer auth, retries, error and
//! event-stream deserialization).
//!
//! API-specific options (TS `BedrockOptions`) arrive in
//! [`ProviderStreamOptions::extra`]: `region`, `profile`, `toolChoice`
//! (`"auto" | "any" | "none" | { type: "tool", name }`), `reasoning`,
//! `thinkingBudgets`, `interleavedThinking`, `thinkingDisplay`
//! (`"summarized" | "omitted"`), `requestMetadata`, and `bearerToken`.
//!
//! eukhe additions on top of v1.0.4: prompt-cache marks for
//! `TextContent::cache_breakpoint` (see [`convert`]) and the
//! `provider_stream_failure` diagnostic.

// Failures carry the SDK error shape (name, message, `$metadata`, raw
// response headers) the TS catch inspects; they are rare and cold, so the
// `Result` size is not worth boxing.
#![allow(clippy::result_large_err)]

mod client;
mod client_config;
mod convert;
mod credentials;
mod event_stream_codec;
mod events;
mod shape_codec;
mod sigv4;
mod smithy_schema;

use std::sync::Arc;

use eukhe_types::pi_ai::{
    AssistantMessage, AssistantMessageEvent, DoneReason, ErrorReason, JsonObject, JsonValue, Model,
    StopReason, ThinkingBudgets, ThinkingLevel, ToolChoice, TranscriptContext, Usage,
};
use serde::Deserialize;

pub use client_config::{AwsCredentials, BedrockClientConfig, BedrockRequestHandler};

use self::client::{BedrockFailure, SendRequest, StreamValue};
use self::events::{handle_metadata, StreamBlocks};
use super::cache_breakpoints::{excess_breakpoints_error, CacheMarkBudget};
use super::lazy::lazy_stream;
use super::simple_options::{
    adjust_max_tokens_for_thinking, build_base_options, clamp_max_tokens_to_context,
    clamp_reasoning,
};
use super::ProviderStreams;
use crate::types::{ProviderStreamOptions, SimpleStreamOptions, StreamOptions};
use crate::utils::diagnostics::{
    append_assistant_message_diagnostic, error_name, AssistantMessageDiagnostic, ErrorObject,
    Thrown, ThrownValue,
};
use crate::utils::error_body::normalize_provider_error;
use crate::utils::event_stream::AssistantMessageEventStream;
use crate::utils::headers::provider_headers_to_record;
use crate::utils::js::{js_to_string, js_trim, json_stringify, number_to_js_string, utf16_len};
use crate::utils::now_ms;
use crate::utils::stream_failure::{
    record_stream_failure, stream_failure_from_stop_reason, ProviderError, ProviderHttpError,
};
use crate::utils::text::get_system_message_text;
use crate::utils::transcript::{
    collapse_system_messages, get_current_tools, get_initial_system_message,
};

/// How Claude's thinking content is returned (TS `BedrockThinkingDisplay`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum BedrockThinkingDisplay {
    /// Thinking blocks contain summarized thinking text (default here).
    Summarized,
    /// Thinking content is redacted; the signature still travels back.
    Omitted,
}

impl BedrockThinkingDisplay {
    /// The wire string.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Summarized => "summarized",
            Self::Omitted => "omitted",
        }
    }
}

/// TS `BedrockOptions.toolChoice`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum BedrockToolChoice {
    Auto,
    Any,
    None,
    Tool { name: String },
}

impl<'de> Deserialize<'de> for BedrockToolChoice {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        #[derive(Deserialize)]
        #[serde(untagged)]
        enum Wire {
            Mode(String),
            Tool {
                #[serde(rename = "type")]
                kind: String,
                name: String,
            },
        }
        match Wire::deserialize(deserializer)? {
            Wire::Mode(mode) => match mode.as_str() {
                "auto" => Ok(Self::Auto),
                "any" => Ok(Self::Any),
                "none" => Ok(Self::None),
                other => Err(serde::de::Error::custom(format!(
                    "unknown tool choice \"{other}\""
                ))),
            },
            Wire::Tool { kind, name } if kind == "tool" => Ok(Self::Tool { name }),
            Wire::Tool { kind, .. } => Err(serde::de::Error::custom(format!(
                "unknown tool choice type \"{kind}\""
            ))),
        }
    }
}

/// TS `BedrockOptions`: the shared stream options plus the Bedrock keys of
/// [`ProviderStreamOptions::extra`].
#[derive(Clone, Default)]
pub(crate) struct BedrockOptions {
    pub(crate) stream: StreamOptions,
    pub(crate) region: Option<String>,
    pub(crate) profile: Option<String>,
    pub(crate) tool_choice: Option<BedrockToolChoice>,
    pub(crate) reasoning: Option<ThinkingLevel>,
    pub(crate) thinking_budgets: Option<ThinkingBudgets>,
    pub(crate) interleaved_thinking: Option<bool>,
    pub(crate) thinking_display: Option<BedrockThinkingDisplay>,
    /// Cost allocation tags (`Record<string, string>`), sent as given.
    pub(crate) request_metadata: Option<JsonValue>,
    pub(crate) bearer_token: Option<String>,
}

/// One optional `extra` key; `null` counts as unset.
fn extra_option<T: for<'de> Deserialize<'de>>(
    extra: &mut JsonObject,
    key: &str,
) -> Result<Option<T>, Thrown> {
    match extra.remove(key) {
        None | Some(JsonValue::Null) => Ok(None),
        Some(value) => serde_json::from_value(value).map(Some).map_err(|error| {
            ErrorObject::named(
                "TypeError",
                format!("Invalid Bedrock option \"{key}\": {error}"),
            )
            .thrown()
        }),
    }
}

impl BedrockOptions {
    fn from_provider_options(options: ProviderStreamOptions) -> Result<Self, Thrown> {
        let ProviderStreamOptions { stream, mut extra } = options;
        let reasoning: Option<String> = extra_option(&mut extra, "reasoning")?;
        let reasoning = match reasoning.as_deref() {
            // TS `!options.reasoning`: the empty string is unset.
            None | Some("") => None,
            Some(level) => Some(
                serde_json::from_value(JsonValue::String(level.to_owned())).map_err(|error| {
                    ErrorObject::named(
                        "TypeError",
                        format!("Invalid Bedrock option \"reasoning\": {error}"),
                    )
                    .thrown()
                })?,
            ),
        };
        Ok(Self {
            stream,
            region: extra_option(&mut extra, "region")?,
            profile: extra_option(&mut extra, "profile")?,
            tool_choice: extra_option(&mut extra, "toolChoice")?,
            reasoning,
            thinking_budgets: extra_option(&mut extra, "thinkingBudgets")?,
            interleaved_thinking: extra_option(&mut extra, "interleavedThinking")?,
            thinking_display: extra_option(&mut extra, "thinkingDisplay")?,
            request_metadata: extra_option(&mut extra, "requestMetadata")?,
            bearer_token: extra_option(&mut extra, "bearerToken")?,
        })
    }
}

/// The Bedrock runtime client configuration `stream` builds for `model` and
/// `options` (TS: the `BedrockRuntimeClientConfig` passed to
/// `new BedrockRuntimeClient`). Exposed for inspection.
///
/// # Errors
///
/// Fails on malformed Bedrock options in `options.extra` or an unusable
/// proxy environment value.
pub fn client_config(
    model: &Model,
    options: &ProviderStreamOptions,
) -> Result<BedrockClientConfig, Thrown> {
    let options = BedrockOptions::from_provider_options(options.clone())?;
    client_config::resolve_client_config(model, &options)
        .map_err(|error| ErrorObject::new(error.to_string()).thrown())
}

/// Human-readable prefixes for Bedrock SDK exception names: downstream retry
/// logic matches patterns like `server.?error` and `service.?unavailable`.
fn bedrock_error_prefix(name: &str) -> &str {
    match name {
        "InternalServerException" => "Internal server error",
        "ModelStreamErrorException" => "Model stream error",
        "ValidationException" => "Validation error",
        "ThrottlingException" => "Throttling error",
        "ServiceUnavailableException" => "Service unavailable",
        other => other,
    }
}

/// Points users at the AWS docs on supported data retention modes.
const BEDROCK_DATA_RETENTION_DOCS_URL: &str =
    "https://docs.aws.amazon.com/bedrock/latest/userguide/data-retention.html";

/// Over-long header values are dropped rather than truncated.
const MAX_BEDROCK_DIAGNOSTIC_VALUE_CHARS: usize = 200;

/// TS `formatBedrockError`.
fn format_bedrock_error(failure: &BedrockFailure) -> String {
    let (norm, service_exception) = match failure {
        BedrockFailure::Sdk(error) => (
            normalize_provider_error(&error.to_error_object().thrown()),
            error.service_exception.then_some(error.name.as_str()),
        ),
        BedrockFailure::Thrown(thrown) => (normalize_provider_error(thrown), None),
    };
    let core = match (norm.message_carries_body, norm.status, norm.body.as_deref()) {
        (false, Some(status), Some(body)) => format!("{}: {body}", number_to_js_string(status)),
        _ => norm.message.clone(),
    };
    let data_retention_hint = if core.to_lowercase().contains("data retention mode") {
        format!(" See {BEDROCK_DATA_RETENTION_DOCS_URL} for supported data retention modes.")
    } else {
        String::new()
    };
    match service_exception {
        Some(name) => format!(
            "{}: {core}{data_retention_hint}",
            bedrock_error_prefix(name)
        ),
        None => format!("{core}{data_retention_hint}"),
    }
}

/// TS `normalizeDiagnosticValue`.
fn normalize_diagnostic_value(value: Option<&str>) -> Option<String> {
    let trimmed = js_trim(value?);
    let length = utf16_len(trimmed);
    (length > 0 && length <= MAX_BEDROCK_DIAGNOSTIC_VALUE_CHARS).then(|| trimmed.to_owned())
}

/// TS `appendBedrockFailureDiagnostic`: status, modeled error code, and
/// request id, each only when known.
fn append_bedrock_failure_diagnostic(
    output: &mut AssistantMessage,
    failure: &BedrockFailure,
    fallback_request_id: Option<&str>,
) {
    let (status, name, request_id) = match failure {
        BedrockFailure::Sdk(error) => {
            let metadata = error.metadata.as_ref();
            (
                metadata.and_then(|metadata| metadata.http_status_code),
                Some(error.name.clone()),
                metadata.and_then(|metadata| metadata.request_id.clone()),
            )
        }
        BedrockFailure::Thrown(thrown) => {
            let status = thrown
                .downcast_ref::<ErrorObject>()
                .and_then(|error| error.metadata_http_status_code.as_ref())
                .and_then(JsonValue::as_u64)
                .and_then(|status| u16::try_from(status).ok());
            let name = (!thrown.is::<ThrownValue>()).then(|| error_name(thrown.as_ref()));
            (status, name, None)
        }
    };
    let mut details = JsonObject::new();
    if let Some(status) = status {
        details.insert("status".to_owned(), status.into());
    }
    if let Some(code) = name
        .filter(|name| name.ends_with("Exception"))
        .and_then(|name| normalize_diagnostic_value(Some(&name)))
    {
        details.insert("errorCode".to_owned(), code.into());
    }
    if let Some(request_id) = normalize_diagnostic_value(request_id.as_deref())
        .or_else(|| fallback_request_id.map(str::to_owned))
    {
        details.insert("requestId".to_owned(), request_id.into());
    }
    if details.is_empty() {
        return;
    }
    append_assistant_message_diagnostic(
        output,
        AssistantMessageDiagnostic {
            kind: "bedrock_response_failure".to_owned(),
            timestamp: now_ms(),
            error: None,
            details: Some(details),
        },
    );
}

/// eukhe addition: the classified failure behind the `provider_stream_failure`
/// diagnostic, as the old eukhe Bedrock provider recorded it.
fn provider_error(
    failure: &BedrockFailure,
    error_message: &str,
    stop_reason_failure: Option<&str>,
    request_id: Option<&str>,
) -> ProviderError {
    match failure {
        BedrockFailure::Sdk(error) if error.service_exception => {
            ProviderError::Http(ProviderHttpError {
                message: error_message.to_owned(),
                status: None,
                body: None,
                headers: std::collections::HashMap::new(),
                request_id: error
                    .metadata
                    .as_ref()
                    .and_then(|metadata| metadata.request_id.clone())
                    .or_else(|| request_id.map(str::to_owned)),
                sdk_name: Some(error.name.clone()),
                retry_after_ms: None,
                provider_error_type: None,
            })
        }
        BedrockFailure::Thrown(_) if stop_reason_failure.is_some() => ProviderError::StreamFailure(
            stream_failure_from_stop_reason(stop_reason_failure, request_id),
        ),
        BedrockFailure::Sdk(_) | BedrockFailure::Thrown(_) => {
            ProviderError::Message(error_message.to_owned())
        }
    }
}

/// TS `new Error(message)` as a failure.
fn error(message: impl Into<String>) -> BedrockFailure {
    BedrockFailure::Thrown(ErrorObject::new(message).thrown())
}

fn create_output(model: &Model) -> AssistantMessage {
    AssistantMessage {
        content: Vec::new(),
        api: "bedrock-converse-stream".into(),
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

/// JS truthiness of a stream item value.
fn truthy(value: &JsonValue) -> bool {
    match value {
        JsonValue::Null => false,
        JsonValue::Bool(flag) => *flag,
        JsonValue::Number(number) => number.as_f64().is_some_and(|n| n != 0.0),
        JsonValue::String(text) => !text.is_empty(),
        JsonValue::Array(_) | JsonValue::Object(_) => true,
    }
}

/// The request body `stream` builds (TS `commandInput`).
fn build_command_input(
    model: &Model,
    context: &TranscriptContext,
    options: &BedrockOptions,
) -> Result<JsonObject, BedrockFailure> {
    let env = options.stream.request.env.as_ref();
    let supports_strict_mode = model
        .compat
        .as_ref()
        .and_then(|compat| compat.as_bedrock())
        .and_then(|compat| compat.supports_strict_mode)
        .unwrap_or(false);
    let cache_retention = convert::resolve_cache_retention(options.stream.cache_retention, env);
    let inference_max_tokens = options
        .stream
        .max_tokens
        .or_else(|| convert::is_anthropic_claude_model(model).then_some(model.max_tokens));
    let messages = context.messages();
    let initial_system_prompt = get_initial_system_message(messages).map(get_system_message_text);
    let converted = convert::convert_messages(messages, model, cache_retention, env)?;
    // eukhe addition: the message marks are fixed; the system cache point
    // takes a slot only when one is left.
    let mut budget = CacheMarkBudget::after_message_marks(&converted, "cachePoint");
    let system = convert::build_system_prompt(
        initial_system_prompt.as_deref(),
        model,
        cache_retention,
        env,
        &mut budget,
    );
    let mut inference_config = JsonObject::new();
    if let Some(max_tokens) = inference_max_tokens {
        inference_config.insert("maxTokens".to_owned(), max_tokens.into());
    }
    if let Some(temperature) = options.stream.temperature {
        inference_config.insert("temperature".to_owned(), temperature.into());
    }
    let tool_config = convert::convert_tool_config(
        &get_current_tools(messages),
        options.tool_choice.as_ref(),
        supports_strict_mode,
    )
    .map_err(|error| BedrockFailure::Thrown(error.into()))?;

    let mut input = JsonObject::new();
    input.insert("modelId".to_owned(), model.id.clone().into());
    input.insert("messages".to_owned(), JsonValue::Array(converted));
    if let Some(system) = system {
        input.insert("system".to_owned(), JsonValue::Array(system));
    }
    input.insert(
        "inferenceConfig".to_owned(),
        JsonValue::Object(inference_config),
    );
    if let Some(tool_config) = tool_config {
        input.insert("toolConfig".to_owned(), tool_config);
    }
    if let Some(fields) = convert::build_additional_model_request_fields(model, options) {
        input.insert("additionalModelRequestFields".to_owned(), fields);
    }
    if let Some(metadata) = &options.request_metadata {
        input.insert("requestMetadata".to_owned(), metadata.clone());
    }
    Ok(input)
}

/// The scratch state shared between the TS `try` body and its `catch`.
struct StreamRun<'a> {
    model: &'a Model,
    options: &'a BedrockOptions,
    output: AssistantMessage,
    blocks: StreamBlocks,
    target: &'a AssistantMessageEventStream,
    /// Kept outside the `try` so the `catch` can correlate a mid-stream
    /// failure: exceptions delivered as stream events carry no HTTP metadata.
    response_request_id: Option<String>,
}

impl StreamRun<'_> {
    fn aborted(&self) -> bool {
        self.options
            .stream
            .request
            .signal
            .as_ref()
            .is_some_and(eukhe_chord::context::AbortSignal::aborted)
    }

    /// The body of the TS `try` block up to `done`.
    // A 1:1 port of the TS stream loop, kept in one piece like the source.
    #[allow(clippy::too_many_lines)]
    async fn run(&mut self, context: &TranscriptContext) -> Result<DoneReason, BedrockFailure> {
        let config = client_config::resolve_client_config(self.model, self.options)
            .map_err(|proxy_error| error(proxy_error.to_string()))?;
        let custom_headers =
            provider_headers_to_record(&[self.options.stream.request.headers.as_ref()]);
        let mut command_input =
            JsonValue::Object(build_command_input(self.model, context, self.options)?);
        if let Some(on_payload) = &self.options.stream.request.on_payload {
            if let Some(next) = on_payload(command_input.clone(), self.model).await? {
                command_input = next;
            }
        }
        let empty = JsonObject::new();
        let input = command_input.as_object().unwrap_or(&empty);
        let model_id = match input.get("modelId") {
            None | Some(JsonValue::Null) => {
                return Err(error("No value provided for input HTTP label: modelId."));
            }
            Some(model_id) => js_to_string(model_id),
        };
        let body = json_stringify(&JsonValue::Object(shape_codec::serialize_struct(
            smithy_schema::REQUEST,
            false,
            input,
        )));

        let mut response = client::send(SendRequest {
            model: self.model,
            model_id,
            config: &config,
            body,
            custom_headers: custom_headers.as_ref(),
            on_response: self.options.stream.request.on_response.as_ref(),
            signal: self.options.stream.request.signal.as_ref(),
        })
        .await?;
        self.response_request_id = normalize_diagnostic_value(response.request_id.as_deref());

        while let Some(item) = response.next_item().await? {
            if let Some(on_event) = &self.options.stream.on_provider_stream_event {
                on_event(&item.to_json(), self.model).await?;
            }
            let data = match item.value {
                StreamValue::Exception(error, _) => match item.member.as_str() {
                    "internalServerException"
                    | "modelStreamErrorException"
                    | "validationException"
                    | "throttlingException"
                    | "serviceUnavailableException" => {
                        return Err(BedrockFailure::Sdk(error));
                    }
                    _ => continue,
                },
                StreamValue::Data(data) => data,
            };
            if !truthy(&data) {
                continue;
            }
            let empty = JsonObject::new();
            let event = data.as_object().unwrap_or(&empty);
            match item.member.as_str() {
                "messageStart" => {
                    if event.get("role").and_then(JsonValue::as_str) != Some("assistant") {
                        return Err(error(
                            "Unexpected assistant message start but got user message start instead",
                        ));
                    }
                    self.target.push(AssistantMessageEvent::Start {
                        partial: self.output.clone(),
                    });
                }
                "contentBlockStart" => {
                    self.blocks
                        .handle_content_block_start(event, &mut self.output, self.target);
                }
                "contentBlockDelta" => {
                    self.blocks
                        .handle_content_block_delta(event, &mut self.output, self.target);
                }
                "contentBlockStop" => {
                    self.blocks
                        .handle_content_block_stop(event, &mut self.output, self.target);
                }
                "messageStop" => {
                    let raw = event
                        .get("stopReason")
                        .filter(|reason| !reason.is_null())
                        .map(js_to_string);
                    let (stop_reason, error_message) = convert::map_stop_reason(raw.as_deref());
                    self.output.raw_stop_reason = raw;
                    self.output.stop_reason = stop_reason;
                    if let Some(message) = error_message {
                        self.output.error_message = Some(message);
                    }
                }
                "metadata" => handle_metadata(event, self.model, &mut self.output),
                // Exception members arrive as `StreamValue::Exception`.
                _ => {}
            }
        }

        if self.aborted() {
            return Err(error("Request was aborted"));
        }
        match self.output.stop_reason {
            StopReason::Pending => Err(error("Bedrock stream ended without a stop reason")),
            StopReason::Error | StopReason::Aborted => Err(error(
                self.output
                    .error_message
                    .clone()
                    .filter(|message| !message.is_empty())
                    .unwrap_or_else(|| "An unknown error occurred".to_owned()),
            )),
            StopReason::Stop => Ok(DoneReason::Stop),
            StopReason::Length => Ok(DoneReason::Length),
            StopReason::ToolUse => Ok(DoneReason::ToolUse),
            StopReason::Deferred => Ok(DoneReason::Deferred),
        }
    }
}

/// Stream a response through Bedrock `ConverseStream` (TS `stream`). Must be
/// called inside a tokio runtime.
#[must_use]
pub fn stream(
    model: &Model,
    context: &TranscriptContext,
    options: ProviderStreamOptions,
) -> AssistantMessageEventStream {
    let options = match BedrockOptions::from_provider_options(options) {
        Ok(options) => options,
        Err(thrown) => return lazy_stream(model, async move { Err(thrown) }),
    };
    // Bedrock has no mid-conversation system messages; fold them into the
    // leading prompt.
    let normalized_context = collapse_system_messages(context.clone());
    // eukhe addition: too many marked blocks fail before the request is built.
    if convert::supports_prompt_caching(model, options.stream.request.env.as_ref()) {
        if let Some(error_stream) = excess_breakpoints_error(model, normalized_context.messages()) {
            return error_stream;
        }
    }
    let target = AssistantMessageEventStream::new();
    let model = model.clone();
    let events = target.clone();
    tokio::spawn(async move {
        let mut run = StreamRun {
            model: &model,
            options: &options,
            output: create_output(&model),
            blocks: StreamBlocks::default(),
            target: &events,
            response_request_id: None,
        };
        let result = run.run(&normalized_context).await;
        let StreamRun {
            mut output,
            mut blocks,
            response_request_id,
            ..
        } = run;
        // A stream can settle without stopping every block, so finalize here.
        blocks.finalize(&mut output);
        match result {
            Ok(reason) => {
                events.push(AssistantMessageEvent::Done {
                    reason,
                    message: output,
                });
                events.end(None);
            }
            Err(failure) => {
                let aborted = options
                    .stream
                    .request
                    .signal
                    .as_ref()
                    .is_some_and(eukhe_chord::context::AbortSignal::aborted);
                let stop_reason_failure = (output.stop_reason == StopReason::Error)
                    .then(|| output.raw_stop_reason.clone())
                    .flatten();
                let reason = if aborted {
                    ErrorReason::Aborted
                } else {
                    ErrorReason::Error
                };
                output.stop_reason = reason.into();
                let error_message = format_bedrock_error(&failure);
                output.error_message = Some(error_message.clone());
                if reason == ErrorReason::Error {
                    append_bedrock_failure_diagnostic(
                        &mut output,
                        &failure,
                        response_request_id.as_deref(),
                    );
                }
                // eukhe addition: provider stream-failure diagnostics.
                let diagnostic_error = if aborted {
                    ProviderError::Aborted
                } else {
                    provider_error(
                        &failure,
                        &error_message,
                        stop_reason_failure.as_deref(),
                        response_request_id.as_deref(),
                    )
                };
                record_stream_failure(
                    (&model.provider, &model.id, &model.api),
                    &mut output,
                    &diagnostic_error,
                );
                events.push(AssistantMessageEvent::Error {
                    reason,
                    error: output,
                });
                events.end(None);
            }
        }
    });
    target
}

/// Maps provider-neutral [`SimpleStreamOptions`] to Bedrock options (TS
/// `streamSimple`). Must be called inside a tokio runtime.
#[must_use]
// The by-value options are the `StreamSimpleFn` signature.
#[allow(clippy::needless_pass_by_value)]
pub fn stream_simple(
    model: &Model,
    context: &TranscriptContext,
    options: SimpleStreamOptions,
) -> AssistantMessageEventStream {
    let mut base = build_base_options(model, context, Some(&options), None);
    let mut extra = JsonObject::new();
    if let Some(tool_choice) = options.tool_choice {
        let tool_choice = match tool_choice {
            ToolChoice::Auto => "auto",
            ToolChoice::None => "none",
        };
        extra.insert("toolChoice".to_owned(), tool_choice.into());
    }
    let Some(reasoning) = options.reasoning else {
        return stream(
            model,
            context,
            ProviderStreamOptions {
                stream: base,
                extra,
            },
        );
    };
    extra.insert(
        "reasoning".to_owned(),
        serde_json::to_value(reasoning).unwrap_or(JsonValue::Null),
    );

    let mut thinking_budgets = options.thinking_budgets.clone();
    if convert::is_anthropic_claude_model(model)
        && !convert::supports_adaptive_thinking(&model.id, &model.name)
    {
        // `None` means the caller did not request an output cap; the helper
        // uses the model cap.
        let adjusted = adjust_max_tokens_for_thinking(
            base.max_tokens,
            model.max_tokens,
            reasoning,
            options.thinking_budgets.as_ref(),
        );
        let max_tokens = clamp_max_tokens_to_context(model, context, adjusted.max_tokens);
        base.max_tokens = Some(max_tokens);
        let budget = adjusted
            .thinking_budget
            .min(max_tokens.saturating_sub(1024));
        let mut budgets = thinking_budgets.take().unwrap_or_default();
        match clamp_reasoning(Some(reasoning)) {
            Some(ThinkingLevel::Minimal) => budgets.minimal = Some(budget),
            Some(ThinkingLevel::Low) => budgets.low = Some(budget),
            Some(ThinkingLevel::Medium) => budgets.medium = Some(budget),
            Some(ThinkingLevel::High | ThinkingLevel::Xhigh | ThinkingLevel::Max) | None => {
                budgets.high = Some(budget);
            }
        }
        thinking_budgets = Some(budgets);
    }
    if let Some(budgets) = thinking_budgets {
        extra.insert(
            "thinkingBudgets".to_owned(),
            serde_json::to_value(budgets).unwrap_or(JsonValue::Null),
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

/// The `bedrock-converse-stream` API module (TS `bedrockProviderModule`).
#[must_use]
pub fn streams() -> ProviderStreams {
    ProviderStreams {
        stream: Arc::new(stream),
        stream_simple: Arc::new(stream_simple),
        fetch_deferred: None,
        cancel_deferred: None,
    }
}

#[cfg(test)]
mod tests {
    use super::client::SdkError;
    use super::*;

    #[test]
    fn formats_service_exceptions_with_prefixes() {
        let mut error = SdkError::plain("ValidationException", "bad");
        error.service_exception = true;
        assert_eq!(
            format_bedrock_error(&BedrockFailure::Sdk(error)),
            "Validation error: bad"
        );
        let mut error = SdkError::plain("FooException", "data retention mode 'x'");
        error.service_exception = true;
        assert_eq!(
            format_bedrock_error(&BedrockFailure::Sdk(error)),
            format!("FooException: data retention mode 'x' See {BEDROCK_DATA_RETENTION_DOCS_URL} for supported data retention modes.")
        );
        assert_eq!(
            format_bedrock_error(&BedrockFailure::Sdk(SdkError::plain(
                "Error",
                "socket hang up"
            ))),
            "socket hang up"
        );
    }

    #[test]
    fn normalizes_diagnostic_values() {
        assert_eq!(
            normalize_diagnostic_value(Some("  id ")),
            Some("id".to_owned())
        );
        assert_eq!(normalize_diagnostic_value(Some("   ")), None);
        assert_eq!(normalize_diagnostic_value(Some(&"R".repeat(201))), None);
    }
}
