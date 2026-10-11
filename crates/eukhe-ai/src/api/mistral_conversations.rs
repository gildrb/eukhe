//! The `mistral-conversations` wire API: streaming responses from the native
//! Mistral Chat Completions endpoint. Port of `api/mistral-conversations.ts`.
//!
//! API-specific options (TS `MistralOptions`) arrive in
//! [`ProviderStreamOptions::extra`]: `toolChoice` (`"auto" | "none" | "any" |
//! "required" | { type: "function", function: { name } }`), `promptMode`
//! (`"reasoning"`), and `reasoningEffort` (`"none" | "low" | "medium" |
//! "high" | "max"`).

mod consume;
mod payload;
mod transport;

use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::Arc;

use eukhe_types::pi_ai::{
    AssistantMessage, AssistantMessageEvent, CacheRetention, DoneReason, ErrorReason, JsonValue,
    Model, ModelThinkingLevel, StopReason, ToolChoice, TranscriptContext, Usage,
};

use super::lazy::lazy_stream;
use super::simple_options::build_base_options;
use super::transform_messages::transform_messages;
use super::ProviderStreams;
use crate::models::clamp_thinking_level;
use crate::types::{ProviderStreamOptions, SimpleStreamOptions, StreamOptions};
use crate::utils::diagnostics::{ErrorObject, Thrown, ThrownValue};
use crate::utils::error_body::{safe_json_stringify, truncate_error_text};
use crate::utils::event_stream::AssistantMessageEventStream;
use crate::utils::hash::short_hash;
use crate::utils::js::js_trim;
use crate::utils::now_ms;
use crate::utils::stream_failure::{
    record_stream_failure, stream_failure_from_stop_reason, ProviderError, ProviderHttpError,
};
use crate::utils::transcript::resolve_transcript;

const MISTRAL_TOOL_CALL_ID_LENGTH: usize = 9;
const MAX_MISTRAL_ERROR_BODY_CHARS: usize = 4000;

/// TS `MistralOptions`: the shared stream options plus the Mistral keys of
/// [`ProviderStreamOptions::extra`], kept as the JSON the caller passed.
#[derive(Clone, Default)]
struct MistralOptions {
    stream: StreamOptions,
    tool_choice: Option<JsonValue>,
    prompt_mode: Option<JsonValue>,
    reasoning_effort: Option<JsonValue>,
}

impl MistralOptions {
    fn from_provider_options(options: ProviderStreamOptions) -> Self {
        let ProviderStreamOptions { stream, mut extra } = options;
        Self {
            stream,
            tool_choice: extra.remove("toolChoice"),
            prompt_mode: extra.remove("promptMode"),
            reasoning_effort: extra.remove("reasoningEffort"),
        }
    }

    /// TS `shouldUsePromptCaching`: the session id when prompt caching applies.
    fn prompt_cache_session_id(&self) -> Option<&str> {
        if self.stream.cache_retention == Some(CacheRetention::None) {
            return None;
        }
        self.stream
            .session_id
            .as_deref()
            .filter(|id| !id.is_empty())
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

/// A thrown JS `TypeError`.
fn type_error(message: &str) -> Thrown {
    ErrorObject::named("TypeError", message).thrown()
}

/// A failure of one Mistral request.
enum MistralFailure {
    /// TS `MistralHttpError`: a non-2xx response.
    Http {
        status: u16,
        body: String,
        status_text: String,
        headers: HashMap<String, String>,
    },
    /// Any other thrown value.
    Thrown(Thrown),
}

impl From<Thrown> for MistralFailure {
    fn from(error: Thrown) -> Self {
        Self::Thrown(error)
    }
}

/// TS `new Error(message)`.
fn error(message: impl Into<String>) -> MistralFailure {
    MistralFailure::Thrown(ErrorObject::new(message).thrown())
}

/// TS `formatMistralError`.
fn format_mistral_error(failure: &MistralFailure) -> String {
    match failure {
        MistralFailure::Http {
            status,
            body,
            status_text,
            ..
        } => {
            let body_text = js_trim(body);
            if body_text.is_empty() {
                let message = if status_text.is_empty() {
                    format!("Request failed with status {status}")
                } else {
                    status_text.clone()
                };
                format!("Mistral API error ({status}): {message}")
            } else {
                format!(
                    "Mistral API error ({status}): {}",
                    truncate_error_text(body_text, MAX_MISTRAL_ERROR_BODY_CHARS)
                )
            }
        }
        MistralFailure::Thrown(thrown) => match thrown.downcast_ref::<ThrownValue>() {
            Some(ThrownValue(value)) => safe_json_stringify(value),
            None => thrown.to_string(),
        },
    }
}

/// eukhe addition: the classified failure behind the
/// `provider_stream_failure` diagnostic, recorded at the points the old
/// eukhe Mistral provider records it.
fn provider_error(failure: &MistralFailure, output: &AssistantMessage) -> ProviderError {
    match failure {
        MistralFailure::Http {
            status,
            body,
            headers,
            ..
        } => ProviderError::Http(ProviderHttpError {
            message: format_mistral_error(failure),
            status: Some(*status),
            body: Some(body.clone()),
            headers: headers.clone(),
            request_id: None,
            sdk_name: Some("MistralHttpError".to_owned()),
            retry_after_ms: None,
            provider_error_type: None,
        }),
        MistralFailure::Thrown(_)
            if output.raw_stop_reason.is_some()
                && matches!(output.stop_reason, StopReason::Error) =>
        {
            ProviderError::StreamFailure(stream_failure_from_stop_reason(
                output.raw_stop_reason.as_deref(),
                None,
            ))
        }
        MistralFailure::Thrown(_) => ProviderError::Message(format_mistral_error(failure)),
    }
}

/// TS `deriveMistralToolCallId`.
fn derive_mistral_tool_call_id(id: &str, attempt: u32) -> String {
    let normalized: String = id.chars().filter(char::is_ascii_alphanumeric).collect();
    if attempt == 0 && normalized.len() == MISTRAL_TOOL_CALL_ID_LENGTH {
        return normalized;
    }
    let seed_base = if normalized.is_empty() {
        id
    } else {
        &normalized
    };
    let seed = if attempt == 0 {
        seed_base.to_owned()
    } else {
        format!("{seed_base}:{attempt}")
    };
    short_hash(&seed)
        .chars()
        .filter(char::is_ascii_alphanumeric)
        .take(MISTRAL_TOOL_CALL_ID_LENGTH)
        .collect()
}

/// TS `createMistralToolCallIdNormalizer`: stable, collision-free 9-char ids.
#[derive(Default)]
struct ToolCallIdNormalizer {
    id_map: HashMap<String, String>,
    reverse_map: HashMap<String, String>,
}

impl ToolCallIdNormalizer {
    fn normalize(&mut self, id: &str) -> String {
        if let Some(existing) = self.id_map.get(id).filter(|existing| !existing.is_empty()) {
            return existing.clone();
        }
        let mut attempt = 0;
        loop {
            let candidate = derive_mistral_tool_call_id(id, attempt);
            let owner = self.reverse_map.get(&candidate);
            if owner.is_none_or(|owner| owner.is_empty() || owner == id) {
                self.id_map.insert(id.to_owned(), candidate.clone());
                self.reverse_map.insert(candidate.clone(), id.to_owned());
                return candidate;
            }
            attempt += 1;
        }
    }
}

/// TS `createOutput`.
fn create_output(model: &Model) -> AssistantMessage {
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
        duration_ms: None,
    }
}

/// The body of the TS `stream` task up to `done`.
async fn run_stream(
    model: &Model,
    context: &TranscriptContext,
    options: &MistralOptions,
    output: &mut AssistantMessage,
    stream: &AssistantMessageEventStream,
) -> Result<DoneReason, MistralFailure> {
    let Some(api_key) = options
        .stream
        .request
        .api_key
        .as_deref()
        .filter(|key| !key.is_empty())
    else {
        return Err(error(format!(
            "No API key for provider: {}",
            model.provider
        )));
    };
    let transformed_messages = {
        let normalizer = RefCell::new(ToolCallIdNormalizer::default());
        let normalize =
            |id: &str, _: &Model, _: &AssistantMessage| normalizer.borrow_mut().normalize(id);
        transform_messages(context.messages(), model, Some(&normalize))
    };

    let mut payload = JsonValue::Object(payload::build_chat_payload(
        model,
        context.messages(),
        &transformed_messages,
        options,
    )?);
    if let Some(on_payload) = &options.stream.request.on_payload {
        if let Some(next_payload) = on_payload(payload.clone(), model).await? {
            payload = next_payload;
        }
    }
    let wire_payload = JsonValue::Object(payload::to_mistral_wire_payload(&payload)?);
    let mut events =
        transport::request_mistral_stream(model, &wire_payload, api_key, options).await?;
    stream.push(AssistantMessageEvent::Start {
        partial: output.clone(),
    });
    consume::consume_chat_stream(
        model,
        output,
        stream,
        &mut events,
        options.stream.on_provider_stream_event.as_ref(),
    )
    .await?;

    if options
        .stream
        .request
        .signal
        .as_ref()
        .is_some_and(eukhe_chord::context::AbortSignal::aborted)
    {
        return Err(error("Request was aborted"));
    }
    match output.stop_reason {
        StopReason::Pending => Err(error("Mistral stream ended without a finish reason")),
        StopReason::Aborted | StopReason::Error => Err(error(
            output
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

/// Stream responses from the native Mistral Chat Completions endpoint (TS
/// `stream`). Must be called inside a tokio runtime.
#[must_use]
pub fn stream(
    model: &Model,
    context: &TranscriptContext,
    options: ProviderStreamOptions,
) -> AssistantMessageEventStream {
    let stream = AssistantMessageEventStream::new();
    let supports_mid_convo_system_messages = model
        .compat
        .as_ref()
        .and_then(|compat| compat.as_mistral_conversations())
        .and_then(|compat| compat.supports_mid_convo_system_messages);
    let normalized_context =
        resolve_transcript(context.clone(), supports_mid_convo_system_messages);
    let options = MistralOptions::from_provider_options(options);
    let model = model.clone();
    let target = stream.clone();
    tokio::spawn(async move {
        let mut output = create_output(&model);
        match run_stream(&model, &normalized_context, &options, &mut output, &target).await {
            Ok(reason) => {
                target.push(AssistantMessageEvent::Done {
                    reason,
                    message: output,
                });
                target.end(None);
            }
            Err(failure) => {
                let aborted = options
                    .stream
                    .request
                    .signal
                    .as_ref()
                    .is_some_and(eukhe_chord::context::AbortSignal::aborted);
                let diagnostic_error = provider_error(&failure, &output);
                let reason = if aborted {
                    ErrorReason::Aborted
                } else {
                    ErrorReason::Error
                };
                output.stop_reason = reason.into();
                output.error_message = Some(format_mistral_error(&failure));
                // eukhe addition: provider stream-failure diagnostics.
                record_stream_failure(
                    (&model.provider, &model.id, &model.api),
                    &mut output,
                    &diagnostic_error,
                );
                target.push(AssistantMessageEvent::Error {
                    reason,
                    error: output,
                });
                target.end(None);
            }
        }
    });
    stream
}

/// Maps provider-agnostic [`SimpleStreamOptions`] to Mistral options (TS
/// `streamSimple`). Must be called inside a tokio runtime.
#[must_use]
// The `StreamSimpleFn` contract passes options by value.
#[allow(clippy::needless_pass_by_value)]
pub fn stream_simple(
    model: &Model,
    context: &TranscriptContext,
    options: SimpleStreamOptions,
) -> AssistantMessageEventStream {
    let Some(api_key) = options
        .stream
        .request
        .api_key
        .clone()
        .filter(|key| !key.is_empty())
    else {
        // TS throws synchronously; the lazy API wrapper turns that into an
        // error stream, as here.
        let message = format!("No API key for provider: {}", model.provider);
        return lazy_stream(
            model,
            async move { Err(ErrorObject::new(message).thrown()) },
        );
    };

    let base = build_base_options(model, context, Some(&options), Some(&api_key));
    let mut extra = eukhe_types::pi_ai::JsonObject::new();
    if let Some(tool_choice) = options.tool_choice {
        let tool_choice = match tool_choice {
            ToolChoice::Auto => "auto",
            ToolChoice::None => "none",
        };
        extra.insert("toolChoice".into(), tool_choice.into());
    }
    let clamped_reasoning = options
        .reasoning
        .map(|reasoning| clamp_thinking_level(model, ModelThinkingLevel::from(reasoning)));
    let reasoning = clamped_reasoning.filter(|level| *level != ModelThinkingLevel::Off);
    // Models with a thinking level map use `reasoning_effort`; other
    // reasoning models use `prompt_mode`.
    let effort_map = model
        .thinking_level_map
        .as_ref()
        .filter(|_| model.reasoning);
    let reasoning_effort = effort_map.and_then(|map| match reasoning {
        Some(level) => Some(
            map.get(&level)
                .cloned()
                .flatten()
                .unwrap_or_else(|| "high".to_owned()),
        ),
        None => map.get(&ModelThinkingLevel::Off).cloned().flatten(),
    });
    if model.reasoning && effort_map.is_none() && reasoning.is_some() {
        extra.insert("promptMode".into(), "reasoning".into());
    }
    if let Some(effort) = reasoning_effort {
        extra.insert("reasoningEffort".into(), effort.into());
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

/// The `mistral-conversations` API module.
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
    use super::*;

    #[test]
    fn derives_nine_char_ids() {
        assert_eq!(derive_mistral_tool_call_id("abc123456", 0), "abc123456");
        assert_eq!(derive_mistral_tool_call_id("call_abc|123456", 0).len(), 9);
        let mut normalizer = ToolCallIdNormalizer::default();
        let first = normalizer.normalize("call|1");
        assert_eq!(normalizer.normalize("call|1"), first);
    }
}
