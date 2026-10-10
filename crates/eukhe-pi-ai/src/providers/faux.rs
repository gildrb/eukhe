//! Scripted in-process provider for tests. Port of `providers/faux.ts`.
//!
//! Responses are queued with [`FauxProviderHandle::set_responses`] and
//! streamed in token-sized chunks. Usage is estimated from the serialized
//! transcript (4 UTF-16 code units per token), with per-session prompt-cache
//! simulation. Deferred requests return a handle that
//! [`fetch_deferred`](crate::models::Models::fetch_deferred) resolves.
//!
//! Event `partial` values are snapshots at emission time; TS shares one live
//! object across events (a JS aliasing artifact with no Rust equivalent).

use std::collections::HashMap;
use std::fmt;
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};

use eukhe_chord::context::AbortSignal;
use eukhe_types::pi_ai::{
    AnyModel, AssistantContentBlock, AssistantMessage, AssistantMessageEvent, CacheRetention,
    DeferredHandle, DoneReason, ErrorReason, JsonObject, JsonValue, Message, Modality, Model,
    ModelCost, ModelInputLimits, ProviderResponse, StopReason, TextContent, ThinkingContent,
    ToolCall, TranscriptContext, Usage, UserContent, UserContentBlock,
};
use futures::future::BoxFuture;

use crate::api::{ProviderStreams, StreamFn, StreamSimpleFn};
use crate::auth::{ApiKeyAuth, ApiKeyResolveInput, AuthResult, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};
use crate::types::{
    DeferredCancelOptions, DeferredFetchOptions, DeferredRequest, DeferredWindow,
    ProviderRequestOptions, ProviderStreamOptions, SimpleStreamOptions, StreamOptions,
};
use crate::utils::diagnostics::{ErrorObject, Thrown};
use crate::utils::event_stream::AssistantMessageEventStream;
use crate::utils::js::utf16_len;
use crate::utils::now_ms;
use crate::utils::sleep::timer_duration;
use crate::utils::text::get_system_message_text;

const DEFAULT_API: &str = "faux";
const DEFAULT_PROVIDER: &str = "faux";
const DEFAULT_MODEL_ID: &str = "faux-1";
const DEFAULT_MODEL_NAME: &str = "Faux Model";
const DEFAULT_BASE_URL: &str = "http://localhost:0";
const DEFAULT_MIN_TOKEN_SIZE: u64 = 3;
const DEFAULT_MAX_TOKEN_SIZE: u64 = 5;

/// One faux model: TS `FauxModelDefinition`.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct FauxModelDefinition {
    pub id: String,
    pub name: Option<String>,
    pub reasoning: Option<bool>,
    pub input: Option<Vec<Modality>>,
    pub input_limits: Option<ModelInputLimits>,
    /// `{ input, output, cacheRead, cacheWrite }`; tiers are ignored.
    pub cost: Option<ModelCost>,
    pub context_window: Option<u64>,
    pub max_tokens: Option<u64>,
}

impl FauxModelDefinition {
    /// A definition with only an id.
    #[must_use]
    pub fn new(id: impl Into<String>) -> Self {
        Self {
            id: id.into(),
            ..Self::default()
        }
    }
}

/// TS `FauxContentBlock = TextContent | ThinkingContent | ToolCall`.
pub type FauxContentBlock = AssistantContentBlock;

/// TS `fauxText()`.
#[must_use]
pub fn faux_text(text: impl Into<String>) -> FauxContentBlock {
    AssistantContentBlock::Text(TextContent::new(text))
}

/// TS `fauxThinking()`.
#[must_use]
pub fn faux_thinking(thinking: impl Into<String>) -> FauxContentBlock {
    AssistantContentBlock::Thinking(ThinkingContent {
        thinking: thinking.into(),
        thinking_signature: None,
        redacted: None,
    })
}

/// TS `fauxToolCall()`: a random id unless `id` is given.
#[must_use]
pub fn faux_tool_call(
    name: impl Into<String>,
    arguments: JsonObject,
    id: Option<String>,
) -> FauxContentBlock {
    AssistantContentBlock::ToolCall(ToolCall {
        id: id.unwrap_or_else(|| random_id("tool")),
        name: name.into(),
        arguments,
        thought_signature: None,
        namespace: None,
    })
}

/// Content accepted by [`faux_assistant_message`]: a string, one block, or
/// several blocks.
#[derive(Debug, Clone, PartialEq)]
pub enum FauxContent {
    Text(String),
    Block(FauxContentBlock),
    Blocks(Vec<FauxContentBlock>),
}

impl From<&str> for FauxContent {
    fn from(text: &str) -> Self {
        Self::Text(text.to_owned())
    }
}

impl From<String> for FauxContent {
    fn from(text: String) -> Self {
        Self::Text(text)
    }
}

impl From<FauxContentBlock> for FauxContent {
    fn from(block: FauxContentBlock) -> Self {
        Self::Block(block)
    }
}

impl From<Vec<FauxContentBlock>> for FauxContent {
    fn from(blocks: Vec<FauxContentBlock>) -> Self {
        Self::Blocks(blocks)
    }
}

fn normalize_faux_assistant_content(content: FauxContent) -> Vec<FauxContentBlock> {
    match content {
        FauxContent::Text(text) => vec![faux_text(text)],
        FauxContent::Block(block) => vec![block],
        FauxContent::Blocks(blocks) => blocks,
    }
}

/// Options of [`faux_assistant_message`].
#[derive(Debug, Clone, Default, PartialEq)]
pub struct FauxAssistantMessageOptions {
    /// Default: `stop`.
    pub stop_reason: Option<StopReason>,
    pub deferred: Option<DeferredHandle>,
    pub error_message: Option<String>,
    pub response_id: Option<String>,
    /// Default: now.
    pub timestamp: Option<u64>,
}

/// TS `fauxAssistantMessage()`.
#[must_use]
pub fn faux_assistant_message(
    content: impl Into<FauxContent>,
    options: FauxAssistantMessageOptions,
) -> AssistantMessage {
    AssistantMessage {
        content: normalize_faux_assistant_content(content.into()),
        api: DEFAULT_API.to_owned(),
        provider: DEFAULT_PROVIDER.to_owned(),
        model: DEFAULT_MODEL_ID.to_owned(),
        response_model: None,
        response_id: options.response_id,
        provider_thinking_level: None,
        thinking_level: None,
        diagnostics: None,
        usage: Usage::default(),
        stop_reason: options.stop_reason.unwrap_or(StopReason::Stop),
        deferred: options.deferred,
        error_message: options.error_message,
        raw_stop_reason: None,
        end_turn: None,
        timestamp: options.timestamp.unwrap_or_else(now_ms),
        duration_ms: None,
    }
}

/// Call counters of a faux provider: TS `FauxProviderState`.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct FauxProviderState {
    pub call_count: u64,
    pub deferred_fetch_count: u64,
    pub cancelled_deferred: Vec<DeferredHandle>,
}

/// Builds a response from the request: TS `FauxResponseFactory`. Receives a
/// snapshot of the provider state.
pub type FauxResponseFactory = Arc<
    dyn Fn(
            &TranscriptContext,
            Option<&SimpleStreamOptions>,
            &FauxProviderState,
            &Model,
        ) -> BoxFuture<'static, Result<AssistantMessage, Thrown>>
        + Send
        + Sync,
>;

/// One queued response: TS `FauxResponseStep`.
#[derive(Clone)]
pub enum FauxResponseStep {
    Message(Box<AssistantMessage>),
    Factory(FauxResponseFactory),
}

impl FauxResponseStep {
    /// A synchronous factory step.
    pub fn factory<F>(factory: F) -> Self
    where
        F: Fn(
                &TranscriptContext,
                Option<&SimpleStreamOptions>,
                &FauxProviderState,
                &Model,
            ) -> Result<AssistantMessage, Thrown>
            + Send
            + Sync
            + 'static,
    {
        Self::Factory(Arc::new(move |context, options, state, model| {
            let result = factory(context, options, state, model);
            Box::pin(async move { result })
        }))
    }
}

impl From<AssistantMessage> for FauxResponseStep {
    fn from(message: AssistantMessage) -> Self {
        Self::Message(Box::new(message))
    }
}

impl fmt::Debug for FauxResponseStep {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Message(message) => formatter.debug_tuple("Message").field(message).finish(),
            Self::Factory(_) => formatter.write_str("Factory"),
        }
    }
}

/// Deferred-response behavior of [`RegisterFauxProviderOptions`].
#[derive(Debug, Clone, Default, PartialEq)]
pub struct FauxDeferredOptions {
    /// Number of fetches that return the original handle before the scripted
    /// response becomes ready.
    pub pending_fetches: Option<f64>,
    pub poll_after_ms: Option<f64>,
}

/// Token chunk sizes of streamed deltas.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct FauxTokenSize {
    pub min: Option<u64>,
    pub max: Option<u64>,
}

/// Options of [`faux_provider`]: TS `RegisterFauxProviderOptions`.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct RegisterFauxProviderOptions {
    pub api: Option<String>,
    pub provider: Option<String>,
    pub models: Option<Vec<FauxModelDefinition>>,
    pub deferred: Option<FauxDeferredOptions>,
    pub tokens_per_second: Option<f64>,
    pub token_size: Option<FauxTokenSize>,
}

/// `Math.random().toString(36).slice(2)`-style random base-36 digits.
pub(crate) fn random_base36() -> String {
    let mut value: u64 = rand::random();
    let mut digits = Vec::new();
    while value > 0 {
        let digit = u32::try_from(value % 36).unwrap_or_default();
        digits.extend(char::from_digit(digit, 36));
        value /= 36;
    }
    digits.iter().rev().collect()
}

fn random_id(prefix: &str) -> String {
    format!("{prefix}:{}:{}", now_ms(), random_base36())
}

/// `Math.random()`: a uniform double in `[0, 1)`.
fn random_unit() -> f64 {
    rand::random()
}

/// `Math.ceil(length / 4)` over a UTF-16 length.
fn estimate_tokens_from_units(units: usize) -> u64 {
    u64::try_from(units.div_ceil(4)).unwrap_or(u64::MAX)
}

fn estimate_tokens(text: &str) -> u64 {
    estimate_tokens_from_units(utf16_len(text))
}

/// JS `JSON.stringify` of a serializable value.
fn json_stringify<T: serde::Serialize>(value: &T) -> String {
    serde_json::to_value(value)
        .map(|value| crate::utils::js::json_stringify(&value))
        .unwrap_or_default()
}

fn user_block_to_text(block: &UserContentBlock) -> String {
    match block {
        UserContentBlock::Text(text) => text.text.clone(),
        UserContentBlock::Image(image) => {
            format!("[image:{}:{}]", image.mime_type, utf16_len(&image.data))
        }
    }
}

fn content_to_text(content: &UserContent) -> String {
    match content {
        UserContent::Text(text) => text.clone(),
        UserContent::Blocks(blocks) => blocks
            .iter()
            .map(user_block_to_text)
            .collect::<Vec<_>>()
            .join("\n"),
    }
}

fn assistant_content_to_text(content: &[AssistantContentBlock]) -> String {
    content
        .iter()
        .map(|block| match block {
            AssistantContentBlock::Text(text) => text.text.clone(),
            AssistantContentBlock::Thinking(thinking) => thinking.thinking.clone(),
            AssistantContentBlock::ToolCall(call) => {
                format!("{}:{}", call.name, json_stringify(&call.arguments))
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn message_to_text(message: &Message) -> String {
    match message {
        Message::System(system) => {
            let mut parts = vec![get_system_message_text(system)];
            parts.extend(
                system
                    .tools_removed
                    .iter()
                    .flatten()
                    .map(|tool| format!("tool-:{}", json_stringify(tool))),
            );
            parts.extend(
                system
                    .tools_added
                    .iter()
                    .flatten()
                    .map(|tool| format!("tool+:{}", json_stringify(tool))),
            );
            parts
                .into_iter()
                .filter(|part| !part.is_empty())
                .collect::<Vec<_>>()
                .join("\n")
        }
        Message::User(user) => content_to_text(&user.content),
        Message::Assistant(assistant) => assistant_content_to_text(&assistant.content),
        Message::ToolResult(result) => std::iter::once(result.tool_name.clone())
            .chain(result.content.iter().map(user_block_to_text))
            .collect::<Vec<_>>()
            .join("\n"),
    }
}

/// One UTF-16 prompt text per message; the whole prompt joins them with blank lines.
type PromptMessages = Vec<Vec<u16>>;

/// `"\n\n"` in UTF-16.
const BLANK_LINE: [u16; 2] = [0x0A, 0x0A];

/// Length of the prompt text that joins the first `count` of `messages` with blank lines.
fn joined_length(messages: &[Vec<u16>], count: usize) -> usize {
    let separators = count.saturating_sub(1) * BLANK_LINE.len();
    separators + messages[..count].iter().map(Vec::len).sum::<usize>()
}

/// Common prefix length in UTF-16 code units.
fn common_prefix_length(a: &[u16], b: &[u16]) -> usize {
    a.iter()
        .zip(b)
        .take_while(|(left, right)| left == right)
        .count()
}

/// Length of the common prefix of the two joined prompts. Equal messages are compared whole; characters are compared
/// only from the first message that differs.
fn common_prompt_prefix_length(previous: &[Vec<u16>], current: &[Vec<u16>]) -> usize {
    let index = previous
        .iter()
        .zip(current)
        .take_while(|(left, right)| left == right)
        .count();
    let rest = |messages: &[Vec<u16>]| -> Vec<u16> {
        if index == messages.len() {
            return Vec::new();
        }
        let mut text = Vec::new();
        if index > 0 {
            text.extend_from_slice(&BLANK_LINE);
        }
        for (offset, message) in messages[index..].iter().enumerate() {
            if offset > 0 {
                text.extend_from_slice(&BLANK_LINE);
            }
            text.extend_from_slice(message);
        }
        text
    };
    joined_length(previous, index) + common_prefix_length(&rest(previous), &rest(current))
}

fn with_usage_estimate(
    mut message: AssistantMessage,
    context: &TranscriptContext,
    options: Option<&StreamOptions>,
    prompt_cache: &Mutex<HashMap<String, PromptMessages>>,
) -> AssistantMessage {
    // One text per message; the whole prompt joins them with blank lines.
    let prompt: PromptMessages = context
        .messages()
        .iter()
        .map(|message| {
            format!("{}:{}", message.role(), message_to_text(message))
                .encode_utf16()
                .collect()
        })
        .collect();
    let prompt_length = joined_length(&prompt, prompt.len());
    let prompt_tokens = estimate_tokens_from_units(prompt_length);
    let output_tokens = estimate_tokens(&assistant_content_to_text(&message.content));
    let mut input = prompt_tokens;
    let mut cache_read = 0;
    let mut cache_write = 0;
    let session_id = options
        .and_then(|options| options.session_id.clone())
        .filter(|id| !id.is_empty());

    if let Some(session_id) = session_id {
        if options.and_then(|options| options.cache_retention) != Some(CacheRetention::None) {
            let mut cache = prompt_cache.lock().unwrap_or_else(PoisonError::into_inner);
            match cache.get(&session_id) {
                Some(previous_prompt) => {
                    let cached_units = common_prompt_prefix_length(previous_prompt, &prompt);
                    cache_read = estimate_tokens_from_units(cached_units);
                    cache_write = estimate_tokens_from_units(prompt_length - cached_units);
                    input = prompt_tokens.saturating_sub(cache_read);
                }
                None => cache_write = prompt_tokens,
            }
            cache.insert(session_id, prompt);
        }
    }

    message.usage = Usage {
        input,
        output: output_tokens,
        cache_read,
        cache_write,
        total_tokens: input + output_tokens + cache_read + cache_write,
        ..Usage::default()
    };
    message
}

/// Splits `text` into chunks of `token_size * 4` UTF-16 code units, never
/// inside a character.
fn split_string_by_token_size(text: &str, min_token_size: u64, max_token_size: u64) -> Vec<String> {
    let mut chunks = Vec::new();
    let mut rest = text;
    while !rest.is_empty() {
        let span = max_token_size - min_token_size + 1;
        #[allow(
            clippy::cast_possible_truncation,
            clippy::cast_sign_loss,
            clippy::cast_precision_loss
        )]
        let token_size = min_token_size + (random_unit() * span as f64).floor() as u64;
        let char_size = usize::try_from((token_size * 4).max(1)).unwrap_or(usize::MAX);
        let mut units = 0;
        let mut end = rest.len();
        for (index, character) in rest.char_indices() {
            if units >= char_size {
                end = index;
                break;
            }
            units += character.len_utf16();
        }
        chunks.push(rest[..end].to_owned());
        rest = &rest[end..];
    }
    if chunks.is_empty() {
        chunks.push(String::new());
    }
    chunks
}

fn clone_message(
    message: &AssistantMessage,
    api: &str,
    provider: &str,
    model_id: &str,
) -> AssistantMessage {
    AssistantMessage {
        api: api.to_owned(),
        provider: provider.to_owned(),
        model: model_id.to_owned(),
        ..message.clone()
    }
}

fn base_message(
    api: &str,
    provider: &str,
    model_id: &str,
    stop_reason: StopReason,
) -> AssistantMessage {
    AssistantMessage {
        content: Vec::new(),
        api: api.to_owned(),
        provider: provider.to_owned(),
        model: model_id.to_owned(),
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

fn create_deferred_message(model: &Model, handle: &DeferredHandle) -> AssistantMessage {
    AssistantMessage {
        deferred: Some(handle.clone()),
        ..base_message(&model.api, &model.provider, &model.id, StopReason::Deferred)
    }
}

fn create_error_message(
    error: &Thrown,
    api: &str,
    provider: &str,
    model_id: &str,
) -> AssistantMessage {
    AssistantMessage {
        error_message: Some(error.to_string()),
        ..base_message(api, provider, model_id, StopReason::Error)
    }
}

fn create_aborted_message(partial: &AssistantMessage) -> AssistantMessage {
    AssistantMessage {
        stop_reason: StopReason::Aborted,
        error_message: Some("Request was aborted".to_owned()),
        timestamp: now_ms(),
        ..partial.clone()
    }
}

async fn schedule_chunk(chunk: &str, tokens_per_second: Option<f64>) {
    match tokens_per_second.filter(|rate| *rate > 0.0) {
        None => tokio::task::yield_now().await,
        Some(rate) => {
            #[allow(clippy::cast_precision_loss)] // Token estimates are far below 2^53.
            let delay_ms = (estimate_tokens(chunk) as f64 / rate) * 1000.0;
            tokio::time::sleep(timer_duration(delay_ms)).await;
        }
    }
}

/// Chunked streaming parameters.
#[derive(Clone, Copy)]
struct Pacing {
    min_token_size: u64,
    max_token_size: u64,
    tokens_per_second: Option<f64>,
}

fn aborted(signal: Option<&AbortSignal>) -> bool {
    signal.is_some_and(AbortSignal::aborted)
}

fn end_aborted(stream: &AssistantMessageEventStream, partial: &AssistantMessage) {
    let message = create_aborted_message(partial);
    stream.push(AssistantMessageEvent::Error {
        reason: ErrorReason::Aborted,
        error: message.clone(),
    });
    stream.end(Some(message));
}

/// The faux "pending stop reason" failure.
#[derive(Debug, Clone, Copy, thiserror::Error)]
#[error("Faux response ended without a stop reason")]
struct MissingStopReason;

#[allow(clippy::too_many_lines)] // One block-by-block emission loop, as in TS.
async fn stream_with_deltas(
    stream: &AssistantMessageEventStream,
    message: AssistantMessage,
    pacing: Pacing,
    signal: Option<&AbortSignal>,
) -> Result<(), Thrown> {
    let mut partial = AssistantMessage {
        content: Vec::new(),
        stop_reason: StopReason::Pending,
        ..message.clone()
    };
    if aborted(signal) {
        end_aborted(stream, &partial);
        return Ok(());
    }

    stream.push(AssistantMessageEvent::Start {
        partial: partial.clone(),
    });

    for (index, block) in message.content.iter().enumerate() {
        if aborted(signal) {
            end_aborted(stream, &partial);
            return Ok(());
        }
        match block {
            AssistantContentBlock::Thinking(thinking) => {
                partial.content.push(faux_thinking(""));
                stream.push(AssistantMessageEvent::ThinkingStart {
                    content_index: index,
                    partial: partial.clone(),
                });
                for chunk in split_string_by_token_size(
                    &thinking.thinking,
                    pacing.min_token_size,
                    pacing.max_token_size,
                ) {
                    schedule_chunk(&chunk, pacing.tokens_per_second).await;
                    if aborted(signal) {
                        end_aborted(stream, &partial);
                        return Ok(());
                    }
                    if let Some(AssistantContentBlock::Thinking(current)) =
                        partial.content.get_mut(index)
                    {
                        current.thinking.push_str(&chunk);
                    }
                    stream.push(AssistantMessageEvent::ThinkingDelta {
                        content_index: index,
                        delta: chunk,
                        partial: partial.clone(),
                    });
                }
                stream.push(AssistantMessageEvent::ThinkingEnd {
                    content_index: index,
                    content: thinking.thinking.clone(),
                    partial: partial.clone(),
                });
            }
            AssistantContentBlock::Text(text) => {
                partial.content.push(faux_text(""));
                stream.push(AssistantMessageEvent::TextStart {
                    content_index: index,
                    partial: partial.clone(),
                });
                for chunk in split_string_by_token_size(
                    &text.text,
                    pacing.min_token_size,
                    pacing.max_token_size,
                ) {
                    schedule_chunk(&chunk, pacing.tokens_per_second).await;
                    if aborted(signal) {
                        end_aborted(stream, &partial);
                        return Ok(());
                    }
                    if let Some(AssistantContentBlock::Text(current)) =
                        partial.content.get_mut(index)
                    {
                        current.text.push_str(&chunk);
                    }
                    stream.push(AssistantMessageEvent::TextDelta {
                        content_index: index,
                        delta: chunk,
                        partial: partial.clone(),
                    });
                }
                stream.push(AssistantMessageEvent::TextEnd {
                    content_index: index,
                    content: text.text.clone(),
                    partial: partial.clone(),
                });
            }
            AssistantContentBlock::ToolCall(call) => {
                partial
                    .content
                    .push(AssistantContentBlock::ToolCall(ToolCall {
                        id: call.id.clone(),
                        name: call.name.clone(),
                        arguments: JsonObject::new(),
                        thought_signature: None,
                        namespace: None,
                    }));
                stream.push(AssistantMessageEvent::ToolCallStart {
                    content_index: index,
                    partial: partial.clone(),
                });
                for chunk in split_string_by_token_size(
                    &json_stringify(&call.arguments),
                    pacing.min_token_size,
                    pacing.max_token_size,
                ) {
                    schedule_chunk(&chunk, pacing.tokens_per_second).await;
                    if aborted(signal) {
                        end_aborted(stream, &partial);
                        return Ok(());
                    }
                    stream.push(AssistantMessageEvent::ToolCallDelta {
                        content_index: index,
                        delta: chunk,
                        partial: partial.clone(),
                    });
                }
                if let Some(AssistantContentBlock::ToolCall(current)) =
                    partial.content.get_mut(index)
                {
                    current.arguments.clone_from(&call.arguments);
                }
                stream.push(AssistantMessageEvent::ToolCallEnd {
                    content_index: index,
                    tool_call: call.clone(),
                    partial: partial.clone(),
                });
            }
        }
    }

    let done_reason = match message.stop_reason {
        StopReason::Pending => return Err(Arc::new(MissingStopReason)),
        StopReason::Error | StopReason::Aborted => {
            let reason = if message.stop_reason == StopReason::Error {
                ErrorReason::Error
            } else {
                ErrorReason::Aborted
            };
            stream.push(AssistantMessageEvent::Error {
                reason,
                error: message.clone(),
            });
            stream.end(Some(message));
            return Ok(());
        }
        StopReason::Stop => DoneReason::Stop,
        StopReason::Length => DoneReason::Length,
        StopReason::ToolUse => DoneReason::ToolUse,
        StopReason::Deferred => DoneReason::Deferred,
    };
    stream.push(AssistantMessageEvent::Done {
        reason: done_reason,
        message: message.clone(),
    });
    stream.end(Some(message));
    Ok(())
}

fn end_with_error(stream: &AssistantMessageEventStream, message: AssistantMessage) {
    stream.push(AssistantMessageEvent::Error {
        reason: ErrorReason::Error,
        error: message.clone(),
    });
    stream.end(Some(message));
}

struct DeferredEntry {
    handle: DeferredHandle,
    step: FauxResponseStep,
    context: TranscriptContext,
    options: Option<SimpleStreamOptions>,
    model: Model,
    pending_fetches: u64,
    cancelled: bool,
    final_message: Option<AssistantMessage>,
}

struct FauxCoreInner {
    api: String,
    provider: String,
    pacing: Pacing,
    deferred: Option<FauxDeferredOptions>,
    models: Vec<Model>,
    pending_responses: Mutex<Vec<FauxResponseStep>>,
    state: Mutex<FauxProviderState>,
    prompt_cache: Mutex<HashMap<String, PromptMessages>>,
    deferred_responses: Mutex<HashMap<String, DeferredEntry>>,
}

fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

fn status_ok() -> ProviderResponse {
    ProviderResponse {
        status: 200,
        headers: eukhe_types::pi_ai::IndexMap::new(),
    }
}

async fn notify_response(
    request: &ProviderRequestOptions<Model>,
    model: &Model,
) -> Result<(), Thrown> {
    match &request.on_response {
        Some(on_response) => on_response(status_ok(), model).await,
        None => Ok(()),
    }
}

/// TS truthiness of `options.deferred`.
fn wants_deferred(options: Option<&SimpleStreamOptions>) -> bool {
    matches!(
        options.and_then(|options| options.deferred),
        Some(DeferredRequest::Flag(true) | DeferredRequest::Window(_))
    )
}

/// The scripted core shared by [`faux_provider`] and the compat
/// registration: TS `createFauxCore()`.
#[derive(Clone)]
pub struct FauxCore {
    inner: Arc<FauxCoreInner>,
}

impl FauxCore {
    /// TS `createFauxCore()`.
    #[must_use]
    pub fn new(options: RegisterFauxProviderOptions) -> Self {
        let api = options.api.unwrap_or_else(|| random_id(DEFAULT_API));
        let provider = options
            .provider
            .unwrap_or_else(|| DEFAULT_PROVIDER.to_owned());
        let token_size = options.token_size.unwrap_or_default();
        let min_token_size = token_size
            .min
            .unwrap_or(DEFAULT_MIN_TOKEN_SIZE)
            .min(token_size.max.unwrap_or(DEFAULT_MAX_TOKEN_SIZE))
            .max(1);
        let max_token_size = min_token_size.max(token_size.max.unwrap_or(DEFAULT_MAX_TOKEN_SIZE));
        let definitions = options
            .models
            .filter(|models| !models.is_empty())
            .unwrap_or_else(|| {
                vec![FauxModelDefinition {
                    id: DEFAULT_MODEL_ID.to_owned(),
                    name: Some(DEFAULT_MODEL_NAME.to_owned()),
                    reasoning: Some(false),
                    input: Some(vec![Modality::Text, Modality::Image]),
                    input_limits: None,
                    cost: Some(ModelCost::default()),
                    context_window: Some(128_000),
                    max_tokens: Some(16_384),
                }]
            });
        let models = definitions
            .into_iter()
            .map(|definition| Model {
                name: definition.name.unwrap_or_else(|| definition.id.clone()),
                id: definition.id,
                api: api.clone(),
                provider: provider.clone(),
                base_url: DEFAULT_BASE_URL.to_owned(),
                input: definition
                    .input
                    .unwrap_or_else(|| vec![Modality::Text, Modality::Image]),
                input_limits: definition.input_limits,
                cost: definition.cost.unwrap_or_default(),
                headers: None,
                model_type: None,
                reasoning: definition.reasoning.unwrap_or(false),
                thinking_level_map: None,
                prompt_cache: None,
                context_window: definition.context_window.unwrap_or(128_000),
                max_tokens: definition.max_tokens.unwrap_or(16_384),
                sampling_params: None,
                sampling_params_by_thinking_level: None,
                compat: None,
                featured: None,
            })
            .collect();
        Self {
            inner: Arc::new(FauxCoreInner {
                api,
                provider,
                pacing: Pacing {
                    min_token_size,
                    max_token_size,
                    tokens_per_second: options.tokens_per_second,
                },
                deferred: options.deferred,
                models,
                pending_responses: Mutex::new(Vec::new()),
                state: Mutex::new(FauxProviderState::default()),
                prompt_cache: Mutex::new(HashMap::new()),
                deferred_responses: Mutex::new(HashMap::new()),
            }),
        }
    }

    /// The api id of the faux models.
    #[must_use]
    pub fn api(&self) -> &str {
        &self.inner.api
    }

    /// The provider id of the faux models.
    #[must_use]
    pub fn provider(&self) -> &str {
        &self.inner.provider
    }

    /// Every faux model (at least one).
    #[must_use]
    pub fn models(&self) -> &[Model] {
        &self.inner.models
    }

    /// The first model: TS `getModel()`.
    #[must_use]
    pub fn get_model(&self) -> Model {
        self.inner.models[0].clone()
    }

    /// The model with `model_id` (the first for an empty id): TS
    /// `getModel(modelId)`.
    #[must_use]
    pub fn get_model_by_id(&self, model_id: &str) -> Option<Model> {
        if model_id.is_empty() {
            return Some(self.get_model());
        }
        self.inner
            .models
            .iter()
            .find(|candidate| candidate.id == model_id)
            .cloned()
    }

    /// A snapshot of the call counters.
    #[must_use]
    pub fn state(&self) -> FauxProviderState {
        lock(&self.inner.state).clone()
    }

    /// Replaces the queued responses.
    pub fn set_responses(&self, responses: Vec<FauxResponseStep>) {
        *lock(&self.inner.pending_responses) = responses;
    }

    /// Appends queued responses.
    pub fn append_responses(&self, responses: Vec<FauxResponseStep>) {
        lock(&self.inner.pending_responses).extend(responses);
    }

    /// Number of queued responses.
    #[must_use]
    pub fn get_pending_response_count(&self) -> usize {
        lock(&self.inner.pending_responses).len()
    }

    async fn resolve_response(
        &self,
        step: &FauxResponseStep,
        context: &TranscriptContext,
        options: Option<&SimpleStreamOptions>,
        request_model: &Model,
    ) -> Result<AssistantMessage, Thrown> {
        let resolved = match step {
            FauxResponseStep::Message(message) => (**message).clone(),
            FauxResponseStep::Factory(factory) => {
                let state = self.state();
                factory(context, options, &state, request_model).await?
            }
        };
        Ok(with_usage_estimate(
            clone_message(
                &resolved,
                &self.inner.api,
                &self.inner.provider,
                &request_model.id,
            ),
            context,
            options.map(|options| &options.stream),
            &self.inner.prompt_cache,
        ))
    }

    async fn run_stream(
        &self,
        outer: &AssistantMessageEventStream,
        step: Option<FauxResponseStep>,
        request_model: &Model,
        context: TranscriptContext,
        options: Option<SimpleStreamOptions>,
    ) -> Result<(), Thrown> {
        if let Some(options) = &options {
            notify_response(&options.stream.request, request_model).await?;
        }
        let Some(step) = step else {
            let error = ErrorObject::new("No more faux responses queued").thrown();
            let message = with_usage_estimate(
                create_error_message(
                    &error,
                    &self.inner.api,
                    &self.inner.provider,
                    &request_model.id,
                ),
                &context,
                options.as_ref().map(|options| &options.stream),
                &self.inner.prompt_cache,
            );
            end_with_error(outer, message);
            return Ok(());
        };
        let signal = options
            .as_ref()
            .and_then(|options| options.stream.request.signal.clone());

        if wants_deferred(options.as_ref()) {
            let deferred_options = self.inner.deferred.clone().unwrap_or_default();
            let handle = DeferredHandle {
                provider: request_model.provider.clone(),
                model_id: request_model.id.clone(),
                api: request_model.api.clone(),
                id: random_id("deferred"),
                expires_at: None,
                poll_after_ms: deferred_options.poll_after_ms,
                data: None,
            };
            #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
            // Floored, non-negative.
            let pending_fetches = deferred_options
                .pending_fetches
                .unwrap_or(0.0)
                .floor()
                .max(0.0) as u64;
            lock(&self.inner.deferred_responses).insert(
                handle.id.clone(),
                DeferredEntry {
                    handle: handle.clone(),
                    step,
                    context,
                    options,
                    model: request_model.clone(),
                    pending_fetches,
                    cancelled: false,
                    final_message: None,
                },
            );
            return stream_with_deltas(
                outer,
                create_deferred_message(request_model, &handle),
                self.inner.pacing,
                signal.as_ref(),
            )
            .await;
        }

        let message = self
            .resolve_response(&step, &context, options.as_ref(), request_model)
            .await?;
        stream_with_deltas(outer, message, self.inner.pacing, signal.as_ref()).await
    }

    /// Streams the next queued response: TS `stream` / `streamSimple`.
    #[must_use]
    pub fn stream(
        &self,
        request_model: &Model,
        context: &TranscriptContext,
        options: Option<SimpleStreamOptions>,
    ) -> AssistantMessageEventStream {
        let outer = AssistantMessageEventStream::new();
        let step = {
            let mut pending = lock(&self.inner.pending_responses);
            (!pending.is_empty()).then(|| pending.remove(0))
        };
        lock(&self.inner.state).call_count += 1;

        let core = self.clone();
        let target = outer.clone();
        let request_model = request_model.clone();
        let context = context.clone();
        tokio::spawn(async move {
            if let Err(error) = core
                .run_stream(&target, step, &request_model, context, options)
                .await
            {
                end_with_error(
                    &target,
                    create_error_message(
                        &error,
                        &core.inner.api,
                        &core.inner.provider,
                        &request_model.id,
                    ),
                );
            }
        });
        outer
    }

    async fn run_fetch(
        &self,
        outer: &AssistantMessageEventStream,
        request_model: &Model,
        handle: &DeferredHandle,
        options: Option<DeferredFetchOptions>,
    ) -> Result<(), Thrown> {
        if let Some(options) = &options {
            notify_response(&options.request, request_model).await?;
        }
        let signal = options
            .as_ref()
            .and_then(|options| options.request.signal.clone());
        let unknown =
            || ErrorObject::new(format!("Unknown faux deferred response: {}", handle.id)).thrown();
        let (step, context, submission_options, model, pending_handle, final_message) = {
            let mut entries = lock(&self.inner.deferred_responses);
            let entry = entries.get_mut(&handle.id).ok_or_else(unknown)?;
            if entry.handle.provider != handle.provider
                || entry.handle.model_id != handle.model_id
                || entry.handle.api != handle.api
            {
                return Err(unknown());
            }
            if entry.cancelled {
                return Err(ErrorObject::new(format!(
                    "Faux deferred response was cancelled: {}",
                    handle.id
                ))
                .thrown());
            }
            let pending_handle = if entry.pending_fetches > 0 {
                entry.pending_fetches -= 1;
                Some(entry.handle.clone())
            } else {
                None
            };
            // `{ deferred, signal, onResponse, ...submissionOptions }`.
            let submission_options = entry.options.clone().map(|mut options| {
                options.deferred = None;
                options.stream.request.signal = None;
                options.stream.request.on_response = None;
                options
            });
            (
                entry.step.clone(),
                entry.context.clone(),
                submission_options,
                entry.model.clone(),
                pending_handle,
                entry.final_message.clone(),
            )
        };

        if let Some(pending_handle) = pending_handle {
            return stream_with_deltas(
                outer,
                create_deferred_message(request_model, &pending_handle),
                self.inner.pacing,
                signal.as_ref(),
            )
            .await;
        }

        let final_message = if let Some(message) = final_message {
            message
        } else {
            let message = match self
                .resolve_response(&step, &context, submission_options.as_ref(), &model)
                .await
            {
                Ok(message) => message,
                Err(error) => {
                    create_error_message(&error, &self.inner.api, &self.inner.provider, &model.id)
                }
            };
            if let Some(entry) = lock(&self.inner.deferred_responses).get_mut(&handle.id) {
                entry.final_message = Some(message.clone());
            }
            message
        };
        stream_with_deltas(outer, final_message, self.inner.pacing, signal.as_ref()).await
    }

    /// Resolves a deferred response: TS `fetchDeferred`.
    #[must_use]
    pub fn fetch_deferred(
        &self,
        request_model: &Model,
        handle: &DeferredHandle,
        options: Option<DeferredFetchOptions>,
    ) -> AssistantMessageEventStream {
        let outer = AssistantMessageEventStream::new();
        lock(&self.inner.state).deferred_fetch_count += 1;
        let core = self.clone();
        let target = outer.clone();
        let request_model = request_model.clone();
        let handle = handle.clone();
        tokio::spawn(async move {
            if let Err(error) = core
                .run_fetch(&target, &request_model, &handle, options)
                .await
            {
                end_with_error(
                    &target,
                    create_error_message(
                        &error,
                        &core.inner.api,
                        &core.inner.provider,
                        &request_model.id,
                    ),
                );
            }
        });
        outer
    }

    /// Records a cancellation: TS `cancelDeferred`.
    ///
    /// # Errors
    ///
    /// The `on_response` callback's failure.
    pub async fn cancel_deferred(
        &self,
        request_model: &Model,
        handle: &DeferredHandle,
        options: Option<DeferredCancelOptions>,
    ) -> Result<(), Thrown> {
        lock(&self.inner.state)
            .cancelled_deferred
            .push(handle.clone());
        if let Some(entry) = lock(&self.inner.deferred_responses).get_mut(&handle.id) {
            entry.cancelled = true;
        }
        match &options {
            Some(options) => notify_response(options, request_model).await,
            None => Ok(()),
        }
    }

    /// The core as [`ProviderStreams`].
    #[must_use]
    pub fn streams(&self) -> ProviderStreams {
        let stream_core = self.clone();
        let simple_core = self.clone();
        let fetch_core = self.clone();
        let cancel_core = self.clone();
        let stream: StreamFn = Arc::new(move |model, context, options| {
            stream_core.stream(model, context, Some(simple_from_provider_options(options)))
        });
        let stream_simple: StreamSimpleFn = Arc::new(move |model, context, options| {
            simple_core.stream(model, context, Some(options))
        });
        ProviderStreams {
            stream,
            stream_simple,
            fetch_deferred: Some(Arc::new(move |model, handle, options| {
                fetch_core.fetch_deferred(model, handle, Some(options))
            })),
            cancel_deferred: Some(Arc::new(move |model, handle, options| {
                let core = cancel_core.clone();
                let (model, handle) = (model.clone(), handle.clone());
                Box::pin(async move { core.cancel_deferred(&model, &handle, Some(options)).await })
            })),
        }
    }
}

/// Full stream options as the faux simple options: the `deferred` key of
/// the API-specific options keeps its TS truthiness.
fn simple_from_provider_options(options: ProviderStreamOptions) -> SimpleStreamOptions {
    let deferred = options.extra.get("deferred").and_then(|value| match value {
        JsonValue::Null => None,
        JsonValue::Bool(flag) => Some(DeferredRequest::Flag(*flag)),
        JsonValue::Object(object) => Some(DeferredRequest::Window(
            object
                .get("window")
                .and_then(JsonValue::as_str)
                .and_then(|window| match window {
                    "15m" => Some(DeferredWindow::Minutes15),
                    "1h" => Some(DeferredWindow::Hours1),
                    "24h" => Some(DeferredWindow::Hours24),
                    _ => None,
                }),
        )),
        JsonValue::Number(number) => Some(DeferredRequest::Flag(
            number
                .as_f64()
                .is_some_and(|number| number != 0.0 && !number.is_nan()),
        )),
        JsonValue::String(text) => Some(DeferredRequest::Flag(!text.is_empty())),
        JsonValue::Array(_) => Some(DeferredRequest::Flag(true)),
    });
    SimpleStreamOptions {
        stream: options.stream,
        deferred,
        ..SimpleStreamOptions::default()
    }
}

struct FauxAuth;

impl ApiKeyAuth for FauxAuth {
    // The trait returns a borrowed name; this one is a literal.
    #[allow(clippy::unnecessary_literal_bound)]
    fn name(&self) -> &str {
        "Faux"
    }

    fn resolve(
        &self,
        _input: ApiKeyResolveInput,
    ) -> BoxFuture<'_, Result<Option<AuthResult>, Thrown>> {
        Box::pin(async { Ok(Some(AuthResult::default())) })
    }
}

/// A faux provider for tests built on explicit `Models` collections: TS
/// `FauxProviderHandle`.
#[derive(Clone)]
pub struct FauxProviderHandle {
    pub provider: Provider,
    core: FauxCore,
}

impl FauxProviderHandle {
    #[must_use]
    pub fn api(&self) -> &str {
        self.core.api()
    }

    #[must_use]
    pub fn models(&self) -> &[Model] {
        self.core.models()
    }

    #[must_use]
    pub fn get_model(&self) -> Model {
        self.core.get_model()
    }

    #[must_use]
    pub fn get_model_by_id(&self, model_id: &str) -> Option<Model> {
        self.core.get_model_by_id(model_id)
    }

    #[must_use]
    pub fn state(&self) -> FauxProviderState {
        self.core.state()
    }

    pub fn set_responses(&self, responses: Vec<FauxResponseStep>) {
        self.core.set_responses(responses);
    }

    pub fn append_responses(&self, responses: Vec<FauxResponseStep>) {
        self.core.append_responses(responses);
    }

    #[must_use]
    pub fn get_pending_response_count(&self) -> usize {
        self.core.get_pending_response_count()
    }
}

/// Faux provider for tests built on explicit `Models` collections:
///
/// ```ignore
/// let faux = faux_provider(RegisterFauxProviderOptions::default());
/// let models = create_models(CreateModelsOptions::default());
/// models.set_provider(faux.provider.clone());
/// faux.set_responses(vec![faux_assistant_message("hi", Default::default()).into()]);
/// ```
#[must_use]
pub fn faux_provider(options: RegisterFauxProviderOptions) -> FauxProviderHandle {
    let core = FauxCore::new(options);
    let provider = build_provider(CreateProviderOptions {
        id: core.provider().to_owned(),
        auth: ProviderAuth {
            api_key: Some(Arc::new(FauxAuth)),
            oauth: None,
        },
        models: core.models().iter().cloned().map(AnyModel::Chat).collect(),
        api: Some(ProviderApi::Single(core.streams())),
        ..CreateProviderOptions::default()
    });
    FauxProviderHandle { provider, core }
}
