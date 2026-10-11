//! eukhe addition: the faux-script format on the faux provider.
//!
//! A faux script is the JSON verification seam shared by eukhe's print mode
//! (`EUKHE_FAUX_SCRIPT`), the daemon worker (`"engine": "faux"` create
//! configs and `childScript`), and the binary-level harnesses. It scripts a
//! faux model and its queued responses:
//!
//! ```json
//! {
//!   "modelId": "faux-1",
//!   "modelName": "Faux Model",
//!   "reasoning": false,
//!   "contextWindow": 128000,
//!   "maxTokens": 16384,
//!   "tokensPerSecond": 50,
//!   "repeatLastResponse": false,
//!   "responses": [
//!     "plain text",
//!     { "text": "text entry" },
//!     { "systemPrompt": true },
//!     {
//!       "content": [
//!         { "type": "thinking", "thinking": "..." },
//!         { "type": "text", "text": "..." },
//!         { "type": "toolCall", "name": "ipython", "arguments": { "code": "1" }, "id": "call-1" }
//!       ],
//!       "stopReason": "toolUse",
//!       "errorMessage": "...",
//!       "delayMs": 250
//!     }
//!   ]
//! }
//! ```
//!
//! The scripted provider registers under the stable identity `api: "faux"`,
//! `provider: "faux"` so fixtures can declare faux models in `models.json`.

use std::collections::VecDeque;
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};
use std::time::Duration;

use eukhe_types::pi_ai::{
    AssistantContentBlock, JsonObject, JsonValue, Message, Modality, Model, StopReason,
    TranscriptContext,
};

use super::faux::{
    faux_assistant_message, faux_provider, faux_text, faux_thinking, faux_tool_call,
    FauxAssistantMessageOptions, FauxContentBlock, FauxModelDefinition, FauxProviderHandle,
    FauxProviderState, FauxResponseStep, RegisterFauxProviderOptions,
};
use crate::models::{create_models, CreateModelsOptions, Models, Provider};
use crate::utils::text::get_system_message_text;

/// The api and provider id every scripted faux provider registers under.
const FAUX_SCRIPT_ID: &str = "faux";
const DEFAULT_MODEL_ID: &str = "faux-1";
const DEFAULT_MODEL_NAME: &str = "Faux Model";
const DEFAULT_CONTEXT_WINDOW: u64 = 128_000;
/// The registry faux model's request budget.
const DEFAULT_MAX_TOKENS: u64 = 16_384;

/// A parsed faux script: model definition plus queued response steps.
#[derive(Debug, Clone)]
pub struct FauxScript {
    pub model: FauxModelDefinition,
    /// Streaming pace; only positive rates are kept.
    pub tokens_per_second: Option<f64>,
    pub responses: Vec<FauxResponseStep>,
    /// The `repeatLastResponse` script key: once the queued responses run
    /// out, the provider re-serves the last one on every further call
    /// instead of erroring. Opt-in for harnesses whose flow keeps calling
    /// the model past the script's depth (an active goal's continuation
    /// churn); the default stays the finite response budget.
    pub repeat_last_response: bool,
}

/// A malformed faux script.
#[derive(Debug, thiserror::Error)]
pub enum FauxScriptError {
    #[error("invalid faux script JSON: {0}")]
    InvalidJson(#[from] serde_json::Error),
    #[error("the faux script must be a JSON object")]
    NotAnObject,
    #[error("the faux script responses must be an array")]
    ResponsesNotAnArray,
    #[error("a faux script response must be a string or object")]
    InvalidResponse,
    #[error("a faux script content block must be an object")]
    BlockNotAnObject,
    #[error("a faux script content block needs a type")]
    MissingBlockType,
    #[error("unknown faux script content type {0}")]
    UnknownBlockType(String),
    #[error("a thinking block needs thinking text")]
    MissingThinking,
    #[error("a text block needs text")]
    MissingText,
    #[error("a toolCall block needs a name")]
    MissingToolName,
    #[error("a toolCall block's arguments must be an object")]
    ToolArgumentsNotAnObject,
    #[error("unknown faux script stopReason {0}")]
    UnknownStopReason(String),
}

/// Parse a faux script from its JSON text.
///
/// # Errors
///
/// [`FauxScriptError::InvalidJson`] for unparsable text, otherwise the
/// errors of [`parse_faux_script_value`].
pub fn parse_faux_script(script: &str) -> Result<FauxScript, FauxScriptError> {
    parse_faux_script_value(&serde_json::from_str(script)?)
}

/// Parse a `{"responses": [...], "modelId": ..., "tokensPerSecond": ...,
/// "repeatLastResponse": ...}` script value.
///
/// Entry forms: a plain string, `{"text": "..."}`, `{"systemPrompt": true}`
/// (answers with the request's system prompt), or
/// `{"content": [{"type": "thinking"|"text"|"toolCall", ...}]}`. Object
/// entries may carry `stopReason` (default `toolUse` when the entry has a
/// tool call, else `stop`), `errorMessage`, and `delayMs` (holds the request
/// in flight before the first event; an abort during the hold ends the
/// stream aborted).
///
/// Entry objects whose `content` is not an array and whose `text` is not a
/// string (for example `{"content": 1}` or `{"text": 1}`) are empty text
/// responses, as in the original eukhe format.
///
/// # Errors
///
/// When the script is not a JSON object, `responses` is not an array, a
/// response entry is neither a string nor an object, a `content` block is
/// malformed, or `stopReason` is unknown.
pub fn parse_faux_script_value(script: &JsonValue) -> Result<FauxScript, FauxScriptError> {
    let object = script.as_object().ok_or(FauxScriptError::NotAnObject)?;
    let model = FauxModelDefinition {
        id: object
            .get("modelId")
            .and_then(JsonValue::as_str)
            .unwrap_or(DEFAULT_MODEL_ID)
            .to_owned(),
        name: Some(
            object
                .get("modelName")
                .and_then(JsonValue::as_str)
                .unwrap_or(DEFAULT_MODEL_NAME)
                .to_owned(),
        ),
        reasoning: Some(
            object
                .get("reasoning")
                .and_then(JsonValue::as_bool)
                .unwrap_or(false),
        ),
        input: Some(vec![Modality::Text, Modality::Image]),
        input_limits: None,
        cost: None,
        context_window: Some(
            object
                .get("contextWindow")
                .and_then(JsonValue::as_u64)
                .unwrap_or(DEFAULT_CONTEXT_WINDOW),
        ),
        max_tokens: Some(
            object
                .get("maxTokens")
                .and_then(JsonValue::as_u64)
                .unwrap_or(DEFAULT_MAX_TOKENS),
        ),
    };
    let tokens_per_second = object
        .get("tokensPerSecond")
        .and_then(JsonValue::as_f64)
        .filter(|rate| *rate > 0.0);
    let responses = match object.get("responses") {
        None => Vec::new(),
        Some(JsonValue::Array(entries)) => entries
            .iter()
            .map(parse_script_step)
            .collect::<Result<Vec<_>, _>>()?,
        Some(_) => return Err(FauxScriptError::ResponsesNotAnArray),
    };
    let repeat_last_response = object
        .get("repeatLastResponse")
        .and_then(JsonValue::as_bool)
        .unwrap_or(false);
    Ok(FauxScript {
        model,
        tokens_per_second,
        responses,
        repeat_last_response,
    })
}

/// Where a scripted response's content comes from.
#[derive(Clone)]
enum ScriptedContent {
    Blocks(Vec<FauxContentBlock>),
    /// `{"systemPrompt": true}`: the request's system prompt as text.
    SystemPromptEcho,
}

impl ScriptedContent {
    fn has_tool_call(&self) -> bool {
        match self {
            Self::Blocks(blocks) => blocks
                .iter()
                .any(|block| matches!(block, AssistantContentBlock::ToolCall(_))),
            Self::SystemPromptEcho => false,
        }
    }

    fn resolve(&self, context: &TranscriptContext) -> Vec<FauxContentBlock> {
        match self {
            Self::Blocks(blocks) => blocks.clone(),
            Self::SystemPromptEcho => vec![faux_text(system_prompt_text(context))],
        }
    }
}

/// The text of the transcript's system messages, joined by blank lines.
fn system_prompt_text(context: &TranscriptContext) -> String {
    context
        .messages()
        .iter()
        .filter_map(|message| match message {
            Message::System(system) => Some(get_system_message_text(system)),
            Message::User(_) | Message::Assistant(_) | Message::ToolResult(_) => None,
        })
        .collect::<Vec<_>>()
        .join("\n\n")
}

/// Parse one scripted response entry into a queued faux step.
fn parse_script_step(entry: &JsonValue) -> Result<FauxResponseStep, FauxScriptError> {
    let content = match entry {
        JsonValue::String(text) => ScriptedContent::Blocks(vec![faux_text(text.clone())]),
        JsonValue::Object(map) => {
            if map.get("systemPrompt").and_then(JsonValue::as_bool) == Some(true) {
                ScriptedContent::SystemPromptEcho
            } else if let Some(blocks) = map.get("content").and_then(JsonValue::as_array) {
                ScriptedContent::Blocks(
                    blocks
                        .iter()
                        .map(parse_content_block)
                        .collect::<Result<Vec<_>, _>>()?,
                )
            } else {
                ScriptedContent::Blocks(vec![faux_text(
                    map.get("text")
                        .and_then(JsonValue::as_str)
                        .unwrap_or_default(),
                )])
            }
        }
        JsonValue::Null | JsonValue::Bool(_) | JsonValue::Number(_) | JsonValue::Array(_) => {
            return Err(FauxScriptError::InvalidResponse)
        }
    };
    let stop_reason = match entry.get("stopReason").and_then(JsonValue::as_str) {
        Some("stop") => StopReason::Stop,
        Some("length") => StopReason::Length,
        Some("toolUse") => StopReason::ToolUse,
        Some("error") => StopReason::Error,
        Some("aborted") => StopReason::Aborted,
        Some(other) => return Err(FauxScriptError::UnknownStopReason(other.to_owned())),
        None if content.has_tool_call() => StopReason::ToolUse,
        None => StopReason::Stop,
    };
    // Scripted error text rides the message with `stopReason: "error"`, so
    // overflow-recovery harnesses can script provider overflow responses.
    let error_message = entry
        .get("errorMessage")
        .and_then(JsonValue::as_str)
        .map(str::to_owned);
    let delay_ms = entry
        .get("delayMs")
        .and_then(JsonValue::as_u64)
        .unwrap_or_default();
    let options = FauxAssistantMessageOptions {
        stop_reason: Some(stop_reason),
        error_message,
        ..FauxAssistantMessageOptions::default()
    };
    Ok(match content {
        ScriptedContent::Blocks(blocks) if delay_ms == 0 => {
            faux_assistant_message(blocks, options).into()
        }
        content => scripted_factory(content, options, delay_ms),
    })
}

/// A factory step: content resolved against the request, and a `delay_ms`
/// hold that keeps the request in flight before the first event. The hold
/// races the request's abort signal; on abort the faux stream ends aborted
/// before any content streams, like a transport dying mid-request.
fn scripted_factory(
    content: ScriptedContent,
    options: FauxAssistantMessageOptions,
    delay_ms: u64,
) -> FauxResponseStep {
    FauxResponseStep::Factory(Arc::new(move |context, request, _state, _model| {
        let message = faux_assistant_message(content.resolve(context), options.clone());
        let signal = request.and_then(|request| request.stream.request.signal.clone());
        Box::pin(async move {
            if delay_ms > 0 {
                let hold = tokio::time::sleep(Duration::from_millis(delay_ms));
                match signal {
                    Some(signal) => {
                        tokio::select! {
                            () = hold => {}
                            _ = signal.cancelled() => {}
                        }
                    }
                    None => hold.await,
                }
            }
            Ok(message)
        })
    }))
}

/// Parse one scripted content block (thinking, text, or tool call).
fn parse_content_block(block: &JsonValue) -> Result<FauxContentBlock, FauxScriptError> {
    let object = block.as_object().ok_or(FauxScriptError::BlockNotAnObject)?;
    match object.get("type").and_then(JsonValue::as_str) {
        Some("thinking") => Ok(faux_thinking(
            object
                .get("thinking")
                .and_then(JsonValue::as_str)
                .ok_or(FauxScriptError::MissingThinking)?,
        )),
        Some("text") => Ok(faux_text(
            object
                .get("text")
                .and_then(JsonValue::as_str)
                .ok_or(FauxScriptError::MissingText)?,
        )),
        Some("toolCall") => {
            let name = object
                .get("name")
                .and_then(JsonValue::as_str)
                .ok_or(FauxScriptError::MissingToolName)?;
            let arguments = match object.get("arguments") {
                None => JsonObject::new(),
                Some(JsonValue::Object(arguments)) => arguments.clone(),
                Some(_) => return Err(FauxScriptError::ToolArgumentsNotAnObject),
            };
            let id = object
                .get("id")
                .and_then(JsonValue::as_str)
                .map(str::to_owned);
            Ok(faux_tool_call(name, arguments, id))
        }
        Some(other) => Err(FauxScriptError::UnknownBlockType(other.to_owned())),
        None => Err(FauxScriptError::MissingBlockType),
    }
}

/// The script's response queue. Every stream call takes its step here and
/// hands exactly that step to the faux core, under this lock, so the
/// dequeue, the last-served record, and the core's own pop are one atomic
/// step even for overlapping calls.
struct ScriptQueue {
    pending: VecDeque<FauxResponseStep>,
    /// The last served step, recorded on every serve regardless of the
    /// mode, so repeat-last switched on after serving still has a step.
    last_served: Option<FauxResponseStep>,
    repeat_last_response: bool,
}

impl ScriptQueue {
    /// The queued front, or in repeat-last mode the last served step once
    /// the queue ran dry, or `None` (the core's "No more faux responses
    /// queued" error).
    fn next_step(&mut self) -> Option<FauxResponseStep> {
        match self.pending.pop_front() {
            Some(step) => {
                self.last_served = Some(step.clone());
                Some(step)
            }
            None if self.repeat_last_response => self.last_served.clone(),
            None => None,
        }
    }
}

fn lock(queue: &Mutex<ScriptQueue>) -> MutexGuard<'_, ScriptQueue> {
    queue.lock().unwrap_or_else(PoisonError::into_inner)
}

/// A faux provider serving a [`FauxScript`].
#[derive(Clone)]
pub struct FauxScriptProvider {
    faux: FauxProviderHandle,
    queue: Arc<Mutex<ScriptQueue>>,
}

impl FauxScriptProvider {
    /// The provider registered into the `Models` collection.
    #[must_use]
    pub fn provider(&self) -> &Provider {
        &self.faux.provider
    }

    /// The scripted model.
    #[must_use]
    pub fn get_model(&self) -> Model {
        self.faux.get_model()
    }

    /// Call counters of the underlying faux provider.
    #[must_use]
    pub fn state(&self) -> FauxProviderState {
        self.faux.state()
    }

    /// Stream calls served so far (including exhausted-queue errors).
    #[must_use]
    pub fn call_count(&self) -> u64 {
        self.faux.state().call_count
    }

    /// Replaces the queued responses.
    pub fn set_responses(&self, responses: Vec<FauxResponseStep>) {
        lock(&self.queue).pending = responses.into();
    }

    /// Appends queued responses.
    pub fn append_responses(&self, responses: Vec<FauxResponseStep>) {
        lock(&self.queue).pending.extend(responses);
    }

    /// Number of queued responses.
    #[must_use]
    pub fn get_pending_response_count(&self) -> usize {
        lock(&self.queue).pending.len()
    }

    /// Repeat-last mode: once the queue runs dry, every further call is
    /// served the last served step instead of the "No more faux responses
    /// queued" error. Off by default (the finite response budget).
    pub fn set_repeat_last_response(&self, repeat: bool) {
        lock(&self.queue).repeat_last_response = repeat;
    }
}

/// Register a faux provider (`api: "faux"`, `provider: "faux"`) serving
/// `script` into `models`, replacing any provider with id `faux`.
#[must_use]
pub fn register_faux_provider_from_script(
    models: &Models,
    script: FauxScript,
) -> FauxScriptProvider {
    let mut faux = faux_provider(RegisterFauxProviderOptions {
        api: Some(FAUX_SCRIPT_ID.to_owned()),
        provider: Some(FAUX_SCRIPT_ID.to_owned()),
        models: Some(vec![script.model]),
        tokens_per_second: script.tokens_per_second,
        ..RegisterFauxProviderOptions::default()
    });
    let queue = Arc::new(Mutex::new(ScriptQueue {
        pending: script.responses.into(),
        last_served: None,
        repeat_last_response: script.repeat_last_response,
    }));

    // The core keeps its own queue; each call feeds it exactly the step the
    // script queue serves, under the script queue's lock.
    let core = faux.clone();
    let inner_stream = faux.provider.stream.clone();
    let stream_queue = Arc::clone(&queue);
    faux.provider.stream = Arc::new(move |model, context, options| {
        let mut queue = lock(&stream_queue);
        core.set_responses(queue.next_step().into_iter().collect());
        inner_stream(model, context, options)
    });
    let core = faux.clone();
    let inner_stream_simple = faux.provider.stream_simple.clone();
    let simple_queue = Arc::clone(&queue);
    faux.provider.stream_simple = Arc::new(move |model, context, options| {
        let mut queue = lock(&simple_queue);
        core.set_responses(queue.next_step().into_iter().collect());
        inner_stream_simple(model, context, options)
    });

    models.set_provider(faux.provider.clone());
    FauxScriptProvider { faux, queue }
}

/// A fresh `Models` collection holding only the scripted faux provider
/// (print mode and tests).
#[must_use]
pub fn create_faux_script_models(script: FauxScript) -> (Models, FauxScriptProvider) {
    let models = create_models(CreateModelsOptions::default());
    let provider = register_faux_provider_from_script(&models, script);
    (models, provider)
}
