//! Compact, replayable assistant-message progress frames.
//!
//! [`AssistantMessageFrameEncoder`] turns one assistant event stream into
//! frames; [`reduce_assistant_message_frames`] replays frames into the message
//! so far. Terminal settlement (`done`/`error`) is excluded and persisted
//! separately.

use std::collections::HashMap;

use serde::{Deserialize, Serialize};

use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, AssistantMessageEvent, JsonObject, JsonValue,
    StopReason, TextContent, ThinkingContent, ToolCall,
};

use super::js::{json_stringify, utf16_len};
use super::json_parse::{parse_streaming_json, parse_streaming_json_object};

/// One frame of assistant-message progress.
// Mirrors the TS union by value; frames are moved into the persisted log once.
#[allow(clippy::large_enum_variant)]
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "type", rename_all_fields = "camelCase")]
pub enum AssistantMessageFrame {
    #[serde(rename = "start")]
    Start { partial: AssistantMessage },
    #[serde(rename = "text_start")]
    TextStart {
        content_index: usize,
        content: TextContent,
    },
    #[serde(rename = "text_delta")]
    TextDelta { content_index: usize, delta: String },
    #[serde(rename = "text_end")]
    TextEnd {
        content_index: usize,
        content: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        text_signature: Option<String>,
    },
    #[serde(rename = "thinking_start")]
    ThinkingStart {
        content_index: usize,
        content: ThinkingContent,
    },
    #[serde(rename = "thinking_delta")]
    ThinkingDelta { content_index: usize, delta: String },
    #[serde(rename = "thinking_end")]
    ThinkingEnd {
        content_index: usize,
        content: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        thinking_signature: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        redacted: Option<bool>,
    },
    #[serde(rename = "toolcall_start")]
    ToolCallStart {
        content_index: usize,
        tool_call: ToolCall,
    },
    #[serde(rename = "toolcall_checkpoint")]
    ToolCallCheckpoint { content_index: usize, json: String },
    #[serde(rename = "toolcall_delta")]
    ToolCallDelta { content_index: usize, delta: String },
    #[serde(rename = "toolcall_end")]
    ToolCallEnd {
        content_index: usize,
        id: String,
        name: String,
        arguments: JsonObject,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        thought_signature: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        namespace: Option<String>,
    },
}

impl AssistantMessageFrame {
    /// The `type` tag.
    #[must_use]
    pub const fn type_name(&self) -> &'static str {
        match self {
            Self::Start { .. } => "start",
            Self::TextStart { .. } => "text_start",
            Self::TextDelta { .. } => "text_delta",
            Self::TextEnd { .. } => "text_end",
            Self::ThinkingStart { .. } => "thinking_start",
            Self::ThinkingDelta { .. } => "thinking_delta",
            Self::ThinkingEnd { .. } => "thinking_end",
            Self::ToolCallStart { .. } => "toolcall_start",
            Self::ToolCallCheckpoint { .. } => "toolcall_checkpoint",
            Self::ToolCallDelta { .. } => "toolcall_delta",
            Self::ToolCallEnd { .. } => "toolcall_end",
        }
    }
}

/// A protocol violation in an event stream or frame sequence (the TS `Error` message).
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("{0}")]
pub struct AssistantMessageFrameError(pub String);

fn error(message: String) -> AssistantMessageFrameError {
    AssistantMessageFrameError(message)
}

/// The kind of a content block, as its `type` tag.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BlockKind {
    Text,
    Thinking,
    ToolCall,
}

impl BlockKind {
    const fn as_str(self) -> &'static str {
        match self {
            Self::Text => "text",
            Self::Thinking => "thinking",
            Self::ToolCall => "toolCall",
        }
    }

    const fn of(block: &AssistantContentBlock) -> Self {
        match block {
            AssistantContentBlock::Text(_) => Self::Text,
            AssistantContentBlock::Thinking(_) => Self::Thinking,
            AssistantContentBlock::ToolCall(_) => Self::ToolCall,
        }
    }
}

enum EncoderBlockState {
    /// Text or thinking: UTF-16 units already in the start snapshot, and delta units seen.
    Text {
        kind: BlockKind,
        covered_chars: usize,
        delta_chars: usize,
    },
    ToolCall {
        caught_up: bool,
        catchup_json: String,
        snapshot_arguments: String,
    },
}

impl EncoderBlockState {
    const fn kind(&self) -> BlockKind {
        match self {
            Self::Text { kind, .. } => *kind,
            Self::ToolCall { .. } => BlockKind::ToolCall,
        }
    }
}

fn clone_text_content(content: &TextContent) -> TextContent {
    TextContent {
        text: content.text.clone(),
        text_signature: content.text_signature.clone(),
        cache_breakpoint: None,
    }
}

fn clone_start_message(message: &AssistantMessage) -> AssistantMessage {
    AssistantMessage {
        content: Vec::new(),
        api: message.api.clone(),
        provider: message.provider.clone(),
        model: message.model.clone(),
        response_model: message.response_model.clone(),
        response_id: message.response_id.clone(),
        provider_thinking_level: message.provider_thinking_level.clone(),
        thinking_level: None,
        diagnostics: message.diagnostics.clone(),
        usage: message.usage,
        stop_reason: StopReason::Pending,
        deferred: None,
        error_message: None,
        raw_stop_reason: None,
        end_turn: None,
        timestamp: message.timestamp,
        duration_ms: None,
    }
}

fn event_block<'a>(
    event_type: &str,
    partial: &'a AssistantMessage,
    content_index: usize,
) -> Result<&'a AssistantContentBlock, AssistantMessageFrameError> {
    partial.content.get(content_index).ok_or_else(|| {
        error(format!(
            "{event_type} event has no content block at index {content_index}"
        ))
    })
}

fn wrong_block(
    event_type: &str,
    block: &AssistantContentBlock,
    content_index: usize,
) -> AssistantMessageFrameError {
    error(format!(
        "{event_type} event points to {} block at index {content_index}",
        block.type_name()
    ))
}

/// `JSON.stringify(arguments)`.
fn serialized_arguments(arguments: &JsonValue) -> String {
    json_stringify(arguments)
}

/// `serializedArguments(parseStreamingJson(""))`.
const EMPTY_PARSED_TOOL_ARGUMENTS: &str = "{}";

/// Whether `current` extends `snapshot` (strings by prefix, arrays and
/// objects element-wise).
fn is_json_prefix(snapshot: &JsonValue, current: &JsonValue) -> bool {
    match (snapshot, current) {
        (JsonValue::String(snapshot), current) => current
            .as_str()
            .is_some_and(|current| current.starts_with(snapshot.as_str())),
        (JsonValue::Array(snapshot), current) => current.as_array().is_some_and(|current| {
            snapshot.len() <= current.len()
                && snapshot
                    .iter()
                    .zip(current)
                    .all(|(snapshot, current)| is_json_prefix(snapshot, current))
        }),
        (JsonValue::Object(snapshot), current) => current.as_object().is_some_and(|current| {
            snapshot.iter().all(|(key, value)| {
                current
                    .get(key)
                    .is_some_and(|current| is_json_prefix(value, current))
            })
        }),
        (JsonValue::Null | JsonValue::Bool(_) | JsonValue::Number(_), current) => {
            snapshot == current
        }
    }
}

/// `text.slice(units)` in UTF-16 code units, never splitting a character.
fn utf16_suffix(text: &str, units: usize) -> &str {
    let mut seen = 0;
    for (index, c) in text.char_indices() {
        if seen >= units {
            return &text[index..];
        }
        seen += c.len_utf16();
    }
    ""
}

/// Encodes one assistant stream. Events may carry a live, advanced `partial`
/// (TS shares one accumulator), so per-block offsets avoid replaying deltas
/// already visible in a start snapshot.
#[derive(Default)]
pub struct AssistantMessageFrameEncoder {
    started: bool,
    terminal: bool,
    blocks: HashMap<usize, EncoderBlockState>,
}

impl std::fmt::Debug for AssistantMessageFrameEncoder {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("AssistantMessageFrameEncoder")
            .field("started", &self.started)
            .field("terminal", &self.terminal)
            .field("open_blocks", &self.blocks.len())
            .finish()
    }
}

impl AssistantMessageFrameEncoder {
    /// A fresh encoder.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Encode one event; `Ok(None)` when it produces no frame.
    ///
    /// # Errors
    ///
    /// The stream breaks the event protocol (events after a terminal event,
    /// a second start, updates before start, blocks of the wrong kind, ...).
    #[allow(clippy::too_many_lines)] // One arm per event type, as in TS.
    pub fn encode(
        &mut self,
        event: &AssistantMessageEvent,
    ) -> Result<Option<AssistantMessageFrame>, AssistantMessageFrameError> {
        if self.terminal {
            return Err(error(format!(
                "Assistant message event {} follows a terminal event",
                event.type_name()
            )));
        }
        let (content_index, partial) = match event {
            AssistantMessageEvent::Start { partial } => {
                if self.started {
                    return Err(error(
                        "Assistant message stream contains more than one start event".to_owned(),
                    ));
                }
                self.started = true;
                return Ok(Some(AssistantMessageFrame::Start {
                    partial: clone_start_message(partial),
                }));
            }
            AssistantMessageEvent::Done { .. } => {
                if !self.started {
                    return Err(error(
                        "Assistant message done event appears before start".to_owned(),
                    ));
                }
                self.terminal = true;
                return Ok(None);
            }
            AssistantMessageEvent::Error { .. } => {
                self.terminal = true;
                return Ok(None);
            }
            AssistantMessageEvent::TextStart {
                content_index,
                partial,
            }
            | AssistantMessageEvent::TextDelta {
                content_index,
                partial,
                ..
            }
            | AssistantMessageEvent::TextEnd {
                content_index,
                partial,
                ..
            }
            | AssistantMessageEvent::ThinkingStart {
                content_index,
                partial,
            }
            | AssistantMessageEvent::ThinkingDelta {
                content_index,
                partial,
                ..
            }
            | AssistantMessageEvent::ThinkingEnd {
                content_index,
                partial,
                ..
            }
            | AssistantMessageEvent::ToolCallStart {
                content_index,
                partial,
            }
            | AssistantMessageEvent::ToolCallDelta {
                content_index,
                partial,
                ..
            }
            | AssistantMessageEvent::ToolCallEnd {
                content_index,
                partial,
                ..
            } => (*content_index, partial),
        };
        if !self.started {
            return Err(error(format!(
                "Assistant message {} event appears before start",
                event.type_name()
            )));
        }
        let event_type = event.type_name();

        match event {
            AssistantMessageEvent::TextStart { .. } => {
                let AssistantContentBlock::Text(content) =
                    event_block(event_type, partial, content_index)?
                else {
                    return Err(wrong_block(
                        event_type,
                        &partial.content[content_index],
                        content_index,
                    ));
                };
                self.start_block(
                    content_index,
                    EncoderBlockState::Text {
                        kind: BlockKind::Text,
                        covered_chars: utf16_len(&content.text),
                        delta_chars: 0,
                    },
                )?;
                Ok(Some(AssistantMessageFrame::TextStart {
                    content_index,
                    content: clone_text_content(content),
                }))
            }
            AssistantMessageEvent::TextDelta { delta, .. } => {
                self.encode_text_delta(content_index, delta, BlockKind::Text)
            }
            AssistantMessageEvent::TextEnd { content, .. } => {
                let AssistantContentBlock::Text(block) =
                    event_block(event_type, partial, content_index)?
                else {
                    return Err(wrong_block(
                        event_type,
                        &partial.content[content_index],
                        content_index,
                    ));
                };
                self.end_block(content_index, BlockKind::Text)?;
                Ok(Some(AssistantMessageFrame::TextEnd {
                    content_index,
                    content: content.clone(),
                    text_signature: block.text_signature.clone(),
                }))
            }
            AssistantMessageEvent::ThinkingStart { .. } => {
                let AssistantContentBlock::Thinking(content) =
                    event_block(event_type, partial, content_index)?
                else {
                    return Err(wrong_block(
                        event_type,
                        &partial.content[content_index],
                        content_index,
                    ));
                };
                self.start_block(
                    content_index,
                    EncoderBlockState::Text {
                        kind: BlockKind::Thinking,
                        covered_chars: utf16_len(&content.thinking),
                        delta_chars: 0,
                    },
                )?;
                Ok(Some(AssistantMessageFrame::ThinkingStart {
                    content_index,
                    content: content.clone(),
                }))
            }
            AssistantMessageEvent::ThinkingDelta { delta, .. } => {
                self.encode_text_delta(content_index, delta, BlockKind::Thinking)
            }
            AssistantMessageEvent::ThinkingEnd { content, .. } => {
                let AssistantContentBlock::Thinking(block) =
                    event_block(event_type, partial, content_index)?
                else {
                    return Err(wrong_block(
                        event_type,
                        &partial.content[content_index],
                        content_index,
                    ));
                };
                self.end_block(content_index, BlockKind::Thinking)?;
                Ok(Some(AssistantMessageFrame::ThinkingEnd {
                    content_index,
                    content: content.clone(),
                    thinking_signature: block.thinking_signature.clone(),
                    redacted: block.redacted,
                }))
            }
            AssistantMessageEvent::ToolCallStart { .. } => {
                let AssistantContentBlock::ToolCall(content) =
                    event_block(event_type, partial, content_index)?
                else {
                    return Err(wrong_block(
                        event_type,
                        &partial.content[content_index],
                        content_index,
                    ));
                };
                let snapshot_arguments =
                    serialized_arguments(&JsonValue::Object(content.arguments.clone()));
                let caught_up = snapshot_arguments == EMPTY_PARSED_TOOL_ARGUMENTS;
                self.start_block(
                    content_index,
                    EncoderBlockState::ToolCall {
                        caught_up,
                        catchup_json: String::new(),
                        snapshot_arguments: if caught_up {
                            String::new()
                        } else {
                            snapshot_arguments
                        },
                    },
                )?;
                Ok(Some(AssistantMessageFrame::ToolCallStart {
                    content_index,
                    tool_call: content.clone(),
                }))
            }
            AssistantMessageEvent::ToolCallDelta { delta, .. } => {
                self.encode_tool_call_delta(content_index, delta)
            }
            AssistantMessageEvent::ToolCallEnd { tool_call, .. } => {
                let block = event_block(event_type, partial, content_index)?;
                if !matches!(block, AssistantContentBlock::ToolCall(_)) {
                    return Err(wrong_block(event_type, block, content_index));
                }
                self.end_block(content_index, BlockKind::ToolCall)?;
                Ok(Some(AssistantMessageFrame::ToolCallEnd {
                    content_index,
                    id: tool_call.id.clone(),
                    name: tool_call.name.clone(),
                    arguments: tool_call.arguments.clone(),
                    thought_signature: tool_call.thought_signature.clone(),
                    namespace: tool_call.namespace.clone(),
                }))
            }
            AssistantMessageEvent::Start { .. }
            | AssistantMessageEvent::Done { .. }
            | AssistantMessageEvent::Error { .. } => Ok(None),
        }
    }

    fn start_block(
        &mut self,
        content_index: usize,
        state: EncoderBlockState,
    ) -> Result<(), AssistantMessageFrameError> {
        if self.blocks.contains_key(&content_index) {
            return Err(error(format!(
                "Assistant message block {content_index} starts more than once"
            )));
        }
        self.blocks.insert(content_index, state);
        Ok(())
    }

    fn block(
        &mut self,
        content_index: usize,
        kind: BlockKind,
    ) -> Result<&mut EncoderBlockState, AssistantMessageFrameError> {
        let state = self.blocks.get_mut(&content_index).ok_or_else(|| {
            error(format!(
                "Assistant message {} block {content_index} has not started",
                kind.as_str()
            ))
        })?;
        if state.kind() != kind {
            return Err(error(format!(
                "Assistant message block {content_index} is {}, not {}",
                state.kind().as_str(),
                kind.as_str()
            )));
        }
        Ok(state)
    }

    fn end_block(
        &mut self,
        content_index: usize,
        kind: BlockKind,
    ) -> Result<(), AssistantMessageFrameError> {
        self.block(content_index, kind)?;
        self.blocks.remove(&content_index);
        Ok(())
    }

    fn encode_text_delta(
        &mut self,
        content_index: usize,
        delta: &str,
        kind: BlockKind,
    ) -> Result<Option<AssistantMessageFrame>, AssistantMessageFrameError> {
        let EncoderBlockState::Text {
            covered_chars,
            delta_chars,
            ..
        } = self.block(content_index, kind)?
        else {
            return Err(error("Unreachable text encoder state".to_owned()));
        };
        let delta_start = *delta_chars;
        let delta_length = utf16_len(delta);
        *delta_chars += delta_length;
        let covered = covered_chars.saturating_sub(delta_start);
        if covered >= delta_length {
            return Ok(None);
        }
        let uncovered = if covered == 0 {
            delta.to_owned()
        } else {
            utf16_suffix(delta, covered).to_owned()
        };
        Ok(Some(match kind {
            BlockKind::Text => AssistantMessageFrame::TextDelta {
                content_index,
                delta: uncovered,
            },
            BlockKind::Thinking | BlockKind::ToolCall => AssistantMessageFrame::ThinkingDelta {
                content_index,
                delta: uncovered,
            },
        }))
    }

    fn encode_tool_call_delta(
        &mut self,
        content_index: usize,
        delta: &str,
    ) -> Result<Option<AssistantMessageFrame>, AssistantMessageFrameError> {
        let EncoderBlockState::ToolCall {
            caught_up,
            catchup_json,
            snapshot_arguments,
        } = self.block(content_index, BlockKind::ToolCall)?
        else {
            return Err(error("Unreachable tool-call encoder state".to_owned()));
        };
        if *caught_up {
            return Ok(
                (!delta.is_empty()).then(|| AssistantMessageFrame::ToolCallDelta {
                    content_index,
                    delta: delta.to_owned(),
                }),
            );
        }
        catchup_json.push_str(delta);
        let arguments = parse_streaming_json(Some(catchup_json));
        if serialized_arguments(&arguments) != *snapshot_arguments {
            // Legacy grammar calls include the initial input in toolcall_start,
            // but their JSON delta stream still begins at an empty input. Its
            // parsed arguments can therefore extend, rather than exactly
            // reproduce, the start snapshot.
            let snapshot = parse_streaming_json(Some(snapshot_arguments));
            if !is_json_prefix(&snapshot, &arguments) {
                return Ok(None);
            }
        }
        *caught_up = true;
        snapshot_arguments.clear();
        let json = std::mem::take(catchup_json);
        Ok(
            (!json.is_empty()).then_some(AssistantMessageFrame::ToolCallCheckpoint {
                content_index,
                json,
            }),
        )
    }
}

/// Reducer-side state of a started block.
struct ReducerBlockState {
    kind: BlockKind,
    ended: bool,
    /// Tool-call JSON received since the last checkpoint.
    json: String,
}

fn append_block(
    message: &mut AssistantMessage,
    states: &mut Vec<(usize, ReducerBlockState)>,
    content_index: usize,
    block: AssistantContentBlock,
) -> Result<(), AssistantMessageFrameError> {
    if content_index != message.content.len() {
        let reason = if content_index < message.content.len() {
            "already exists"
        } else {
            "would leave a gap"
        };
        return Err(error(format!(
            "Cannot start assistant message block at index {content_index}: {reason}"
        )));
    }
    let kind = BlockKind::of(&block);
    message.content.push(block);
    states.retain(|(index, _)| *index != content_index);
    states.push((
        content_index,
        ReducerBlockState {
            kind,
            ended: false,
            json: String::new(),
        },
    ));
    Ok(())
}

fn active_block<'a>(
    message: &'a mut AssistantMessage,
    states: &'a mut [(usize, ReducerBlockState)],
    content_index: usize,
    expected_kind: BlockKind,
    frame_type: &str,
) -> Result<(&'a mut AssistantContentBlock, &'a mut ReducerBlockState), AssistantMessageFrameError>
{
    let state = states
        .iter_mut()
        .find(|(index, _)| *index == content_index)
        .map(|(_, state)| state);
    let block = message.content.get_mut(content_index);
    let (Some(state), Some(block)) = (state, block) else {
        return Err(error(format!(
            "{frame_type} frame has no started block at index {content_index}"
        )));
    };
    if state.kind != expected_kind || BlockKind::of(block) != expected_kind {
        return Err(error(format!(
            "{frame_type} frame expected {} block at index {content_index}, found {}",
            expected_kind.as_str(),
            block.type_name()
        )));
    }
    if state.ended {
        return Err(error(format!(
            "{frame_type} frame follows the end of block at index {content_index}"
        )));
    }
    Ok((block, state))
}

/// Replay frames without mutating them. `Ok(None)` when there is no start frame.
///
/// # Errors
///
/// The frame sequence is invalid (frames before start, a second start,
/// blocks of the wrong kind, frames after a block's end, index gaps).
#[allow(clippy::too_many_lines)] // One arm per frame type, as in TS.
pub fn reduce_assistant_message_frames<'a>(
    frames: impl IntoIterator<Item = &'a AssistantMessageFrame>,
) -> Result<Option<AssistantMessage>, AssistantMessageFrameError> {
    let mut message: Option<AssistantMessage> = None;
    let mut frame_before_start: Option<&'static str> = None;
    // Started blocks in insertion order (TS `Map` iteration order).
    let mut states: Vec<(usize, ReducerBlockState)> = Vec::new();

    for frame in frames {
        if let AssistantMessageFrame::Start { partial } = frame {
            if message.is_some() {
                return Err(error(
                    "Assistant message frame sequence contains more than one start frame"
                        .to_owned(),
                ));
            }
            if let Some(before) = frame_before_start {
                return Err(error(format!(
                    "{before} frame appears before the start frame"
                )));
            }
            message = Some(partial.clone());
            continue;
        }
        let Some(message) = message.as_mut() else {
            frame_before_start.get_or_insert(frame.type_name());
            continue;
        };
        let frame_type = frame.type_name();

        match frame {
            AssistantMessageFrame::Start { .. } => {}
            AssistantMessageFrame::TextStart {
                content_index,
                content,
            } => {
                append_block(
                    message,
                    &mut states,
                    *content_index,
                    AssistantContentBlock::Text(content.clone()),
                )?;
            }
            AssistantMessageFrame::TextDelta {
                content_index,
                delta,
            } => {
                let (block, _) = active_block(
                    message,
                    &mut states,
                    *content_index,
                    BlockKind::Text,
                    frame_type,
                )?;
                if let AssistantContentBlock::Text(text) = block {
                    text.text.push_str(delta);
                }
            }
            AssistantMessageFrame::TextEnd {
                content_index,
                content,
                text_signature,
            } => {
                let (block, state) = active_block(
                    message,
                    &mut states,
                    *content_index,
                    BlockKind::Text,
                    frame_type,
                )?;
                if let AssistantContentBlock::Text(text) = block {
                    text.text.clone_from(content);
                    text.text_signature.clone_from(text_signature);
                }
                state.ended = true;
            }
            AssistantMessageFrame::ThinkingStart {
                content_index,
                content,
            } => {
                append_block(
                    message,
                    &mut states,
                    *content_index,
                    AssistantContentBlock::Thinking(content.clone()),
                )?;
            }
            AssistantMessageFrame::ThinkingDelta {
                content_index,
                delta,
            } => {
                let (block, _) = active_block(
                    message,
                    &mut states,
                    *content_index,
                    BlockKind::Thinking,
                    frame_type,
                )?;
                if let AssistantContentBlock::Thinking(thinking) = block {
                    thinking.thinking.push_str(delta);
                }
            }
            AssistantMessageFrame::ThinkingEnd {
                content_index,
                content,
                thinking_signature,
                redacted,
            } => {
                let (block, state) = active_block(
                    message,
                    &mut states,
                    *content_index,
                    BlockKind::Thinking,
                    frame_type,
                )?;
                if let AssistantContentBlock::Thinking(thinking) = block {
                    thinking.thinking.clone_from(content);
                    thinking.thinking_signature.clone_from(thinking_signature);
                    thinking.redacted = *redacted;
                }
                state.ended = true;
            }
            AssistantMessageFrame::ToolCallStart {
                content_index,
                tool_call,
            } => {
                append_block(
                    message,
                    &mut states,
                    *content_index,
                    AssistantContentBlock::ToolCall(tool_call.clone()),
                )?;
            }
            AssistantMessageFrame::ToolCallCheckpoint {
                content_index,
                json,
            } => {
                let (block, state) = active_block(
                    message,
                    &mut states,
                    *content_index,
                    BlockKind::ToolCall,
                    frame_type,
                )?;
                state.json.clone_from(json);
                if let AssistantContentBlock::ToolCall(call) = block {
                    call.arguments = parse_streaming_json_object(Some(json));
                }
            }
            AssistantMessageFrame::ToolCallDelta {
                content_index,
                delta,
            } => {
                let (_, state) = active_block(
                    message,
                    &mut states,
                    *content_index,
                    BlockKind::ToolCall,
                    frame_type,
                )?;
                state.json.push_str(delta);
            }
            AssistantMessageFrame::ToolCallEnd {
                content_index,
                id,
                name,
                arguments,
                thought_signature,
                namespace,
            } => {
                let (block, state) = active_block(
                    message,
                    &mut states,
                    *content_index,
                    BlockKind::ToolCall,
                    frame_type,
                )?;
                if let AssistantContentBlock::ToolCall(call) = block {
                    call.id.clone_from(id);
                    call.name.clone_from(name);
                    call.arguments.clone_from(arguments);
                    call.thought_signature.clone_from(thought_signature);
                    call.namespace.clone_from(namespace);
                }
                state.ended = true;
            }
        }
    }

    let Some(mut message) = message else {
        return Ok(None);
    };
    for (content_index, state) in &states {
        if state.kind != BlockKind::ToolCall || state.ended || state.json.is_empty() {
            continue;
        }
        if let Some(AssistantContentBlock::ToolCall(call)) = message.content.get_mut(*content_index)
        {
            call.arguments = parse_streaming_json_object(Some(&state.json));
        }
    }
    Ok(Some(message))
}

#[cfg(test)]
mod tests;
