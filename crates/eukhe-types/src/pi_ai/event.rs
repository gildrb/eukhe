//! The assistant message event protocol.

use serde::{Deserialize, Serialize};

use super::content::ToolCall;
use super::message::AssistantMessage;
use super::partial::Partial;
use super::timing::PromptProgress;
use super::usage::{DoneReason, ErrorReason};

/// Event protocol for `AssistantMessageEventStream`.
///
/// Successful streams emit `start` before partial updates and terminate with
/// `done`. A stream may terminate directly with `error` when request setup
/// fails before generation starts; after `start`, failures also terminate
/// with `error`. Updates and `done` never appear before `start`.
/// `prompt_progress` (llama.cpp `llama-server`) comes between `start` and
/// the first content event: how far the server got through the prompt.
///
/// `partial` is the response so far: one [`Partial`] shared by every event
/// of the stream, read when handling the event (it may already be ahead).
/// Text and thinking blocks are empty when their `*_start` event is emitted
/// and grow only through their `*_delta` events until the authoritative
/// `*_end`. Redacted thinking may be complete
/// at start and emit no deltas. Tool-call arguments at `toolcall_start` are
/// provider-specific; `toolcall_delta` carries subsequent JSON updates.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "type", rename_all_fields = "camelCase")]
pub enum AssistantMessageEvent {
    #[serde(rename = "start")]
    Start { partial: Partial },
    #[serde(rename = "prompt_progress")]
    PromptProgress {
        progress: PromptProgress,
        partial: Partial,
    },
    #[serde(rename = "text_start")]
    TextStart {
        content_index: usize,
        partial: Partial,
    },
    #[serde(rename = "text_delta")]
    TextDelta {
        content_index: usize,
        delta: String,
        partial: Partial,
    },
    #[serde(rename = "text_end")]
    TextEnd {
        content_index: usize,
        content: String,
        partial: Partial,
    },
    #[serde(rename = "thinking_start")]
    ThinkingStart {
        content_index: usize,
        partial: Partial,
    },
    #[serde(rename = "thinking_delta")]
    ThinkingDelta {
        content_index: usize,
        delta: String,
        partial: Partial,
    },
    #[serde(rename = "thinking_end")]
    ThinkingEnd {
        content_index: usize,
        content: String,
        partial: Partial,
    },
    #[serde(rename = "toolcall_start")]
    ToolCallStart {
        content_index: usize,
        partial: Partial,
    },
    #[serde(rename = "toolcall_delta")]
    ToolCallDelta {
        content_index: usize,
        delta: String,
        partial: Partial,
    },
    #[serde(rename = "toolcall_end")]
    ToolCallEnd {
        content_index: usize,
        tool_call: ToolCall,
        partial: Partial,
    },
    #[serde(rename = "done")]
    Done {
        reason: DoneReason,
        message: AssistantMessage,
    },
    #[serde(rename = "error")]
    Error {
        reason: ErrorReason,
        error: AssistantMessage,
    },
}

impl AssistantMessageEvent {
    /// The `type` tag.
    #[must_use]
    pub const fn type_name(&self) -> &'static str {
        match self {
            Self::Start { .. } => "start",
            Self::PromptProgress { .. } => "prompt_progress",
            Self::TextStart { .. } => "text_start",
            Self::TextDelta { .. } => "text_delta",
            Self::TextEnd { .. } => "text_end",
            Self::ThinkingStart { .. } => "thinking_start",
            Self::ThinkingDelta { .. } => "thinking_delta",
            Self::ThinkingEnd { .. } => "thinking_end",
            Self::ToolCallStart { .. } => "toolcall_start",
            Self::ToolCallDelta { .. } => "toolcall_delta",
            Self::ToolCallEnd { .. } => "toolcall_end",
            Self::Done { .. } => "done",
            Self::Error { .. } => "error",
        }
    }

    /// The live partial; `None` for `done` and `error`.
    #[must_use]
    pub const fn partial(&self) -> Option<&Partial> {
        match self {
            Self::Start { partial }
            | Self::PromptProgress { partial, .. }
            | Self::TextStart { partial, .. }
            | Self::TextDelta { partial, .. }
            | Self::TextEnd { partial, .. }
            | Self::ThinkingStart { partial, .. }
            | Self::ThinkingDelta { partial, .. }
            | Self::ThinkingEnd { partial, .. }
            | Self::ToolCallStart { partial, .. }
            | Self::ToolCallDelta { partial, .. }
            | Self::ToolCallEnd { partial, .. } => Some(partial),
            Self::Done { .. } | Self::Error { .. } => None,
        }
    }
}
