//! The Anthropic Messages wire tags eukhe reads: event, content block,
//! delta, thinking and role names, parsed with
//! [`wire_type`](crate::utils::wire_type::wire_type).

use serde::Deserialize;

/// An SSE event name and its JSON `type`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum EventType {
    MessageStart,
    MessageDelta,
    MessageStop,
    ContentBlockStart,
    ContentBlockDelta,
    ContentBlockStop,
    Error,
}

/// A content block's `type`, in requests and responses.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum BlockType {
    Text,
    Image,
    Thinking,
    RedactedThinking,
    ToolUse,
    ToolResult,
    ToolAddition,
    ToolRemoval,
    Fallback,
    WebSearchToolResult,
    WebSearchResult,
}

/// A `content_block_delta`'s `delta.type`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
pub(crate) enum DeltaType {
    #[serde(rename = "text_delta")]
    Text,
    #[serde(rename = "thinking_delta")]
    Thinking,
    #[serde(rename = "input_json_delta")]
    InputJson,
    #[serde(rename = "signature_delta")]
    Signature,
}

/// A request's `thinking.type`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum ThinkingType {
    Adaptive,
    Enabled,
    BetweenTools,
}

/// A wire message's `role`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum Role {
    User,
    System,
    Assistant,
}
