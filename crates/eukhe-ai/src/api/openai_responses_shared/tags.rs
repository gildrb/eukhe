//! The `OpenAI` Responses wire tags eukhe reads: stream event, output item and
//! content part types, parsed with
//! [`wire_type`](crate::utils::wire_type::wire_type).

use serde::Deserialize;

/// A stream event's `type`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
pub(crate) enum EventType {
    #[serde(rename = "response.created")]
    Created,
    #[serde(rename = "response.output_item.added")]
    OutputItemAdded,
    #[serde(rename = "response.reasoning_summary_text.delta")]
    ReasoningSummaryTextDelta,
    #[serde(rename = "response.reasoning_text.delta")]
    ReasoningTextDelta,
    #[serde(rename = "response.reasoning_summary_part.done")]
    ReasoningSummaryPartDone,
    #[serde(rename = "response.output_text.delta")]
    OutputTextDelta,
    #[serde(rename = "response.refusal.delta")]
    RefusalDelta,
    #[serde(rename = "response.function_call_arguments.delta")]
    FunctionCallArgumentsDelta,
    #[serde(rename = "response.function_call_arguments.done")]
    FunctionCallArgumentsDone,
    #[serde(rename = "response.custom_tool_call_input.delta")]
    CustomToolCallInputDelta,
    #[serde(rename = "response.custom_tool_call_input.done")]
    CustomToolCallInputDone,
    #[serde(rename = "response.output_item.done")]
    OutputItemDone,
    #[serde(rename = "response.completed")]
    Completed,
    #[serde(rename = "response.done")]
    Done,
    #[serde(rename = "response.incomplete")]
    Incomplete,
    #[serde(rename = "response.failed")]
    Failed,
    #[serde(rename = "error")]
    Error,
    #[serde(rename = "codex.rate_limits")]
    CodexRateLimits,
}

/// An output item's `type`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum ItemType {
    Reasoning,
    Message,
    FunctionCall,
    CustomToolCall,
    FunctionCallOutput,
    CustomToolCallOutput,
}

/// A message content part's `type`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum PartType {
    OutputText,
    Refusal,
}

/// An output text part's annotation `type`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum AnnotationType {
    UrlCitation,
}
