//! Transcript messages: system, user, assistant, and tool-result messages,
//! plus the deferred-response handle and assistant diagnostics.
//!
//! Each message struct serializes its own `role` tag first; [`Message`]
//! serializes untagged and deserializes by dispatching on `role`.

use indexmap::IndexMap;
use serde::{Deserialize, Deserializer, Serialize};

use super::content::{
    null_as_default, AssistantContentBlock, SystemContent, UserContent, UserContentBlock,
};
use super::settings::ModelThinkingLevel;
use super::string_enum::string_enum;
use super::tool::{Tool, ToolReference};
use super::usage::{StopReason, Usage};
use super::{Api, JsonObject, JsonValue, ProviderId};

/// Deserialize a present `JsonValue` field, keeping an explicit `null` as
/// `Some(Value::Null)` (absence stays `None` through `#[serde(default)]`).
pub(crate) fn present_json<'de, D: Deserializer<'de>>(
    deserializer: D,
) -> Result<Option<JsonValue>, D::Error> {
    JsonValue::deserialize(deserializer).map(Some)
}

/// A durable handle for a provider request that continues asynchronously.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct DeferredHandle {
    pub provider: String,
    pub model_id: String,
    pub api: String,
    /// Provider token, such as a response id or batch id plus row id.
    pub id: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub expires_at: Option<u64>,
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        serialize_with = "super::js_number::option::serialize"
    )]
    pub poll_after_ms: Option<f64>,
    /// Provider conversion data required to reconstruct the final assistant message.
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        deserialize_with = "present_json"
    )]
    pub data: Option<JsonValue>,
}

/// TS `string | number` error code of a diagnostic.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum DiagnosticCode {
    String(String),
    Number(#[serde(serialize_with = "super::js_number::serialize")] f64),
}

/// Error details captured in a diagnostic.
#[derive(Debug, Clone, PartialEq, Default, Serialize, Deserialize)]
pub struct DiagnosticErrorInfo {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
    pub message: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub stack: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub code: Option<DiagnosticCode>,
}

/// A redacted provider/runtime diagnostic for a failure or recovery.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct AssistantMessageDiagnostic {
    #[serde(rename = "type")]
    pub kind: String,
    pub timestamp: u64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub error: Option<DiagnosticErrorInfo>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub details: Option<JsonObject>,
}

/// System instructions and tool declarations at one point in the transcript.
///
/// The leading system message is the system prompt. Later system messages
/// change it: `content` adds instructions from that point on, `sections`
/// replace or remove named prompt sections, and `tools_added`/`tools_removed`
/// change the tool set. Replaying every system message in order yields the
/// current prompt and tools.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "role", rename = "system", rename_all = "camelCase")]
pub struct SystemMessage {
    /// Instruction text. On the leading message this is the base prompt; later, additional instructions.
    pub content: SystemContent,
    /// Named, ordered prompt sections rendered verbatim after `content`. The
    /// leading message declares them; later messages replace sections by name,
    /// and `None` removes one.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub sections: Option<IndexMap<String, Option<String>>>,
    /// Tools that stop being available at this point. Serialized before
    /// `toolsAdded`: pi-durable's `prompt.ts` persists `{ role, content,
    /// sections, toolsRemoved, toolsAdded, timestamp }`; pi-ai's own builders
    /// (`transcript.ts`) only ever emit `toolsAdded`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tools_removed: Option<Vec<ToolReference>>,
    /// Complete definitions of tools that become available at this point.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tools_added: Option<Vec<Tool>>,
    /// Unix timestamp in milliseconds.
    pub timestamp: u64,
}

/// A user message.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "role", rename = "user")]
pub struct UserMessage {
    #[serde(default, deserialize_with = "null_as_default")]
    pub content: UserContent,
    /// Unix timestamp in milliseconds.
    pub timestamp: u64,
}

/// An assistant response.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "role", rename = "assistant", rename_all = "camelCase")]
pub struct AssistantMessage {
    #[serde(default, deserialize_with = "null_as_default")]
    pub content: Vec<AssistantContentBlock>,
    pub api: Api,
    pub provider: ProviderId,
    pub model: String,
    /// Concrete model reported by the provider when different from the requested `model`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub response_model: Option<String>,
    /// Provider-specific response/message identifier when the upstream API exposes one.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub response_id: Option<String>,
    /// Exact provider-native effort level used for this response.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub provider_thinking_level: Option<String>,
    /// Pi thinking level the agent loop requested for this response.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub thinking_level: Option<ModelThinkingLevel>,
    /// Redacted provider/runtime diagnostics for failures and recoveries.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub diagnostics: Option<Vec<AssistantMessageDiagnostic>>,
    pub usage: Usage,
    pub stop_reason: StopReason,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub deferred: Option<DeferredHandle>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub error_message: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub raw_stop_reason: Option<String>,
    /// Provider indication of whether the model explicitly ended its turn.
    /// Preserved for debugging; does not affect agent control flow.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub end_turn: Option<bool>,
    /// Unix timestamp in milliseconds when the request started.
    pub timestamp: u64,
    /// Milliseconds from `timestamp` until the response ended, measured with
    /// a monotonic clock. Set by `AssistantMessageEventStream` on the final
    /// message of a response it saw start; absent for legacy messages and for
    /// deferred results fetched later.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub duration_ms: Option<u64>,
}

string_enum! {
    /// Outcome of a nested tool call. `unfinished`: the call was still
    /// running when the calling tool finished.
    pub enum NestedToolCallStatus {
        Ok => "ok",
        Error => "error",
        Unfinished => "unfinished",
    }
}

/// A tool call that another tool made while it ran, for example from a codemode script.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct NestedToolCallRecord {
    pub id: String,
    pub name: String,
    /// Omitted when over the size limits; `arguments_bytes` then gives their size.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub arguments: Option<JsonObject>,
    /// UTF-8 size of the arguments as JSON, set when `arguments` is omitted.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub arguments_bytes: Option<u64>,
    pub status: NestedToolCallStatus,
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        serialize_with = "super::js_number::option::serialize"
    )]
    pub duration_ms: Option<f64>,
    /// Error text, truncated.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

/// Bounded record of the nested calls a tool made. Results are not recorded.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct NestedToolCalls {
    pub calls: Vec<NestedToolCallRecord>,
    /// False when calls were dropped, arguments omitted, or calls had not finished.
    pub complete: bool,
}

/// The result of a tool call. `details` is the JSON representation of the
/// tool's typed details.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "role", rename = "toolResult", rename_all = "camelCase")]
pub struct ToolResultMessage {
    pub tool_call_id: String,
    pub tool_name: String,
    /// Supports text and images.
    #[serde(default, deserialize_with = "null_as_default")]
    pub content: Vec<UserContentBlock>,
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        deserialize_with = "present_json"
    )]
    pub details: Option<JsonValue>,
    /// Usage from the tool execution itself, if available. Not part of main LLM context accounting.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub usage: Option<Usage>,
    /// Calls this tool made to other tools. Kept for the session record; not sent to the model.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub nested_calls: Option<NestedToolCalls>,
    pub is_error: bool,
    /// Unix timestamp in milliseconds when the result was created.
    pub timestamp: u64,
    /// Milliseconds the tool's execution took, measured with a monotonic
    /// clock. Absent for legacy results.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub duration_ms: Option<u64>,
}

/// TS `Message = SystemMessage | UserMessage | AssistantMessage | ToolResultMessage`.
// Mirrors the TS `Message` union by value, as every caller builds and matches it.
#[allow(clippy::large_enum_variant)]
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(untagged)]
#[serde(from = "MessageWire")]
pub enum Message {
    System(SystemMessage),
    User(UserMessage),
    Assistant(AssistantMessage),
    ToolResult(ToolResultMessage),
}

// Deserialization mirror of `Message`.
#[allow(clippy::large_enum_variant)]
#[derive(Deserialize)]
#[serde(tag = "role")]
enum MessageWire {
    #[serde(rename = "system")]
    System(SystemMessage),
    #[serde(rename = "user")]
    User(UserMessage),
    #[serde(rename = "assistant")]
    Assistant(AssistantMessage),
    #[serde(rename = "toolResult")]
    ToolResult(ToolResultMessage),
}

impl From<MessageWire> for Message {
    fn from(wire: MessageWire) -> Self {
        match wire {
            MessageWire::System(message) => Self::System(message),
            MessageWire::User(message) => Self::User(message),
            MessageWire::Assistant(message) => Self::Assistant(message),
            MessageWire::ToolResult(message) => Self::ToolResult(message),
        }
    }
}

impl Message {
    /// The `role` tag.
    #[must_use]
    pub const fn role(&self) -> &'static str {
        match self {
            Self::System(_) => "system",
            Self::User(_) => "user",
            Self::Assistant(_) => "assistant",
            Self::ToolResult(_) => "toolResult",
        }
    }

    /// Unix timestamp in milliseconds.
    #[must_use]
    pub const fn timestamp(&self) -> u64 {
        match self {
            Self::System(message) => message.timestamp,
            Self::User(message) => message.timestamp,
            Self::Assistant(message) => message.timestamp,
            Self::ToolResult(message) => message.timestamp,
        }
    }

    /// The system message, when this is one.
    #[must_use]
    pub const fn as_system(&self) -> Option<&SystemMessage> {
        match self {
            Self::System(message) => Some(message),
            Self::User(_) | Self::Assistant(_) | Self::ToolResult(_) => None,
        }
    }

    /// The assistant message, when this is one.
    #[must_use]
    pub const fn as_assistant(&self) -> Option<&AssistantMessage> {
        match self {
            Self::Assistant(message) => Some(message),
            Self::System(_) | Self::User(_) | Self::ToolResult(_) => None,
        }
    }
}

impl From<SystemMessage> for Message {
    fn from(message: SystemMessage) -> Self {
        Self::System(message)
    }
}

impl From<UserMessage> for Message {
    fn from(message: UserMessage) -> Self {
        Self::User(message)
    }
}

impl From<AssistantMessage> for Message {
    fn from(message: AssistantMessage) -> Self {
        Self::Assistant(message)
    }
}

impl From<ToolResultMessage> for Message {
    fn from(message: ToolResultMessage) -> Self {
        Self::ToolResult(message)
    }
}
