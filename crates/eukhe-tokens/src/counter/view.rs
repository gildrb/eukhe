//! The parts of a message the counter reads, borrowed from each of eukhe's
//! message shapes: the `pi_ai` transcript types, the session's agent
//! messages, and wire JSON rows.

use std::borrow::Cow;

use eukhe_types::session::AgentMessage;
use eukhe_types::{ai, pi_ai};
use serde::Deserialize;
use serde_json::Value;

/// The `role` of a wire message row.
#[derive(Clone, Copy, Deserialize)]
#[serde(rename_all = "camelCase")]
enum WireRole {
    Assistant,
    User,
    Developer,
    Custom,
    HookMessage,
    ToolResult,
    BashExecution,
    BranchSummary,
    CompactionSummary,
    #[serde(other)]
    Other,
}

/// The `type` of a wire content block.
#[derive(Clone, Copy, Deserialize)]
#[serde(rename_all = "camelCase")]
enum WireBlock {
    Text,
    Image,
    Thinking,
    ToolCall,
    #[serde(other)]
    Other,
}

/// `value[key]` as `T`; absent or another shape is `None`.
fn wire_field<'a, T: Deserialize<'a>>(value: &'a Value, key: &str) -> Option<T> {
    value.get(key).and_then(|field| T::deserialize(field).ok())
}

/// One countable part of a message.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Part<'a> {
    /// Text the model reads.
    Text(&'a str),
    /// A base64-encoded image.
    Image(&'a str),
    /// A thinking block: its visible text, its replay signature (a
    /// redacted block's whole payload).
    Thinking {
        text: &'a str,
        signature: Option<&'a str>,
        redacted: bool,
    },
    /// A tool call: its name and its arguments as JSON text.
    ToolCall {
        name: &'a str,
        arguments: Cow<'a, str>,
    },
}

/// An assistant turn: who produced it, how it ended, what its provider
/// reported, and its blocks.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AssistantTurn<'a> {
    pub api: &'a str,
    pub provider: &'a str,
    pub model: &'a str,
    /// The turn aborted or failed: replay drops it.
    pub dropped: bool,
    /// Output tokens the provider reported for the turn.
    pub output: u64,
    /// Reasoning tokens the provider reported, when it did.
    pub reasoning: Option<u64>,
    pub parts: Vec<Part<'a>>,
}

/// A message as the counter reads it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MessageParts<'a> {
    /// Any message but an assistant turn: its parts.
    Plain(Vec<Part<'a>>),
    /// An assistant turn.
    Assistant(AssistantTurn<'a>),
}

/// JSON text of tool-call arguments (`JSON.stringify` of an object).
fn arguments_json<T: serde::Serialize>(arguments: &T) -> Cow<'static, str> {
    Cow::Owned(serde_json::to_string(arguments).unwrap_or_else(|_| "null".to_owned()))
}

impl<'a> MessageParts<'a> {
    /// A `pi_ai` transcript message; `None` for a system message, whose
    /// prompt text the caller assembles (eukhe-ai `get_system_message_text`).
    #[must_use]
    pub fn from_pi_ai(message: &'a pi_ai::Message) -> Option<Self> {
        Some(match message {
            pi_ai::Message::System(_) => return None,
            pi_ai::Message::User(user) => Self::Plain(pi_user_content(&user.content)),
            pi_ai::Message::ToolResult(result) => Self::Plain(pi_blocks(&result.content)),
            pi_ai::Message::Assistant(assistant) => Self::Assistant(AssistantTurn {
                api: assistant.api.as_str(),
                provider: assistant.provider.as_str(),
                model: &assistant.model,
                dropped: matches!(
                    assistant.stop_reason,
                    pi_ai::StopReason::Aborted | pi_ai::StopReason::Error
                ),
                output: assistant.usage.output,
                reasoning: assistant.usage.reasoning,
                parts: assistant
                    .content
                    .iter()
                    .map(|block| match block {
                        pi_ai::AssistantContentBlock::Text(text) => Part::Text(&text.text),
                        pi_ai::AssistantContentBlock::Thinking(thinking) => Part::Thinking {
                            text: &thinking.thinking,
                            signature: thinking.thinking_signature.as_deref(),
                            redacted: thinking.redacted == Some(true),
                        },
                        pi_ai::AssistantContentBlock::ToolCall(call) => Part::ToolCall {
                            name: &call.name,
                            arguments: arguments_json(&call.arguments),
                        },
                    })
                    .collect(),
            }),
        })
    }

    /// A session agent message.
    #[must_use]
    pub fn from_agent(message: &'a AgentMessage) -> Self {
        match message {
            AgentMessage::User(user) => Self::Plain(ai_user_content(&user.content)),
            AgentMessage::Custom(custom) => Self::Plain(ai_user_content(&custom.content)),
            AgentMessage::ToolResult(result) => Self::Plain(ai_blocks(&result.content)),
            AgentMessage::BashExecution(bash) => {
                Self::Plain(vec![Part::Text(&bash.command), Part::Text(&bash.output)])
            }
            AgentMessage::BranchSummary(summary) => Self::Plain(vec![Part::Text(&summary.summary)]),
            AgentMessage::CompactionSummary(summary) => {
                Self::Plain(vec![Part::Text(&summary.summary)])
            }
            AgentMessage::Assistant(assistant) => Self::Assistant(ai_assistant(assistant)),
        }
    }

    /// A wire message row (`AgentMessage` JSON). Unknown roles count
    /// nothing.
    #[must_use]
    pub fn from_wire(message: &'a Value) -> Self {
        let text = |key: &str| message.get(key).and_then(Value::as_str);
        match wire_field(message, "role").unwrap_or(WireRole::Other) {
            WireRole::Assistant => Self::Assistant(wire_assistant(message)),
            WireRole::User
            | WireRole::Developer
            | WireRole::Custom
            | WireRole::HookMessage
            | WireRole::ToolResult => Self::Plain(match message.get("content") {
                Some(Value::String(content)) => vec![Part::Text(content)],
                Some(Value::Array(blocks)) => blocks.iter().filter_map(wire_user_block).collect(),
                Some(_) | None => Vec::new(),
            }),
            WireRole::BashExecution => Self::Plain(
                [text("command"), text("output")]
                    .into_iter()
                    .flatten()
                    .map(Part::Text)
                    .collect(),
            ),
            WireRole::BranchSummary | WireRole::CompactionSummary => {
                Self::Plain(text("summary").map(Part::Text).into_iter().collect())
            }
            WireRole::Other => Self::Plain(Vec::new()),
        }
    }
}

fn pi_user_content(content: &pi_ai::UserContent) -> Vec<Part<'_>> {
    match content {
        pi_ai::UserContent::Text(text) => vec![Part::Text(text)],
        pi_ai::UserContent::Blocks(blocks) => pi_blocks(blocks),
    }
}

fn pi_blocks(blocks: &[pi_ai::UserContentBlock]) -> Vec<Part<'_>> {
    blocks
        .iter()
        .map(|block| match block {
            pi_ai::UserContentBlock::Text(text) => Part::Text(&text.text),
            pi_ai::UserContentBlock::Image(image) => Part::Image(&image.data),
        })
        .collect()
}

fn ai_user_content(content: &ai::UserContent) -> Vec<Part<'_>> {
    match content {
        ai::UserContent::Text(text) => vec![Part::Text(text)],
        ai::UserContent::Blocks(blocks) => ai_blocks(blocks),
    }
}

/// Parts of agent-message content blocks; an un-modeled (`Raw`) block is
/// read like a wire block.
#[must_use]
pub fn ai_blocks(blocks: &[ai::UserContentBlock]) -> Vec<Part<'_>> {
    blocks
        .iter()
        .filter_map(|block| match block {
            ai::UserContentBlock::Text(text) => Some(Part::Text(&text.text)),
            ai::UserContentBlock::Image(image) => Some(Part::Image(&image.data)),
            ai::UserContentBlock::Raw(raw) => wire_user_block(raw),
        })
        .collect()
}

/// An agent-message assistant turn.
#[must_use]
pub fn ai_assistant(assistant: &ai::AssistantMessage) -> AssistantTurn<'_> {
    AssistantTurn {
        api: assistant.api.as_str(),
        provider: assistant.provider.as_str(),
        model: &assistant.model,
        dropped: matches!(
            assistant.stop_reason,
            ai::StopReason::Aborted | ai::StopReason::Error
        ),
        output: assistant.usage.output,
        // The agent-message usage keeps no reasoning split.
        reasoning: None,
        parts: assistant
            .content
            .iter()
            .map(|block| match block {
                ai::AssistantContentBlock::Text(text) => Part::Text(&text.text),
                ai::AssistantContentBlock::Thinking(thinking) => Part::Thinking {
                    text: &thinking.thinking,
                    signature: thinking.thinking_signature.as_deref(),
                    redacted: thinking.redacted == Some(true),
                },
                ai::AssistantContentBlock::ToolCall(call) => Part::ToolCall {
                    name: &call.name,
                    arguments: arguments_json(&call.arguments),
                },
            })
            .collect(),
    }
}

/// A text or image block of user, custom or tool-result wire content.
fn wire_user_block(block: &Value) -> Option<Part<'_>> {
    let field = |key: &str| block.get(key).and_then(Value::as_str);
    match block.get("type").map(WireBlock::deserialize) {
        Some(Ok(WireBlock::Image)) => field("data").map(Part::Image),
        // Earlier builds persisted text blocks without a (string) `type` tag.
        Some(Ok(WireBlock::Text) | Err(_)) | None => field("text").map(Part::Text),
        Some(Ok(WireBlock::Thinking | WireBlock::ToolCall | WireBlock::Other)) => None,
    }
}

fn wire_assistant(message: &Value) -> AssistantTurn<'_> {
    let text = |key: &str| message.get(key).and_then(Value::as_str).unwrap_or_default();
    let usage = message.get("usage");
    let usage_field = |key: &str| {
        usage
            .and_then(|usage| usage.get(key))
            .and_then(Value::as_u64)
    };
    AssistantTurn {
        api: text("api"),
        provider: text("provider"),
        model: text("model"),
        dropped: matches!(
            wire_field(message, "stopReason"),
            Some(ai::StopReason::Aborted | ai::StopReason::Error)
        ),
        output: usage_field("output").unwrap_or(0),
        reasoning: usage_field("reasoning"),
        parts: message
            .get("content")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
            .filter_map(|block| {
                let field = |key: &str| block.get(key).and_then(Value::as_str);
                match wire_field(block, "type")? {
                    WireBlock::Text => field("text").map(Part::Text),
                    WireBlock::Thinking => Some(Part::Thinking {
                        text: field("thinking").unwrap_or_default(),
                        signature: field("thinkingSignature"),
                        redacted: block.get("redacted").and_then(Value::as_bool) == Some(true),
                    }),
                    WireBlock::ToolCall => Some(Part::ToolCall {
                        name: field("name").unwrap_or_default(),
                        arguments: block
                            .get("arguments")
                            .map_or(Cow::Borrowed("null"), arguments_json),
                    }),
                    WireBlock::Image | WireBlock::Other => None,
                }
            })
            .collect(),
    }
}
