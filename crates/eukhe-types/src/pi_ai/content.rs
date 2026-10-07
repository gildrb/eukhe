//! Content blocks (`TextContent`, `ThinkingContent`, `ImageContent`,
//! `ToolCall`) and the block unions messages carry.
//!
//! Each block struct serializes its own `type` tag first, like the TS object
//! literals. The unions serialize untagged (the member carries the tag) and
//! deserialize by dispatching on `type`.

use serde::{Deserialize, Deserializer, Serialize};

use super::string_enum::string_enum;
use super::JsonObject;

string_enum! {
    /// eukhe addition: an explicit prompt-cache breakpoint on a content block.
    /// A cacheable request prefix may end right after the marked block;
    /// providers with explicit cache marks (Anthropic `cache_control`, Bedrock
    /// `cachePoint`, `OpenAI` Responses `prompt_cache_breakpoint`) emit one mark
    /// per marked block within their mark budget, others ignore it.
    pub enum CacheBreakpoint {
        /// The provider's default (shortest) cache lifetime.
        Ephemeral => "ephemeral",
    }
}

string_enum! {
    /// Phase of an `OpenAI` Responses message (`TextSignatureV1.phase`).
    pub enum TextSignaturePhase {
        Commentary => "commentary",
        FinalAnswer => "final_answer",
    }
}

/// Structured `textSignature` payload (`v: 1`), stored as JSON in
/// [`TextContent::text_signature`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TextSignatureV1 {
    /// Always `1`.
    pub v: u8,
    pub id: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub phase: Option<TextSignaturePhase>,
}

/// Text content block (`type: "text"`).
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(tag = "type", rename = "text", rename_all = "camelCase")]
pub struct TextContent {
    pub text: String,
    /// Provider message metadata, e.g. the `OpenAI` Responses legacy id string
    /// or a [`TextSignatureV1`] JSON payload.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub text_signature: Option<String>,
    /// eukhe addition: prompt-cache breakpoint after this block (wire key
    /// `cacheBreakpoint`; absent on unmarked blocks).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub cache_breakpoint: Option<CacheBreakpoint>,
}

impl TextContent {
    /// A plain text block.
    #[must_use]
    pub fn new(text: impl Into<String>) -> Self {
        Self {
            text: text.into(),
            text_signature: None,
            cache_breakpoint: None,
        }
    }
}

/// Thinking content block (`type: "thinking"`).
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(tag = "type", rename = "thinking", rename_all = "camelCase")]
pub struct ThinkingContent {
    pub thinking: String,
    /// Provider-specific opaque or serialized reasoning replay data.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub thinking_signature: Option<String>,
    /// When true, the thinking content was redacted by safety filters. The
    /// opaque encrypted payload is stored in `thinking_signature` so it can be
    /// passed back to the API for multi-turn continuity.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub redacted: Option<bool>,
}

/// Image content block (`type: "image"`).
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(tag = "type", rename = "image", rename_all = "camelCase")]
pub struct ImageContent {
    /// Base64-encoded image data.
    pub data: String,
    /// For example `image/jpeg` or `image/png`.
    pub mime_type: String,
}

/// Tool call content block (`type: "toolCall"`).
#[derive(Debug, Clone, PartialEq, Default, Serialize, Deserialize)]
#[serde(tag = "type", rename = "toolCall", rename_all = "camelCase")]
pub struct ToolCall {
    pub id: String,
    pub name: String,
    pub arguments: JsonObject,
    /// Google-specific opaque signature for reusing thought context.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub thought_signature: Option<String>,
    /// `OpenAI` Responses namespace for calls to dynamically loaded or namespaced tools.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub namespace: Option<String>,
}

/// Read access to the text of a block, for `contentText`-style helpers.
pub trait ContentBlockText {
    /// The block's text when it is a text block.
    fn text_block(&self) -> Option<&str>;
    /// The block's `type` tag.
    fn block_type(&self) -> &'static str;
}

/// TS `TextContent | ImageContent` (user, tool-result, and image content).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
#[serde(from = "UserContentBlockWire")]
pub enum UserContentBlock {
    Text(TextContent),
    Image(ImageContent),
}

#[derive(Deserialize)]
#[serde(tag = "type")]
enum UserContentBlockWire {
    #[serde(rename = "text")]
    Text(TextContent),
    #[serde(rename = "image")]
    Image(ImageContent),
}

impl From<UserContentBlockWire> for UserContentBlock {
    fn from(wire: UserContentBlockWire) -> Self {
        match wire {
            UserContentBlockWire::Text(block) => Self::Text(block),
            UserContentBlockWire::Image(block) => Self::Image(block),
        }
    }
}

impl ContentBlockText for UserContentBlock {
    fn text_block(&self) -> Option<&str> {
        match self {
            Self::Text(block) => Some(&block.text),
            Self::Image(_) => None,
        }
    }

    fn block_type(&self) -> &'static str {
        match self {
            Self::Text(_) => "text",
            Self::Image(_) => "image",
        }
    }
}

/// TS `TextContent | ThinkingContent | ToolCall` (assistant content).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(untagged)]
#[serde(from = "AssistantContentBlockWire")]
pub enum AssistantContentBlock {
    Text(TextContent),
    Thinking(ThinkingContent),
    ToolCall(ToolCall),
}

#[derive(Deserialize)]
#[serde(tag = "type")]
enum AssistantContentBlockWire {
    #[serde(rename = "text")]
    Text(TextContent),
    #[serde(rename = "thinking")]
    Thinking(ThinkingContent),
    #[serde(rename = "toolCall")]
    ToolCall(ToolCall),
}

impl From<AssistantContentBlockWire> for AssistantContentBlock {
    fn from(wire: AssistantContentBlockWire) -> Self {
        match wire {
            AssistantContentBlockWire::Text(block) => Self::Text(block),
            AssistantContentBlockWire::Thinking(block) => Self::Thinking(block),
            AssistantContentBlockWire::ToolCall(block) => Self::ToolCall(block),
        }
    }
}

impl AssistantContentBlock {
    /// The block's `type` tag.
    #[must_use]
    pub const fn type_name(&self) -> &'static str {
        match self {
            Self::Text(_) => "text",
            Self::Thinking(_) => "thinking",
            Self::ToolCall(_) => "toolCall",
        }
    }
}

impl ContentBlockText for AssistantContentBlock {
    fn text_block(&self) -> Option<&str> {
        match self {
            Self::Text(block) => Some(&block.text),
            Self::Thinking(_) | Self::ToolCall(_) => None,
        }
    }

    fn block_type(&self) -> &'static str {
        self.type_name()
    }
}

impl ContentBlockText for TextContent {
    fn text_block(&self) -> Option<&str> {
        Some(&self.text)
    }

    fn block_type(&self) -> &'static str {
        "text"
    }
}

/// TS `string | (TextContent | ImageContent)[]` (user message content).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum UserContent {
    Text(String),
    Blocks(Vec<UserContentBlock>),
}

impl Default for UserContent {
    /// The empty block list that lax deserialization uses for null/missing content.
    fn default() -> Self {
        Self::Blocks(Vec::new())
    }
}

impl From<String> for UserContent {
    fn from(text: String) -> Self {
        Self::Text(text)
    }
}

impl From<&str> for UserContent {
    fn from(text: &str) -> Self {
        Self::Text(text.to_owned())
    }
}

impl From<Vec<UserContentBlock>> for UserContent {
    fn from(blocks: Vec<UserContentBlock>) -> Self {
        Self::Blocks(blocks)
    }
}

/// TS `string | TextContent[]` (system message content).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum SystemContent {
    Text(String),
    Blocks(Vec<TextContent>),
}

impl Default for SystemContent {
    fn default() -> Self {
        Self::Text(String::new())
    }
}

impl From<String> for SystemContent {
    fn from(text: String) -> Self {
        Self::Text(text)
    }
}

impl From<&str> for SystemContent {
    fn from(text: &str) -> Self {
        Self::Text(text.to_owned())
    }
}

/// Lax content deserialization: untyped callers (custom tools, hand-built
/// histories, old session files) can write `null` content; it reads as the
/// type's default (an empty block list), like `transformMessages`.
pub(crate) fn null_as_default<'de, D, T>(deserializer: D) -> Result<T, D::Error>
where
    D: Deserializer<'de>,
    T: Deserialize<'de> + Default,
{
    Ok(Option::<T>::deserialize(deserializer)?.unwrap_or_default())
}
