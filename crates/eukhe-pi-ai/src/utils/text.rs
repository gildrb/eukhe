//! Text extraction from message content and system-message rendering.

use eukhe_types::pi_ai::{ContentBlockText, SystemContent, SystemMessage, UserContent};

/// Content `contentText` accepts: a string or a list of content blocks.
pub trait MessageContent {
    /// The text blocks joined with `separator` (a string is returned as is).
    fn content_text(&self, separator: &str) -> String;
}

impl MessageContent for str {
    fn content_text(&self, _separator: &str) -> String {
        self.to_owned()
    }
}

impl MessageContent for String {
    fn content_text(&self, _separator: &str) -> String {
        self.clone()
    }
}

impl<B: ContentBlockText> MessageContent for [B] {
    fn content_text(&self, separator: &str) -> String {
        let texts: Vec<&str> = self
            .iter()
            .filter_map(ContentBlockText::text_block)
            .collect();
        texts.join(separator)
    }
}

impl<B: ContentBlockText> MessageContent for Vec<B> {
    fn content_text(&self, separator: &str) -> String {
        self.as_slice().content_text(separator)
    }
}

impl MessageContent for UserContent {
    fn content_text(&self, separator: &str) -> String {
        match self {
            Self::Text(text) => text.clone(),
            Self::Blocks(blocks) => blocks.content_text(separator),
        }
    }
}

impl MessageContent for SystemContent {
    fn content_text(&self, separator: &str) -> String {
        match self {
            Self::Text(text) => text.clone(),
            Self::Blocks(blocks) => blocks.content_text(separator),
        }
    }
}

/// The TS default `contentText` separator.
pub const DEFAULT_CONTENT_SEPARATOR: &str = "\n";

/// Extract and join text from message content (TS `contentText(content, separator = "\n")`).
#[must_use]
pub fn content_text<C: MessageContent + ?Sized>(content: &C, separator: &str) -> String {
    content.content_text(separator)
}

/// Render a system message as a complete prompt: its content followed by its sections.
#[must_use]
pub fn get_system_message_text(message: &SystemMessage) -> String {
    let mut parts = vec![message.content.content_text(DEFAULT_CONTENT_SEPARATOR)];
    if let Some(sections) = &message.sections {
        parts.extend(sections.values().flatten().cloned());
    }
    parts.retain(|part| !part.is_empty());
    parts.join("\n\n")
}

/// Render a later system message for APIs that accept system messages
/// mid-conversation. Section changes are framed by name so the model can
/// relate them to the leading prompt. This framing is request-time only.
#[must_use]
pub fn render_system_message_update(message: &SystemMessage) -> String {
    let mut parts = Vec::new();
    let text = message.content.content_text(DEFAULT_CONTENT_SEPARATOR);
    if !text.is_empty() {
        parts.push(text);
    }
    if let Some(sections) = &message.sections {
        for (name, value) in sections {
            parts.push(match value {
                None => format!("Removed system prompt section \"{name}\"."),
                Some(value) => format!("Updated system prompt section \"{name}\":\n\n{value}"),
            });
        }
    }
    parts.join("\n\n")
}

#[cfg(test)]
mod tests {
    use eukhe_types::pi_ai::{
        AssistantContentBlock, ImageContent, JsonObject, TextContent, ThinkingContent, ToolCall,
        UserContentBlock,
    };

    use super::*;

    fn content() -> Vec<AssistantContentBlock> {
        vec![
            AssistantContentBlock::Thinking(ThinkingContent {
                thinking: "reasoning".into(),
                ..ThinkingContent::default()
            }),
            AssistantContentBlock::Text(TextContent::new("first")),
            AssistantContentBlock::ToolCall(ToolCall {
                id: "1".into(),
                name: "read".into(),
                arguments: JsonObject::new(),
                ..ToolCall::default()
            }),
            AssistantContentBlock::Text(TextContent::new("second")),
        ]
    }

    #[test]
    fn extracts_assistant_text_blocks() {
        assert_eq!(content_text(&content(), "\n"), "first\nsecond");
    }

    #[test]
    fn supports_custom_separators() {
        assert_eq!(content_text(&content(), ""), "firstsecond");
    }

    #[test]
    fn passes_string_content_through() {
        assert_eq!(content_text("hello", "\n"), "hello");
    }

    #[test]
    fn extracts_text_from_tool_result_content() {
        let tool_result_content = vec![
            UserContentBlock::Text(TextContent::new("first")),
            UserContentBlock::Image(ImageContent {
                data: "...".into(),
                mime_type: "image/png".into(),
            }),
            UserContentBlock::Text(TextContent::new("second")),
        ];
        assert_eq!(content_text(&tool_result_content, ""), "firstsecond");
    }
}
