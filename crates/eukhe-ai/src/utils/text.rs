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
    let content = message.content.content_text(DEFAULT_CONTENT_SEPARATOR);
    join_prompt_parts(std::iter::once(content.as_str()).chain(section_texts(message, ..)))
}

/// eukhe addition: [`get_system_message_text`] cut after the section named
/// `breakpoint`: the prefix (the content and the sections up to and
/// including it) and the tail (the sections after it; `""` when none). The
/// two joined with `"\n\n"`, an empty one left out, are the whole prompt.
/// `None` when no section is named `breakpoint`.
#[must_use]
pub fn split_system_message_text(
    message: &SystemMessage,
    breakpoint: &str,
) -> Option<(String, String)> {
    let end = message.sections.as_ref()?.get_index_of(breakpoint)? + 1;
    let content = message.content.content_text(DEFAULT_CONTENT_SEPARATOR);
    Some((
        join_prompt_parts(std::iter::once(content.as_str()).chain(section_texts(message, ..end))),
        join_prompt_parts(section_texts(message, end..)),
    ))
}

/// eukhe addition: the leading system prompt as its shared prefix and the
/// session's tail: [`split_system_message_text`] at `breakpoint`, else the
/// whole prompt and `""`. No message: two empty texts.
#[must_use]
pub fn split_system_prompt(
    message: Option<&SystemMessage>,
    breakpoint: Option<&str>,
) -> (String, String) {
    let Some(message) = message else {
        return (String::new(), String::new());
    };
    breakpoint
        .and_then(|breakpoint| split_system_message_text(message, breakpoint))
        .unwrap_or_else(|| (get_system_message_text(message), String::new()))
}

/// The texts of the sections of `message` in `range` (by position); removed
/// sections have none.
fn section_texts(
    message: &SystemMessage,
    range: impl std::ops::RangeBounds<usize>,
) -> impl Iterator<Item = &str> {
    message
        .sections
        .as_ref()
        .and_then(|sections| sections.get_range(range))
        .into_iter()
        .flat_map(|sections| sections.values())
        .filter_map(Option::as_deref)
}

/// The non-empty parts joined with `"\n\n"`.
fn join_prompt_parts<'a>(parts: impl IntoIterator<Item = &'a str>) -> String {
    let mut text = String::new();
    for part in parts.into_iter().filter(|part| !part.is_empty()) {
        if !text.is_empty() {
            text.push_str("\n\n");
        }
        text.push_str(part);
    }
    text
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

    fn sectioned(content: &str, sections: &[(&str, Option<&str>)]) -> SystemMessage {
        SystemMessage {
            content: SystemContent::Text(content.to_owned()),
            sections: Some(
                sections
                    .iter()
                    .map(|(key, value)| ((*key).to_owned(), value.map(str::to_owned)))
                    .collect(),
            ),
            tools_added: None,
            tools_removed: None,
            timestamp: 0,
        }
    }

    #[test]
    fn splits_the_prompt_after_the_breakpoint_section() {
        let message = sectioned(
            "",
            &[
                ("core", Some("Core.")),
                ("empty", Some("")),
                ("model", Some("Model.")),
                ("cwd", Some("Cwd.")),
                ("gone", None),
                ("date", Some("Date.")),
            ],
        );
        let whole = get_system_message_text(&message);
        assert_eq!(whole, "Core.\n\nModel.\n\nCwd.\n\nDate.");
        let split = split_system_message_text(&message, "model");
        assert_eq!(
            split,
            Some(("Core.\n\nModel.".to_owned(), "Cwd.\n\nDate.".to_owned()))
        );
        let (prefix, tail) = split.expect("split");
        assert_eq!(format!("{prefix}\n\n{tail}"), whole);
        // The content leads the prefix; a breakpoint on the last section
        // leaves no tail; an unknown one does not split.
        let message = sectioned("Base.", &[("core", Some("Core."))]);
        assert_eq!(
            split_system_message_text(&message, "core"),
            Some(("Base.\n\nCore.".to_owned(), String::new()))
        );
        assert_eq!(split_system_message_text(&message, "other"), None);
    }
}
