//! Text helpers over raw wire messages.
//!
//! Message payloads are carried as raw JSON (`serde_json::Value`) so the daemon
//! stays forward-compatible with the agent-loop lane's message evolution while
//! text helpers cover everything the session store and UI need.

use serde_json::Value;

/// Extract the text of a message content field (string or content blocks).
#[must_use]
pub fn message_text(message: &Value) -> String {
    let Some(content) = message.get("content") else {
        return String::new();
    };
    content_to_text(content)
}

#[must_use]
pub fn content_to_text(content: &Value) -> String {
    match content {
        Value::String(s) => s.clone(),
        Value::Array(blocks) => {
            let mut text = String::new();
            let texts = blocks
                .iter()
                .filter(|block| BlockKind::of(block) == BlockKind::Text)
                .filter_map(|block| block.get("text").and_then(Value::as_str));
            for (index, part) in texts.enumerate() {
                if index > 0 {
                    text.push(' ');
                }
                text.push_str(part);
            }
            text
        }
        _ => String::new(),
    }
}

/// A wire message's `role`, parsed off the raw message.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MessageRole {
    User,
    Assistant,
    ToolResult,
    Custom,
    /// Any other role string.
    Other,
}

impl MessageRole {
    #[must_use]
    pub fn parse(role: &str) -> Self {
        match role {
            "user" => Self::User,
            "assistant" => Self::Assistant,
            "toolResult" => Self::ToolResult,
            "custom" => Self::Custom,
            _ => Self::Other,
        }
    }
}

/// The message's role; `None` when `role` is absent or not a string.
pub fn message_role(message: &Value) -> Option<MessageRole> {
    message
        .get("role")
        .and_then(Value::as_str)
        .map(MessageRole::parse)
}

/// A content block's `type`, parsed off the raw block.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BlockKind {
    Text,
    Thinking,
    Image,
    ToolCall,
    /// Any other type, or none.
    Other,
}

impl BlockKind {
    #[must_use]
    pub fn of(block: &Value) -> Self {
        match block.get("type").and_then(Value::as_str) {
            Some("text") => Self::Text,
            Some("thinking") => Self::Thinking,
            Some("image") => Self::Image,
            Some("toolCall") => Self::ToolCall,
            Some(_) | None => Self::Other,
        }
    }
}

pub fn message_timestamp_ms(message: &Value) -> Option<u64> {
    message.get("timestamp").and_then(Value::as_u64)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn extracts_text_from_content_blocks() {
        let message = json!({
            "role": "user",
            "content": [{"type": "text", "text": "hello "}, {"type": "image"}, {"type": "text", "text": "world"}],
        });
        assert_eq!(message_text(&message), "hello  world");
        assert_eq!(message_role(&message), Some(MessageRole::User));
    }
}
