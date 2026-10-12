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
        Value::Array(blocks) => blocks
            .iter()
            .filter_map(|block| {
                if block.get("type").and_then(Value::as_str) == Some("text") {
                    block.get("text").and_then(Value::as_str)
                } else {
                    None
                }
            })
            .collect::<Vec<_>>()
            .join(" "),
        _ => String::new(),
    }
}

pub fn message_role(message: &Value) -> Option<&str> {
    message.get("role").and_then(Value::as_str)
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
        assert_eq!(message_role(&message), Some("user"));
    }
}
