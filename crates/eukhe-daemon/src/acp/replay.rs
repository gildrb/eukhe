//! `session/load`: a saved session's history as the `session/update`s a
//! client rebuilds its view from, in the shapes a live turn streams.

use std::path::Path;

use serde_json::Value;

use super::types::{AcpSessionUpdate, AcpToolStatus, TextBlock, ToolCallContent};
use super::wire_events::{tool_call_start, tool_result_text};

/// The updates that replay `messages` (the `get_messages` rows, oldest
/// first) of a session that runs in `cwd`.
pub(super) fn replay_updates(messages: &[Value], cwd: &Path) -> Vec<AcpSessionUpdate> {
    messages
        .iter()
        .enumerate()
        .flat_map(|(index, message)| message_updates(index, message, cwd))
        .collect()
}

/// One history row's updates: a user message's text, an assistant
/// message's text, thinking and tool calls, a tool result's end.
fn message_updates(index: usize, message: &Value, cwd: &Path) -> Vec<AcpSessionUpdate> {
    match message.get("role").and_then(Value::as_str) {
        Some("user") => user_texts(message.get("content"))
            .into_iter()
            .map(|text| AcpSessionUpdate::UserMessageChunk {
                content: TextBlock::new(text),
            })
            .collect(),
        Some("assistant") => assistant_updates(index, message, cwd),
        Some("toolResult") => tool_result_update(message).into_iter().collect(),
        Some(_) | None => Vec::new(),
    }
}

/// A user message's text: a string, or its text blocks.
fn user_texts(content: Option<&Value>) -> Vec<String> {
    match content {
        Some(Value::String(text)) => vec![text.clone()],
        Some(Value::Array(blocks)) => blocks
            .iter()
            .filter(|block| block.get("type").and_then(Value::as_str) == Some("text"))
            .filter_map(|block| block.get("text").and_then(Value::as_str))
            .map(str::to_string)
            .collect(),
        Some(_) | None => Vec::new(),
    }
}

fn assistant_updates(index: usize, message: &Value, cwd: &Path) -> Vec<AcpSessionUpdate> {
    let message_id = format!("eukhe-history-{index}");
    message
        .get("content")
        .and_then(Value::as_array)
        .map(|blocks| {
            blocks
                .iter()
                .filter_map(|block| assistant_block(&message_id, block, cwd))
                .collect()
        })
        .unwrap_or_default()
}

fn assistant_block(message_id: &str, block: &Value, cwd: &Path) -> Option<AcpSessionUpdate> {
    let text = |key: &str| {
        block
            .get(key)
            .and_then(Value::as_str)
            .filter(|text| !text.is_empty())
            .map(TextBlock::new)
    };
    match block.get("type").and_then(Value::as_str) {
        Some("text") => Some(AcpSessionUpdate::AgentMessageChunk {
            message_id: message_id.to_string(),
            content: text("text")?,
        }),
        Some("thinking") => Some(AcpSessionUpdate::AgentThoughtChunk {
            message_id: message_id.to_string(),
            content: text("thinking")?,
        }),
        Some("toolCall") => Some(AcpSessionUpdate::ToolCall(tool_call_start(
            block.get("id").and_then(Value::as_str)?.to_string(),
            block
                .get("name")
                .and_then(Value::as_str)
                .unwrap_or_default(),
            block.get("arguments").cloned().unwrap_or(Value::Null),
            cwd,
        ))),
        Some(_) | None => None,
    }
}

/// A tool result: its call's end, with the call's output.
fn tool_result_update(message: &Value) -> Option<AcpSessionUpdate> {
    let failed = message.get("isError").and_then(Value::as_bool) == Some(true);
    Some(AcpSessionUpdate::ToolCallUpdate {
        tool_call_id: message
            .get("toolCallId")
            .and_then(Value::as_str)?
            .to_string(),
        status: Some(if failed {
            AcpToolStatus::Failed
        } else {
            AcpToolStatus::Completed
        }),
        content: tool_result_text(Some(message)).map(|text| vec![ToolCallContent::new(text)]),
        meta: None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn a_history_replays_as_the_live_shapes() {
        let messages = [
            json!({ "role": "user", "content": [{ "type": "text", "text": "List the files" }] }),
            json!({ "role": "assistant", "content": [
                { "type": "thinking", "thinking": "ls" },
                { "type": "toolCall", "id": "c1", "name": "bash", "arguments": { "script": "ls" } },
            ]}),
            json!({ "role": "toolResult", "toolCallId": "c1", "toolName": "bash",
                "content": [{ "type": "text", "text": "a.rs" }], "isError": false }),
            json!({ "role": "assistant", "content": [{ "type": "text", "text": "One file: a.rs" }] }),
            json!({ "role": "compactionSummary", "summary": "s" }),
        ];
        let frames: Vec<Value> = replay_updates(&messages, Path::new("/work"))
            .iter()
            .map(AcpSessionUpdate::to_bare_value)
            .collect();
        assert_eq!(
            frames,
            [
                json!({ "sessionUpdate": "user_message_chunk", "content": { "type": "text", "text": "List the files" } }),
                json!({ "sessionUpdate": "agent_thought_chunk", "messageId": "eukhe-history-1",
                    "content": { "type": "text", "text": "ls" } }),
                json!({ "sessionUpdate": "tool_call", "toolCallId": "c1", "title": "Run `ls`", "name": "bash",
                    "kind": "execute", "status": "in_progress", "rawInput": { "script": "ls", "command": "ls" } }),
                json!({ "sessionUpdate": "tool_call_update", "toolCallId": "c1", "status": "completed",
                    "content": [{ "type": "content", "content": { "type": "text", "text": "a.rs" } }] }),
                json!({ "sessionUpdate": "agent_message_chunk", "messageId": "eukhe-history-3",
                    "content": { "type": "text", "text": "One file: a.rs" } }),
            ]
        );
    }
}
