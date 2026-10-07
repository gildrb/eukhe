//! Port of `test/transform-messages-copilot-openai-to-anthropic.test.ts`.

mod anthropic_support;

use anthropic_support::{assert_match_object, model};
use eukhe_pi_ai::api::transform_messages::transform_messages;
use eukhe_types::pi_ai::{AssistantMessage, JsonValue, Message, Model};
use serde_json::json;

/// Normalize function matching what anthropic.ts uses.
fn anthropic_normalize_tool_call_id(
    id: &str,
    _model: &Model,
    _source: &AssistantMessage,
) -> String {
    id.chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '_' || c == '-' {
                c
            } else {
                '_'
            }
        })
        .take(64)
        .collect()
}

fn make_copilot_claude_model() -> Model {
    model(&json!({
        "id": "claude-sonnet-4.6",
        "name": "Claude Sonnet 4.6",
        "provider": "github-copilot",
        "baseUrl": "https://api.individual.githubcopilot.com",
        "reasoning": true,
        "input": ["text", "image"],
        "contextWindow": 128_000,
        "maxTokens": 16000,
    }))
}

fn usage() -> JsonValue {
    json!({
        "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
    })
}

fn make_assistant_message(content: &JsonValue) -> JsonValue {
    json!({
        "role": "assistant",
        "content": content,
        "api": "openai-responses",
        "provider": "github-copilot",
        "model": "gpt-5",
        "usage": usage(),
        "stopReason": "toolUse",
        "timestamp": 1,
    })
}

fn transform(messages: &JsonValue) -> Vec<JsonValue> {
    let messages: Vec<Message> = serde_json::from_value(messages.clone()).expect("messages");
    transform_messages(
        &messages,
        &make_copilot_claude_model(),
        Some(&anthropic_normalize_tool_call_id),
    )
    .iter()
    .map(|message| serde_json::to_value(message).expect("message json"))
    .collect()
}

fn blocks_of_type<'a>(message: &'a JsonValue, kind: &str) -> Vec<&'a JsonValue> {
    message["content"]
        .as_array()
        .expect("content")
        .iter()
        .filter(|block| block["type"] == kind)
        .collect()
}

fn find_assistant(result: &[JsonValue]) -> &JsonValue {
    result
        .iter()
        .find(|message| message["role"] == "assistant")
        .expect("assistant")
}

#[test]
fn converts_thinking_blocks_to_plain_text_when_source_model_differs() {
    let result = transform(&json!([
        { "role": "user", "content": "hello", "timestamp": 1 },
        {
            "role": "assistant",
            "content": [
                { "type": "thinking", "thinking": "Let me think about this...", "thinkingSignature": "reasoning_content" },
                { "type": "text", "text": "Hi there!" },
            ],
            "api": "openai-completions",
            "provider": "github-copilot",
            "model": "gpt-4o",
            "usage": usage(),
            "stopReason": "stop",
            "timestamp": 1,
        },
    ]));
    let assistant = find_assistant(&result);

    // Thinking block should be converted to text since models differ
    assert_eq!(blocks_of_type(assistant, "thinking").len(), 0);
    assert!(blocks_of_type(assistant, "text").len() >= 2);
}

#[test]
fn removes_thought_signature_from_tool_calls_when_migrating_between_models() {
    let thought_signature =
        json!({ "type": "reasoning.encrypted", "id": "call_123", "data": "encrypted" }).to_string();
    let result = transform(&json!([
        { "role": "user", "content": "run a command", "timestamp": 1 },
        make_assistant_message(&json!([{
            "type": "toolCall",
            "id": "call_123",
            "name": "bash",
            "arguments": { "command": "ls" },
            "thoughtSignature": thought_signature,
        }])),
        {
            "role": "toolResult",
            "toolCallId": "call_123",
            "toolName": "bash",
            "content": [{ "type": "text", "text": "output" }],
            "isError": false,
            "timestamp": 1,
        },
    ]));
    let assistant = find_assistant(&result);
    let tool_call = blocks_of_type(assistant, "toolCall")[0];

    assert_eq!(tool_call.get("thoughtSignature"), None);
}

#[test]
fn adds_synthetic_tool_results_for_trailing_orphaned_tool_calls() {
    let result = transform(&json!([
        { "role": "user", "content": "read the file", "timestamp": 1 },
        make_assistant_message(&json!([{
            "type": "toolCall",
            "id": "call_123|fc_123",
            "name": "read",
            "arguments": { "path": "README.md" },
        }])),
    ]));
    let last_message = result.last().expect("last message");

    assert_match_object(
        last_message,
        &json!({
            "role": "toolResult",
            "toolCallId": "call_123_fc_123",
            "toolName": "read",
            "isError": true,
            "content": [{ "type": "text", "text": "No result provided" }],
        }),
    );
}

#[test]
fn adds_synthetic_results_only_for_trailing_tool_calls_that_are_still_missing_results() {
    let result = transform(&json!([
        { "role": "user", "content": "run commands", "timestamp": 1 },
        make_assistant_message(&json!([
            { "type": "toolCall", "id": "call_1|fc_1", "name": "read", "arguments": { "path": "README.md" } },
            { "type": "toolCall", "id": "call_2|fc_2", "name": "bash", "arguments": { "command": "pwd" } },
        ])),
        {
            "role": "toolResult",
            "toolCallId": "call_1|fc_1",
            "toolName": "read",
            "content": [{ "type": "text", "text": "done" }],
            "isError": false,
            "timestamp": 1,
        },
    ]));
    let synthetic_results: Vec<&JsonValue> = result
        .iter()
        .filter(|message| message["role"] == "toolResult" && message["isError"] == true)
        .collect();

    assert_eq!(synthetic_results.len(), 1);
    assert_match_object(
        synthetic_results[0],
        &json!({
            "role": "toolResult",
            "toolCallId": "call_2_fc_2",
            "toolName": "bash",
            "content": [{ "type": "text", "text": "No result provided" }],
        }),
    );
}
