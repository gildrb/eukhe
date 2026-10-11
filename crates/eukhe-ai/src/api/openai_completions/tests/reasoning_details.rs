//! Port of `openai-completions-reasoning-details.test.ts`.
//!
//! The TS fake client shifts one chunk set per `create` call; here each
//! request runs against its own recording `fetch` with the next chunk set.

use serde_json::{json, Value as JsonValue};

use super::support::{context, model, run_with_chunks};
use crate::api::openai_completions::OpenAICompletionsOptions;
use crate::types::{AssistantMessage, Model};

fn reasoning_detail() -> JsonValue {
    json!({ "type": "reasoning.encrypted", "id": "call_1", "data": "encrypted-signature" })
}

fn signed_reasoning_text_detail() -> JsonValue {
    json!({
        "type": "reasoning.text",
        "text": "I should call the read tool.",
        "signature": "sha256:signed-text",
        "id": "reasoning-text-1",
        "format": "anthropic-claude-v1",
        "index": 0,
    })
}

fn reasoning_summary_detail() -> JsonValue {
    json!({
        "type": "reasoning.summary",
        "summary": "Decided to inspect the requested file.",
        "id": "reasoning-summary-1",
        "format": "anthropic-claude-v1",
        "index": 1,
    })
}

/// `{ name: "read", description: "Read a file", parameters: Type.Object({ path: Type.String() }) }`.
fn read_tool() -> JsonValue {
    json!({
        "name": "read",
        "description": "Read a file",
        "parameters": {
            "type": "object",
            "properties": { "path": { "type": "string" } },
            "required": ["path"],
        },
    })
}

fn test_model() -> Model {
    model(json!({
        "id": "google/gemini-test",
        "name": "Gemini Test",
        "api": "openai-completions",
        "provider": "openrouter",
        "baseUrl": "https://openrouter.ai/api/v1",
        "reasoning": true,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 100_000,
        "maxTokens": 4096,
    }))
}

fn chunk(delta: &JsonValue, finish_reason: Option<&str>) -> JsonValue {
    json!({
        "id": "chatcmpl-test",
        "model": "google/gemini-test",
        "choices": [{ "index": 0, "delta": delta, "finish_reason": finish_reason }],
    })
}

fn tool_call_chunk() -> JsonValue {
    chunk(
        &json!({
            "tool_calls": [{
                "index": 0,
                "id": "call_1",
                "type": "function",
                "function": { "name": "read", "arguments": "{\"path\":\"README.md\"}" },
            }],
        }),
        None,
    )
}

fn replay_chunks() -> Vec<JsonValue> {
    vec![
        chunk(&json!({ "content": "ok" }), None),
        chunk(&json!({}), Some("stop")),
    ]
}

/// `streamOpenAICompletions(model(), normalizeContext({ messages, tools: [readTool] }), { apiKey: "test" })`:
/// the request payload and the final message.
async fn run_stream(
    messages: &[JsonValue],
    chunks: Vec<JsonValue>,
) -> (JsonValue, AssistantMessage) {
    let ctx = context(json!({ "messages": messages, "tools": [read_tool()] }));
    let (request, _, message) = run_with_chunks(
        &test_model(),
        &ctx,
        OpenAICompletionsOptions::default(),
        chunks,
    )
    .await;
    let payload = request
        .unwrap_or_else(|| panic!("no request was sent: {:?}", message.error_message))
        .json();
    (payload, message)
}

fn message_json(message: &AssistantMessage) -> JsonValue {
    serde_json::to_value(message).expect("serialize assistant message")
}

/// The first content block of `type`, as JSON.
fn find_block(message: &JsonValue, block_type: &str) -> Option<JsonValue> {
    message["content"]
        .as_array()?
        .iter()
        .find(|block| block["type"] == json!(block_type))
        .cloned()
}

fn assistant_payload(payload: &JsonValue) -> Option<&JsonValue> {
    payload["messages"]
        .as_array()?
        .iter()
        .find(|message| message["role"] == json!("assistant"))
}

fn json_string(value: &JsonValue) -> String {
    serde_json::to_string(value).expect("serialize JSON")
}

#[tokio::test]
async fn preserves_reasoning_details_in_the_thinking_signature() {
    let (_, assistant_message) = run_stream(
        &[],
        vec![
            chunk(&json!({ "reasoning_details": [reasoning_detail()] }), None),
            tool_call_chunk(),
            chunk(&json!({}), Some("tool_calls")),
        ],
    )
    .await;
    let assistant = message_json(&assistant_message);
    assert_eq!(
        find_block(&assistant, "thinking"),
        Some(json!({
            "type": "thinking",
            "thinking": "",
            "thinkingSignature": json_string(&json!([reasoning_detail()])),
        }))
    );
    assert_eq!(
        find_block(&assistant, "toolCall"),
        Some(json!({
            "type": "toolCall",
            "id": "call_1",
            "name": "read",
            "arguments": { "path": "README.md" },
        }))
    );

    let (payload, _) = run_stream(&[assistant], replay_chunks()).await;

    assert_eq!(
        assistant_payload(&payload).and_then(|message| message.get("reasoning_details")),
        Some(&json!([reasoning_detail()]))
    );
}

#[tokio::test]
async fn falls_back_to_encrypted_tool_call_signatures_for_older_stored_assistant_messages() {
    let (_, assistant_message) = run_stream(
        &[],
        vec![
            chunk(&json!({ "reasoning_details": [reasoning_detail()] }), None),
            tool_call_chunk(),
            chunk(&json!({}), Some("tool_calls")),
        ],
    )
    .await;
    let mut assistant = message_json(&assistant_message);
    let content = assistant["content"]
        .as_array_mut()
        .expect("assistant content array");
    content.retain(|block| block["type"] != json!("thinking"));
    let tool_call = content
        .iter_mut()
        .find(|block| block["type"] == json!("toolCall"))
        .expect("Expected tool call");
    tool_call["thoughtSignature"] = json!(json_string(&reasoning_detail()));

    let (payload, _) = run_stream(&[assistant], replay_chunks()).await;

    assert_eq!(
        assistant_payload(&payload).and_then(|message| message.get("reasoning_details")),
        Some(&json!([reasoning_detail()]))
    );
}

#[tokio::test]
async fn preserves_signed_text_and_summary_reasoning_details_in_their_original_sequence() {
    let signed = signed_reasoning_text_detail();
    let (_, assistant_message) = run_stream(
        &[],
        vec![
            chunk(
                &json!({ "reasoning": signed["text"], "reasoning_details": [signed] }),
                None,
            ),
            chunk(
                &json!({ "reasoning_details": [reasoning_detail(), reasoning_summary_detail()] }),
                None,
            ),
            tool_call_chunk(),
            chunk(&json!({}), Some("tool_calls")),
        ],
    )
    .await;
    let expected_reasoning_details =
        json!([signed, reasoning_detail(), reasoning_summary_detail()]);
    let assistant = message_json(&assistant_message);
    assert_eq!(
        find_block(&assistant, "thinking"),
        Some(json!({
            "type": "thinking",
            "thinking": signed["text"],
            "thinkingSignature": json_string(&expected_reasoning_details),
        }))
    );

    let (payload, _) = run_stream(&[assistant], replay_chunks()).await;

    let payload = assistant_payload(&payload).expect("assistant payload message");
    assert_eq!(
        payload.get("reasoning_details"),
        Some(&expected_reasoning_details)
    );
    assert_eq!(payload.get("reasoning"), None);
}

#[tokio::test]
async fn merges_consecutive_text_and_summary_reasoning_details_deltas_before_replay() {
    let text_delta = json!({ "type": "reasoning.text", "text": "The", "index": 0 });
    let text_delta_with_signature = json!({
        "type": "reasoning.text",
        "text": " user wants the time.",
        "signature": "sha256:text-signature",
        "format": "openai-responses-v1",
        "index": 0,
    });
    let summary_delta = json!({ "type": "reasoning.summary", "summary": "Looked", "index": 0 });
    let summary_delta_with_format = json!({
        "type": "reasoning.summary",
        "summary": " up time.",
        "format": "openai-responses-v1",
        "index": 0,
    });
    let later_summary_delta = json!({
        "type": "reasoning.summary",
        "summary": "After encrypted block.",
        "format": "openai-responses-v1",
        "index": 0,
    });
    let expected_reasoning_details = json!([
        {
            "type": "reasoning.text",
            "text": "The user wants the time.",
            "index": 0,
            "signature": "sha256:text-signature",
            "format": "openai-responses-v1",
        },
        {
            "type": "reasoning.summary",
            "summary": "Looked up time.",
            "index": 0,
            "format": "openai-responses-v1",
        },
        reasoning_detail(),
        later_summary_delta,
    ]);

    let (_, assistant_message) = run_stream(
        &[],
        vec![
            chunk(&json!({ "reasoning_details": [text_delta] }), None),
            chunk(
                &json!({ "reasoning_details": [text_delta_with_signature] }),
                None,
            ),
            chunk(&json!({ "reasoning_details": [summary_delta] }), None),
            chunk(
                &json!({ "reasoning_details": [summary_delta_with_format] }),
                None,
            ),
            chunk(&json!({ "reasoning_details": [reasoning_detail()] }), None),
            chunk(&json!({ "reasoning_details": [later_summary_delta] }), None),
            tool_call_chunk(),
            chunk(&json!({}), Some("tool_calls")),
        ],
    )
    .await;
    let assistant = message_json(&assistant_message);
    // TS compares `JSON.stringify(expected)`: key order is part of the assertion.
    assert_eq!(
        find_block(&assistant, "thinking"),
        Some(json!({
            "type": "thinking",
            "thinking": "",
            "thinkingSignature": json_string(&expected_reasoning_details),
        }))
    );

    let (payload, _) = run_stream(&[assistant], replay_chunks()).await;

    assert_eq!(
        assistant_payload(&payload).and_then(|message| message.get("reasoning_details")),
        Some(&expected_reasoning_details)
    );
}
