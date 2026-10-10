//! Port of `test/bedrock-redacted-reasoning.test.ts`. Blobs travel as base64
//! (the wire form) where TS compares `Uint8Array`s.

use base64::engine::general_purpose::STANDARD;
use base64::Engine as _;
use eukhe_pi_ai::api::bedrock_converse_stream::stream;
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, JsonValue, Message, Model, StopReason, TextContent,
    ThinkingContent, ToolCall, ToolResultMessage, Usage, UserContentBlock,
};
use serde_json::json;

use super::support::{
    capture_payload, context_of, event_stream, mock_env, model_from, now, options, user,
    with_base_url, EnvGuard, MockBedrock, Reply,
};

const REDACTED_BASE64: &str = "cnNuXzVaVnJpZjRKMGJYSXFtV2RsZWRqN1FJRmVOaWtSUWJF";

fn gpt_model() -> Model {
    model_from(json!({
        "id": "global.openai.gpt-5.6-terra",
        "name": "GPT-5.6 Terra (Global)",
        "api": "bedrock-converse-stream",
        "provider": "amazon-bedrock",
        "baseUrl": "https://bedrock-runtime.ap-northeast-1.amazonaws.com",
        "reasoning": true,
        "input": ["text"],
        "cost": { "input": 1.25, "output": 10, "cacheRead": 0.125, "cacheWrite": 0 },
        "contextWindow": 400_000,
        "maxTokens": 128_000,
    }))
}

fn redacted_delta(index: u64, bytes: &str) -> JsonValue {
    json!({ "contentBlockDelta": {
        "contentBlockIndex": index,
        "delta": { "reasoningContent": { "redactedContent": bytes } },
    } })
}

/// The frames GPT-5.6 emits: encrypted reasoning, then text.
fn redacted_reasoning_events() -> Vec<JsonValue> {
    vec![
        json!({ "messageStart": { "role": "assistant" } }),
        redacted_delta(0, REDACTED_BASE64),
        json!({ "contentBlockStop": { "contentBlockIndex": 0 } }),
        json!({ "contentBlockDelta": { "contentBlockIndex": 1, "delta": { "text": "done" } } }),
        json!({ "contentBlockStop": { "contentBlockIndex": 1 } }),
        json!({ "messageStop": { "stopReason": "end_turn" } }),
    ]
}

async fn run(items: &[JsonValue]) -> AssistantMessage {
    let server = MockBedrock::start(vec![Reply::events(&[], event_stream(items))]).await;
    let model = with_base_url(&gpt_model(), &server.url);
    let mut options = options(json!({}));
    options.stream.request.env = Some(mock_env());
    stream(&model, &context_of(vec![user("hello")]), options)
        .result()
        .await
}

fn thinking(message: &AssistantMessage) -> ThinkingContent {
    message
        .content
        .iter()
        .find_map(|block| match block {
            AssistantContentBlock::Thinking(thinking) => Some(thinking.clone()),
            _ => None,
        })
        .expect("thinking block")
}

fn assistant(content: Vec<AssistantContentBlock>, stop_reason: StopReason) -> Message {
    Message::Assistant(AssistantMessage {
        content,
        api: "bedrock-converse-stream".into(),
        provider: "amazon-bedrock".into(),
        model: gpt_model().id,
        response_model: None,
        response_id: None,
        provider_thinking_level: None,
        thinking_level: None,
        diagnostics: None,
        usage: Usage::default(),
        stop_reason,
        deferred: None,
        error_message: None,
        raw_stop_reason: None,
        end_turn: None,
        timestamp: now(),
        duration_ms: None,
    })
}

fn redacted_thinking() -> AssistantContentBlock {
    AssistantContentBlock::Thinking(ThinkingContent {
        thinking: String::new(),
        thinking_signature: Some(REDACTED_BASE64.into()),
        redacted: Some(true),
    })
}

#[tokio::test]
async fn does_not_fail_the_stream_when_reasoning_arrives_as_redacted_content() {
    let _env = EnvGuard::new(&[]).await;
    let response = run(&redacted_reasoning_events()).await;
    assert_ne!(
        response.stop_reason,
        StopReason::Error,
        "{:?}",
        response.error_message
    );
    let types: Vec<&str> = response
        .content
        .iter()
        .map(AssistantContentBlock::type_name)
        .collect();
    assert_eq!(types, ["thinking", "text"]);
    assert_eq!(
        response.content[1],
        AssistantContentBlock::Text(TextContent::new("done"))
    );
}

#[tokio::test]
async fn preserves_the_encrypted_reasoning_payload_on_the_assistant_message() {
    let _env = EnvGuard::new(&[]).await;
    let response = run(&redacted_reasoning_events()).await;
    let thinking = thinking(&response);
    assert_eq!(thinking.redacted, Some(true));
    assert_eq!(
        thinking.thinking_signature.as_deref(),
        Some(REDACTED_BASE64)
    );
    // No streaming scratch state survives into the persisted message.
    let serialized = serde_json::to_value(&thinking).expect("serializes");
    assert!(serialized.get("redactedChunks").is_none());
}

#[tokio::test]
async fn encodes_the_payload_when_the_stream_never_sends_content_block_stop() {
    let _env = EnvGuard::new(&[]).await;
    let response = run(&[
        json!({ "messageStart": { "role": "assistant" } }),
        redacted_delta(0, REDACTED_BASE64),
        json!({ "messageStop": { "stopReason": "end_turn" } }),
    ])
    .await;
    let thinking = thinking(&response);
    assert_eq!(
        thinking.thinking_signature.as_deref(),
        Some(REDACTED_BASE64)
    );
    let serialized = serde_json::to_value(&thinking).expect("serializes");
    assert!(serialized.get("redactedChunks").is_none());
    assert!(serialized.get("index").is_none());
}

#[tokio::test]
async fn joins_encrypted_reasoning_split_across_deltas() {
    let _env = EnvGuard::new(&[]).await;
    let bytes = STANDARD.decode(REDACTED_BASE64).expect("base64");
    let (head, tail) = bytes.split_at(7);
    let response = run(&[
        json!({ "messageStart": { "role": "assistant" } }),
        redacted_delta(0, &STANDARD.encode(head)),
        redacted_delta(0, &STANDARD.encode(tail)),
        json!({ "contentBlockStop": { "contentBlockIndex": 0 } }),
        json!({ "messageStop": { "stopReason": "end_turn" } }),
    ])
    .await;
    let thinking = thinking(&response);
    assert_eq!(
        thinking.thinking_signature.as_deref(),
        Some(REDACTED_BASE64)
    );
    // The placeholder marks the block once, not once per delta.
    assert_eq!(thinking.thinking, "[Reasoning redacted]");
}

#[tokio::test]
async fn replays_redacted_reasoning_as_reasoning_content_redacted_content() {
    let payload = capture_payload(
        &gpt_model(),
        vec![
            user("hello"),
            assistant(
                vec![
                    redacted_thinking(),
                    AssistantContentBlock::Text(TextContent::new("done")),
                ],
                StopReason::Stop,
            ),
            user("continue"),
        ],
    )
    .await;
    let assistant = payload["messages"]
        .as_array()
        .expect("messages")
        .iter()
        .find(|message| message["role"] == "assistant")
        .expect("assistant");
    assert_eq!(
        assistant["content"],
        json!([
            { "reasoningContent": { "redactedContent": REDACTED_BASE64 } },
            { "text": "done" },
        ])
    );
}

#[tokio::test]
async fn replays_redacted_reasoning_before_the_tool_use_block_it_belongs_to() {
    let payload = capture_payload(
        &gpt_model(),
        vec![
            user("read the file"),
            assistant(
                vec![
                    redacted_thinking(),
                    AssistantContentBlock::ToolCall(ToolCall {
                        id: "tool-1".into(),
                        name: "read".into(),
                        arguments: json!({ "path": "/tmp/a.txt" })
                            .as_object()
                            .expect("object")
                            .clone(),
                        thought_signature: None,
                        namespace: None,
                    }),
                ],
                StopReason::ToolUse,
            ),
            Message::ToolResult(ToolResultMessage {
                tool_call_id: "tool-1".into(),
                tool_name: "read".into(),
                content: vec![UserContentBlock::Text(TextContent::new("file body"))],
                details: None,
                usage: None,
                nested_calls: None,
                is_error: false,
                timestamp: now(),
                duration_ms: None,
            }),
        ],
    )
    .await;
    let assistant = payload["messages"]
        .as_array()
        .expect("messages")
        .iter()
        .find(|message| message["role"] == "assistant")
        .expect("assistant");
    assert_eq!(
        assistant["content"],
        json!([
            { "reasoningContent": { "redactedContent": REDACTED_BASE64 } },
            { "toolUse": { "toolUseId": "tool-1", "name": "read", "input": { "path": "/tmp/a.txt" } } },
        ])
    );
}
