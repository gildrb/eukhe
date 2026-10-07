//! Port of `test/bedrock-convert-messages.test.ts`.
//!
//! The TS cases with `{ type: "unknown" }` content blocks cannot be built in
//! Rust: the content unions are closed and reject unknown blocks when a
//! transcript is deserialized. They are replaced by that boundary check plus
//! the matching all-filtered cases. Lone UTF-16 surrogates cannot live in a
//! Rust `String`; those cases sanitize the UTF-16 input first
//! (`sanitize_surrogates_utf16`, what the TS `sanitizeSurrogates` yields).

use eukhe_pi_ai::api::bedrock_converse_stream::stream;
use eukhe_pi_ai::utils::sanitize_unicode::sanitize_surrogates_utf16;
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, CacheRetention, Message, StopReason, TextContent,
    Tool, ToolCall, ToolResultMessage, Usage, UserContent, UserContentBlock, UserMessage,
};
use serde_json::{json, Value};

use super::support::{
    capture_payload, capture_payload_context, context_of, event_stream, mock_env, model_from, now,
    options, sonnet_45_model, user, with_base_url, EnvGuard, MockBedrock, Reply,
};

fn nova_model() -> eukhe_types::pi_ai::Model {
    model_from(json!({
        "id": "amazon.nova-lite-v1:0",
        "name": "Nova Lite",
        "api": "bedrock-converse-stream",
        "provider": "amazon-bedrock",
        "baseUrl": "https://bedrock-runtime.us-east-1.amazonaws.com",
        "reasoning": false,
        "input": ["text", "image"],
        "cost": { "input": 3, "output": 15, "cacheRead": 0.3, "cacheWrite": 3.75 },
        "contextWindow": 200_000,
        "maxTokens": 64_000,
    }))
}

fn assistant(content: Vec<AssistantContentBlock>, stop_reason: StopReason) -> Message {
    Message::Assistant(AssistantMessage {
        content,
        api: "bedrock-converse-stream".into(),
        provider: "amazon-bedrock".into(),
        model: sonnet_45_model().id,
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
    })
}

fn tool_result(id: &str, name: &str, text: &str) -> Message {
    Message::ToolResult(ToolResultMessage {
        tool_call_id: id.into(),
        tool_name: name.into(),
        content: vec![UserContentBlock::Text(TextContent::new(text))],
        details: None,
        usage: None,
        nested_calls: None,
        is_error: false,
        timestamp: now(),
    })
}

fn messages_of(payload: &Value) -> &Vec<Value> {
    payload["messages"].as_array().expect("messages")
}

fn lookup_tool(strict: &str) -> Tool {
    serde_json::from_value(json!({
        "name": "lookup",
        "description": "Look up a value",
        "parameters": {
            "type": "object",
            "properties": { "value": { "type": "string" } },
            "required": ["value"],
        },
        "constrainedSampling": { "type": "json_schema", "strict": strict },
    }))
    .expect("tool")
}

async fn capture_with_tools(model: &eukhe_types::pi_ai::Model, tool: Tool) -> Value {
    capture_payload_context(
        model,
        eukhe_types::pi_ai::Context {
            system_prompt: None,
            messages: vec![user("Use the tool")],
            tools: Some(vec![tool]),
        },
    )
    .await
}

#[tokio::test]
async fn gates_native_strict_tool_use_by_model_capability() {
    let payload = capture_with_tools(&sonnet_45_model(), lookup_tool("require")).await;
    assert_eq!(
        payload["toolConfig"]["tools"][0]["toolSpec"]["strict"],
        json!(true)
    );

    let nova_payload = capture_with_tools(&nova_model(), lookup_tool("prefer")).await;
    assert!(nova_payload["toolConfig"]["tools"][0]["toolSpec"]
        .get("strict")
        .is_none());
}

#[tokio::test]
async fn preserves_empty_property_names_in_streamed_tool_arguments() {
    let _env = EnvGuard::new(&[]).await;
    let server = MockBedrock::start(vec![Reply::events(
        &[],
        event_stream(&[
            json!({ "messageStart": { "role": "assistant" } }),
            json!({ "contentBlockStart": {
                "contentBlockIndex": 0,
                "start": { "toolUse": { "toolUseId": "tool-1", "name": "edit" } },
            } }),
            json!({ "contentBlockDelta": {
                "contentBlockIndex": 0,
                "delta": { "toolUse": {
                    "input": "{\"path\":\"/workspace/foobar/file.js\",\"edits\":[{\"oldText\":\"first\",\"newText\":\"updated first\"},{\"oldText\":\"second\",\"newText\":\"updated second\",\"\":\"\"}]}",
                } },
            } }),
            json!({ "contentBlockStop": { "contentBlockIndex": 0 } }),
            json!({ "messageStop": { "stopReason": "tool_use" } }),
        ]),
    )])
    .await;
    let model = with_base_url(&sonnet_45_model(), &server.url);
    let mut options = options(json!({}));
    options.stream.cache_retention = Some(CacheRetention::None);
    options.stream.request.env = Some(mock_env());

    let message = stream(&model, &context_of(vec![user("Use the tool")]), options)
        .result()
        .await;

    assert_eq!(
        serde_json::to_value(&message.content[0]).expect("serializes"),
        json!({
            "type": "toolCall",
            "id": "tool-1",
            "name": "edit",
            "arguments": {
                "path": "/workspace/foobar/file.js",
                "edits": [
                    { "oldText": "first", "newText": "updated first" },
                    { "oldText": "second", "newText": "updated second", "": "" },
                ],
            },
        })
    );
}

#[test]
fn rejects_unknown_user_and_assistant_content_blocks_at_the_transcript_boundary() {
    // TS skips `{ type: "unknown" }` blocks; Rust transcripts cannot hold them.
    let user_message = serde_json::from_value::<Message>(json!({
        "role": "user",
        "content": [{ "type": "text", "text": "hello" }, { "type": "unknown", "data": "foo" }],
        "timestamp": 1,
    }));
    assert!(user_message.is_err());
    let assistant_message = serde_json::from_value::<Message>(json!({
        "role": "assistant",
        "content": [{ "type": "unknown", "data": "foo" }],
        "api": "bedrock-converse-stream",
        "provider": "amazon-bedrock",
        "model": "m",
        "usage": serde_json::to_value(Usage::default()).expect("usage"),
        "stopReason": "stop",
        "timestamp": 1,
    }));
    assert!(assistant_message.is_err());
}

#[tokio::test]
async fn replaces_user_messages_whose_blocks_are_all_filtered_with_a_placeholder() {
    let payload = capture_payload(
        &sonnet_45_model(),
        vec![Message::User(UserMessage {
            content: UserContent::Blocks(vec![UserContentBlock::Text(TextContent::new(" "))]),
            timestamp: now(),
        })],
    )
    .await;
    let messages = messages_of(&payload);
    assert_eq!(messages.len(), 1);
    assert_eq!(messages[0]["content"], json!([{ "text": "<empty>" }]));
}

#[tokio::test]
async fn replaces_blank_user_string_content_with_a_placeholder() {
    let payload = capture_payload(&sonnet_45_model(), vec![user("   ")]).await;
    let messages = messages_of(&payload);
    assert_eq!(messages.len(), 1);
    assert_eq!(messages[0]["content"], json!([{ "text": "<empty>" }]));
}

#[tokio::test]
async fn filters_blank_user_text_blocks_when_other_content_remains() {
    let payload = capture_payload(
        &sonnet_45_model(),
        vec![Message::User(UserMessage {
            content: UserContent::Blocks(vec![
                UserContentBlock::Text(TextContent::new("")),
                UserContentBlock::Text(TextContent::new("hello")),
            ]),
            timestamp: now(),
        })],
    )
    .await;
    let messages = messages_of(&payload);
    assert_eq!(messages.len(), 1);
    assert_eq!(messages[0]["content"], json!([{ "text": "hello" }]));
}

#[tokio::test]
async fn replaces_user_content_emptied_by_surrogate_sanitization_with_a_placeholder() {
    let text = sanitize_surrogates_utf16(&[0xd83d]);
    let payload = capture_payload(&sonnet_45_model(), vec![user(&text)]).await;
    let messages = messages_of(&payload);
    assert_eq!(messages.len(), 1);
    assert_eq!(messages[0]["content"], json!([{ "text": "<empty>" }]));
}

#[tokio::test]
async fn skips_assistant_text_blocks_emptied_by_surrogate_sanitization() {
    let text = sanitize_surrogates_utf16(&[0xd83d]);
    let payload = capture_payload(
        &sonnet_45_model(),
        vec![assistant(
            vec![AssistantContentBlock::Text(TextContent::new(text))],
            StopReason::Stop,
        )],
    )
    .await;
    assert!(messages_of(&payload).is_empty());
}

#[tokio::test]
async fn replaces_blank_tool_result_content_with_a_placeholder() {
    let payload =
        capture_payload(&sonnet_45_model(), vec![tool_result("tool-1", "tool", "")]).await;
    let messages = messages_of(&payload);
    assert_eq!(messages.len(), 1);
    assert_eq!(
        messages[0]["content"][0]["toolResult"]["content"],
        json!([{ "text": "<empty>" }])
    );
}

#[tokio::test]
async fn skips_assistant_messages_whose_blocks_are_all_filtered() {
    let payload = capture_payload(
        &sonnet_45_model(),
        vec![assistant(
            vec![AssistantContentBlock::Text(TextContent::new("  "))],
            StopReason::Stop,
        )],
    )
    .await;
    assert!(messages_of(&payload).is_empty());
}

#[tokio::test]
async fn removes_empty_property_names_only_from_replayed_bedrock_input() {
    let tool_arguments = json!({
        "path": "/workspace/foobar/file.js",
        "edits": [
            { "oldText": "first", "newText": "updated first" },
            { "oldText": "second", "newText": "updated second", "": "" },
        ],
    });
    let arguments = tool_arguments.as_object().expect("object").clone();
    let messages = vec![
        assistant(
            vec![AssistantContentBlock::ToolCall(ToolCall {
                id: "tool-1".into(),
                name: "edit".into(),
                arguments: arguments.clone(),
                thought_signature: None,
                namespace: None,
            })],
            StopReason::ToolUse,
        ),
        tool_result("tool-1", "edit", "done"),
        user("Continue"),
    ];

    let payload = capture_payload(&sonnet_45_model(), messages.clone()).await;

    assert_eq!(
        messages_of(&payload)[0]["content"][0]["toolUse"]["input"],
        json!({
            "path": "/workspace/foobar/file.js",
            "edits": [
                { "oldText": "first", "newText": "updated first" },
                { "oldText": "second", "newText": "updated second" },
            ],
        })
    );
    let Message::Assistant(original) = &messages[0] else {
        unreachable!("built as assistant");
    };
    let AssistantContentBlock::ToolCall(call) = &original.content[0] else {
        unreachable!("built as tool call");
    };
    assert_eq!(
        call.arguments["edits"][1],
        json!({ "oldText": "second", "newText": "updated second", "": "" })
    );
}
