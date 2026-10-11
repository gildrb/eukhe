//! Port of `openai-completions-cache-control-format.test.ts`.

use serde_json::json;

use super::support::{capture_payload, context, model};
use crate::api::openai_completions::OpenAICompletionsOptions;
use crate::providers::all::get_builtin_model;
use crate::types::{CacheRetention, JsonValue, Model, StreamOptions};

fn custom_qwen() -> Model {
    model(json!({
        "id": "custom-qwen",
        "name": "Custom Qwen",
        "api": "openai-completions",
        "provider": "openrouter",
        "baseUrl": "https://example.com/v1",
        "reasoning": true,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 128_000,
        "maxTokens": 32_000,
        "compat": { "cacheControlFormat": "anthropic" },
    }))
}

fn fable_batch() -> Model {
    get_builtin_model("openrouter", "anthropic/claude-fable-5.1:batch").expect("catalog model")
}

/// TS `capturePayload(model, options, messages)`: system prompt, one `read`
/// tool, and `messages` (default: one user "Hello").
async fn capture(
    model: &Model,
    cache_retention: Option<CacheRetention>,
    messages: Option<JsonValue>,
) -> JsonValue {
    let messages =
        messages.unwrap_or_else(|| json!([{ "role": "user", "content": "Hello", "timestamp": 1 }]));
    let ctx = context(json!({
        "systemPrompt": "System prompt",
        "messages": messages,
        "tools": [{
            "name": "read",
            "description": "Read a file",
            "parameters": {
                "type": "object",
                "properties": { "path": { "type": "string" } },
                "required": ["path"],
            },
        }],
    }));
    let options = OpenAICompletionsOptions {
        stream: StreamOptions {
            cache_retention,
            ..StreamOptions::default()
        },
        ..OpenAICompletionsOptions::default()
    };
    capture_payload(model, &ctx, options).await
}

fn instruction_message(params: &JsonValue) -> Option<&JsonValue> {
    params["messages"]
        .as_array()?
        .iter()
        .find(|message| matches!(message["role"].as_str(), Some("system" | "developer")))
}

fn last_message(params: &JsonValue) -> &JsonValue {
    params["messages"]
        .as_array()
        .and_then(|messages| messages.last())
        .expect("at least one message")
}

fn expect_anthropic_cache_markers(params: &JsonValue) {
    let instruction = instruction_message(params).expect("instruction message");
    assert!(instruction["content"].is_array(), "{instruction}");
    assert_eq!(
        instruction["content"][0]["cache_control"],
        json!({ "type": "ephemeral" })
    );

    let tools = params["tools"].as_array().expect("tools");
    assert_eq!(tools.len(), 1);
    assert_eq!(tools[0]["cache_control"], json!({ "type": "ephemeral" }));

    let last = last_message(params);
    assert_eq!(last["role"], "user");
    assert!(last["content"].is_array(), "{last}");
    assert_eq!(
        last["content"][0]["cache_control"],
        json!({ "type": "ephemeral" })
    );
}

#[tokio::test]
async fn applies_anthropic_style_cache_markers_when_model_compat_enables_them() {
    let params = capture(&custom_qwen(), None, None).await;
    expect_anthropic_cache_markers(&params);
}

#[tokio::test]
async fn preserves_anthropic_style_cache_markers_for_openrouter_anthropic_batch_aliases() {
    let params = capture(&fable_batch(), None, None).await;
    expect_anthropic_cache_markers(&params);
}

#[tokio::test]
async fn moves_the_conversation_cache_marker_to_a_tool_result() {
    let model = fable_batch();
    let params = capture(
        &model,
        None,
        Some(json!([
            { "role": "user", "content": "Read the file", "timestamp": 1 },
            {
                "role": "assistant",
                "content": [{ "type": "toolCall", "id": "call_1", "name": "read", "arguments": { "path": "README.md" } }],
                "api": "openai-completions",
                "provider": "openrouter",
                "model": model.id,
                "usage": {
                    "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
                    "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
                },
                "stopReason": "toolUse",
                "timestamp": 1,
            },
            {
                "role": "toolResult",
                "toolCallId": "call_1",
                "toolName": "read",
                "content": [{ "type": "text", "text": "file contents" }],
                "isError": false,
                "timestamp": 1,
            },
        ])),
    )
    .await;

    let user = params["messages"]
        .as_array()
        .and_then(|messages| messages.iter().find(|message| message["role"] == "user"))
        .expect("user message");
    assert_eq!(user["content"], "Read the file");

    let tool = last_message(&params);
    assert_eq!(tool["role"], "tool");
    assert!(tool["content"].is_array(), "{tool}");
    assert_eq!(
        tool["content"][0]["cache_control"],
        json!({ "type": "ephemeral" })
    );
}

#[tokio::test]
async fn omits_anthropic_style_cache_markers_when_cache_retention_is_none() {
    let params = capture(&custom_qwen(), Some(CacheRetention::None), None).await;
    let instruction = instruction_message(&params).expect("instruction message");

    assert!(!instruction["content"].is_array(), "{instruction}");
    assert!(params["tools"][0].get("cache_control").is_none());
    assert!(last_message(&params)["content"].is_string());
}
