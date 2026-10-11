//! Port of `openai-completions-tool-result-images.test.ts`.

use serde_json::{json, Value as JsonValue};

use super::super::compat::{get_compat, ResolvedCompat};
use super::super::convert::{convert_messages, ConvertCompletionsMessagesOptions};
use super::support::{context, model};
use crate::providers::all::get_builtin_model;
use crate::types::{Model, TranscriptContext};

fn empty_usage() -> JsonValue {
    json!({
        "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
    })
}

/// `{ ...getModel("openai", "gpt-4o-mini") minus compat, api: "openai-completions", input: ["text", "image"] }`.
fn image_model() -> Model {
    let base = get_builtin_model("openai", "gpt-4o-mini").expect("openai/gpt-4o-mini in catalog");
    let mut value = serde_json::to_value(&base).expect("serialize model");
    let object = value.as_object_mut().expect("model JSON object");
    object.remove("compat");
    object.insert("api".to_owned(), json!("openai-completions"));
    object.insert("input".to_owned(), json!(["text", "image"]));
    model(value)
}

/// The TS test's fully specified `compat` record, resolved: the record is
/// attached as the model's explicit compat so every field overrides detection.
fn test_compat(base: &Model) -> ResolvedCompat {
    let mut value = serde_json::to_value(base).expect("serialize model");
    value["compat"] = json!({
        "supportsStore": true,
        "supportsDeveloperRole": true,
        "supportsReasoningEffort": true,
        "supportsUsageInStreaming": true,
        "supportsFinishReason": true,
        "maxTokensField": "max_completion_tokens",
        "requiresToolResultName": false,
        "requiresAssistantAfterToolResult": false,
        "requiresThinkingAsText": false,
        "requiresReasoningContentOnAssistantMessages": false,
        "thinkingFormat": "openai",
        "openRouterRouting": {},
        "vercelGatewayRouting": {},
        "chatTemplateKwargs": {},
        "chatTemplateArgs": {},
        "zaiToolStream": false,
        "supportsThinkingTokenBudget": false,
        "supportsStrictMode": true,
        "supportsOpenAIGrammarTools": false,
        "supportsMidConvoSystemMessages": false,
        "supportsMidConvoToolAdditions": false,
        "cacheControlFormat": "anthropic",
        "sendSessionAffinityHeaders": false,
        "sessionAffinityFormat": "openai",
        "supportsLongCacheRetention": true,
    });
    get_compat(&model(value))
}

fn convert(model: &Model, context: &TranscriptContext) -> Vec<JsonValue> {
    convert_messages(
        model,
        context,
        &test_compat(model),
        &ConvertCompletionsMessagesOptions::default(),
    )
    .unwrap_or_else(|error| panic!("convert_messages failed: {error:?}"))
}

fn build_tool_result(tool_call_id: &str, timestamp: i64) -> JsonValue {
    json!({
        "role": "toolResult",
        "toolCallId": tool_call_id,
        "toolName": "read",
        "content": [
            { "type": "text", "text": "Read image file [image/png]" },
            { "type": "image", "data": "ZmFrZQ==", "mimeType": "image/png" },
        ],
        "isError": false,
        "timestamp": timestamp,
    })
}

fn build_empty_tool_result(tool_call_id: &str, timestamp: i64) -> JsonValue {
    json!({
        "role": "toolResult",
        "toolCallId": tool_call_id,
        "toolName": "bash",
        "content": [{ "type": "text", "text": "" }],
        "isError": false,
        "timestamp": timestamp,
    })
}

fn assistant(model: &Model, content: &JsonValue, timestamp: i64) -> JsonValue {
    let model = serde_json::to_value(model).expect("serialize model");
    json!({
        "role": "assistant",
        "content": content,
        "api": model["api"],
        "provider": model["provider"],
        "model": model["id"],
        "usage": empty_usage(),
        "stopReason": "toolUse",
        "timestamp": timestamp,
    })
}

const NOW: i64 = 1_700_000_000_000;

// Regression test for https://github.com/earendil-works/pi/issues/9797
#[test]
fn omits_empty_text_parts_from_user_messages_with_images() {
    let model = image_model();
    let ctx = context(json!({
        "messages": [{
            "role": "user",
            "content": [
                { "type": "text", "text": "" },
                { "type": "image", "data": "ZmFrZQ==", "mimeType": "image/png" },
            ],
            "timestamp": NOW,
        }],
    }));

    assert_eq!(
        convert(&model, &ctx),
        vec![json!({
            "role": "user",
            "content": [{ "type": "image_url", "image_url": { "url": "data:image/png;base64,ZmFrZQ==" } }],
        })]
    );
}

#[test]
fn batches_tool_result_images_after_consecutive_tool_results() {
    let model = image_model();
    let assistant_message = assistant(
        &model,
        &json!([
            { "type": "toolCall", "id": "tool-1", "name": "read", "arguments": { "path": "img-1.png" } },
            { "type": "toolCall", "id": "tool-2", "name": "read", "arguments": { "path": "img-2.png" } },
        ]),
        NOW,
    );
    let ctx = context(json!({
        "messages": [
            { "role": "user", "content": "Read the images", "timestamp": NOW - 2 },
            assistant_message,
            build_tool_result("tool-1", NOW + 1),
            build_tool_result("tool-2", NOW + 2),
        ],
    }));

    let messages = convert(&model, &ctx);
    let roles: Vec<&JsonValue> = messages.iter().map(|message| &message["role"]).collect();
    assert_eq!(
        roles,
        [
            &json!("user"),
            &json!("assistant"),
            &json!("tool"),
            &json!("tool"),
            &json!("user")
        ]
    );

    let image_message = messages.last().expect("image message");
    assert_eq!(image_message["role"], json!("user"));
    let parts = image_message["content"]
        .as_array()
        .expect("image message content is an array");
    let image_parts = parts
        .iter()
        .filter(|part| part.get("type") == Some(&json!("image_url")))
        .count();
    assert_eq!(image_parts, 2);
}

#[test]
fn uses_no_tool_output_placeholder_for_empty_tool_results_without_images() {
    let model = image_model();
    let assistant_message = assistant(
        &model,
        &json!([{ "type": "toolCall", "id": "tool-1", "name": "bash", "arguments": { "command": "true" } }]),
        NOW,
    );
    let ctx = context(json!({
        "messages": [
            { "role": "user", "content": "Run the command", "timestamp": NOW - 1 },
            assistant_message,
            build_empty_tool_result("tool-1", NOW + 1),
        ],
    }));

    let messages = convert(&model, &ctx);
    let tool_message = messages
        .iter()
        .find(|message| message["role"] == json!("tool"))
        .expect("a tool message");
    let content = tool_message["content"]
        .as_str()
        .expect("string tool content");
    assert_eq!(content, "(no tool output)");
    assert!(!content.contains("see attached image"));
}
