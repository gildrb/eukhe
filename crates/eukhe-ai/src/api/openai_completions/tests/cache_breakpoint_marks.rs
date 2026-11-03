//! eukhe addition: explicit prompt-cache breakpoints
//! (`TextContent::cache_breakpoint`) on Anthropic-format `cache_control`
//! models. Marked user and assistant text blocks carry `cache_control`, the
//! optional system and tool marks share the four-mark budget, and
//! over-marked transcripts fail before a request is sent.

use serde_json::json;

use super::super::compat::get_compat;
use super::super::convert::{convert_messages, ConvertCompletionsMessagesOptions};
use super::support::{collect, context, options_with_fetch, sse_fetch, stop_chunks, test_model};
use crate::api::openai_completions::stream_with_options;
use crate::api::system_one_shared::test_fetch::recorded;
use crate::types::{AssistantMessageEvent, JsonValue, Model, StopReason, TranscriptContext};

fn openrouter_anthropic() -> Model {
    test_model(json!({
        "id": "anthropic/claude-sonnet-4",
        "name": "Anthropic: Claude Sonnet 4",
        "provider": "openrouter",
        "baseUrl": "https://openrouter.ai/api/v1",
        "compat": { "cacheControlFormat": "anthropic" },
    }))
}

/// System prompt, one `read` tool, and one user message with `blocks`.
fn marked_context(blocks: &JsonValue) -> TranscriptContext {
    context(json!({
        "systemPrompt": "System prompt",
        "messages": [{ "role": "user", "content": blocks, "timestamp": 1 }],
        "tools": [{
            "name": "read",
            "description": "Read a file",
            "parameters": {
                "type": "object",
                "properties": { "path": { "type": "string" } },
                "required": ["path"],
            },
        }],
    }))
}

/// A user turn, a same-model assistant answer with `content`, then the user
/// turn that continues it.
fn assistant_context(content: &JsonValue) -> TranscriptContext {
    context(json!({
        "messages": [
            { "role": "user", "content": "question", "timestamp": 1 },
            {
                "role": "assistant",
                "content": content,
                "api": "openai-completions",
                "provider": "openrouter",
                "model": "anthropic/claude-sonnet-4",
                "usage": {
                    "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
                    "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
                },
                "stopReason": "stop",
                "timestamp": 2,
            },
            { "role": "user", "content": "review", "timestamp": 3 },
        ],
    }))
}

fn marked(text: &str) -> JsonValue {
    json!({ "type": "text", "text": text, "cacheBreakpoint": "ephemeral" })
}

fn plain(text: &str) -> JsonValue {
    json!({ "type": "text", "text": text })
}

async fn payload_for(context: &TranscriptContext) -> JsonValue {
    let (fetch, requests) = sse_fetch(stop_chunks());
    let (_, message) = collect(stream_with_options(
        &openrouter_anthropic(),
        context,
        options_with_fetch(fetch),
    ))
    .await;
    recorded(&requests)
        .first()
        .unwrap_or_else(|| panic!("no request was sent: {:?}", message.error_message))
        .json()
}

fn message_with_role<'a>(payload: &'a JsonValue, role: &str) -> &'a JsonValue {
    payload["messages"]
        .as_array()
        .and_then(|messages| messages.iter().find(|message| message["role"] == role))
        .unwrap_or_else(|| panic!("no {role} message in {payload}"))
}

#[tokio::test]
async fn marked_user_text_blocks_carry_cache_control() {
    let payload = payload_for(&marked_context(&json!([marked("first"), plain("second")]))).await;

    assert_eq!(
        message_with_role(&payload, "user"),
        &json!({
            "role": "user",
            "content": [
                { "type": "text", "text": "first", "cache_control": { "type": "ephemeral" } },
                { "type": "text", "text": "second", "cache_control": { "type": "ephemeral" } },
            ],
        })
    );
    // Two marks used: the system and tool marks still fit the budget of four.
    assert_eq!(
        message_with_role(&payload, "system"),
        &json!({
            "role": "system",
            "content": [{ "type": "text", "text": "System prompt", "cache_control": { "type": "ephemeral" } }],
        })
    );
    assert_eq!(
        payload["tools"][0]["cache_control"],
        json!({ "type": "ephemeral" })
    );
}

#[tokio::test]
async fn three_marked_blocks_drop_the_optional_system_and_tool_marks() {
    let payload = payload_for(&marked_context(&json!([
        marked("a"),
        marked("b"),
        marked("c"),
        plain("d")
    ])))
    .await;

    assert_eq!(
        message_with_role(&payload, "user"),
        &json!({
            "role": "user",
            "content": [
                { "type": "text", "text": "a", "cache_control": { "type": "ephemeral" } },
                { "type": "text", "text": "b", "cache_control": { "type": "ephemeral" } },
                { "type": "text", "text": "c", "cache_control": { "type": "ephemeral" } },
                { "type": "text", "text": "d", "cache_control": { "type": "ephemeral" } },
            ],
        })
    );
    assert_eq!(
        message_with_role(&payload, "system"),
        &json!({ "role": "system", "content": "System prompt" })
    );
    assert!(
        payload["tools"][0].get("cache_control").is_none(),
        "{payload}"
    );
}

#[tokio::test]
async fn a_marked_assistant_text_block_sends_the_answer_as_marked_text_parts() {
    let payload = payload_for(&assistant_context(&json!([
        plain("draft"),
        marked("answer")
    ])))
    .await;

    assert_eq!(
        message_with_role(&payload, "assistant"),
        &json!({
            "role": "assistant",
            "content": [
                { "type": "text", "text": "draft" },
                { "type": "text", "text": "answer", "cache_control": { "type": "ephemeral" } },
            ],
        })
    );
}

#[tokio::test]
async fn an_unmarked_assistant_answer_stays_one_string() {
    let payload = payload_for(&assistant_context(&json!([
        plain("draft"),
        plain("answer")
    ])))
    .await;

    assert_eq!(
        message_with_role(&payload, "assistant"),
        &json!({ "role": "assistant", "content": "draftanswer" })
    );
}

#[test]
fn a_marked_assistant_text_part_carries_cache_control_after_thinking_as_text() {
    let model = test_model(json!({
        "id": "anthropic/claude-sonnet-4",
        "name": "Anthropic: Claude Sonnet 4",
        "provider": "openrouter",
        "baseUrl": "https://openrouter.ai/api/v1",
        "compat": { "cacheControlFormat": "anthropic", "requiresThinkingAsText": true },
    }));
    let cache_control = json!({ "type": "ephemeral" });
    let messages = convert_messages(
        &model,
        &assistant_context(&json!([
            { "type": "thinking", "thinking": "plan" },
            plain("draft"),
            marked("answer"),
        ])),
        &get_compat(&model),
        &ConvertCompletionsMessagesOptions {
            cache_control: Some(&cache_control),
            ..ConvertCompletionsMessagesOptions::default()
        },
    )
    .unwrap_or_else(|error| panic!("convert_messages failed: {error:?}"));

    assert_eq!(
        messages[1],
        json!({
            "role": "assistant",
            "content": [
                { "type": "text", "text": "plan" },
                { "type": "text", "text": "draft" },
                { "type": "text", "text": "answer", "cache_control": { "type": "ephemeral" } },
            ],
        })
    );
}

#[tokio::test]
async fn four_marked_blocks_fail_before_sending() {
    let (fetch, requests) = sse_fetch(stop_chunks());
    let (events, message) = collect(stream_with_options(
        &openrouter_anthropic(),
        &marked_context(&json!([marked("a"), marked("b"), marked("c"), marked("d")])),
        options_with_fetch(fetch),
    ))
    .await;

    let expected = "Too many cache breakpoints: the request marks 4 blocks, at most 3 are allowed";
    assert!(recorded(&requests).is_empty());
    assert_eq!(message.stop_reason, StopReason::Error);
    assert_eq!(message.error_message.as_deref(), Some(expected));
    match events.last() {
        Some(AssistantMessageEvent::Error { error, .. }) => {
            assert_eq!(error.error_message.as_deref(), Some(expected));
        }
        other => panic!("expected an error event, got {other:?}"),
    }
}
