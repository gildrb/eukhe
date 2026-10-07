//! Port of `test/tool-call-id-normalization.test.ts`: tool call IDs from the
//! `OpenAI` Responses API (`{call_id}|{id}`, `id` 400+ chars with `+/=`) are
//! normalized when sent to other providers (regression for pi#1022).
//!
//! Every case talks to live providers. TS resolves keys with
//! `test/oauth.ts` (stored OAuth credentials or env); here keys come from the
//! provider's env API key variables (`getEnvApiKey`).

use eukhe_pi_ai::compat::{complete_simple, get_model};
use eukhe_pi_ai::env_api_keys::get_env_api_key;
use eukhe_pi_ai::types::SimpleStreamOptions;
use eukhe_types::pi_ai::{AssistantContentBlock, Context, JsonValue, Message, StopReason};
use serde_json::json;

const FAILING_TOOL_CALL_ID: &str = "call_pAYbIr76hXIjncD9UE4eGfnS|t5nnb2qYMFWGSsr13fhCd1CaCu3t3qONEPuOudu4HSVEtA8YJSL6FAZUxvoOoD792VIJWl91g87EdqsCWp9krVsdBysQoDaf9lMCLb8BS4EYi4gQd5kBQBYLlgD71PYwvf+TbMD9J9/5OMD42oxSRj8H+vRf78/l2Xla33LWz4nOgsddBlbvabICRs8GHt5C9PK5keFtzyi3lsyVKNlfduK3iphsZqs4MLv4zyGJnvZo/+QzShyk5xnMSQX/f98+aEoNflEApCdEOXipipgeiNWnpFSHbcwmMkZoJhURNu+JEz3xCh1mrXeYoN5o+trLL3IXJacSsLYXDrYTipZZbJFRPAucgbnjYBC+/ZzJOfkwCs+Gkw7EoZR7ZQgJ8ma+9586n4tT4cI8DEhBSZsWMjrCt8dxKg==";

fn now() -> u64 {
    u64::try_from(
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_millis(),
    )
    .unwrap_or(u64::MAX)
}

fn key(provider: &str) -> String {
    get_env_api_key(provider, None).unwrap_or_else(|| panic!("no API key for {provider}"))
}

fn echo_tool() -> JsonValue {
    json!({
        "name": "echo",
        "description": "Echoes the message back",
        "parameters": {
            "type": "object",
            "properties": { "message": { "type": "string", "description": "Message to echo back" } },
            "required": ["message"],
        },
    })
}

fn context(system_prompt: &str, messages: &[JsonValue]) -> Context {
    serde_json::from_value(json!({
        "systemPrompt": system_prompt,
        "messages": messages,
        "tools": [echo_tool()],
    }))
    .expect("context")
}

fn options(api_key: String) -> SimpleStreamOptions {
    let mut options = SimpleStreamOptions::default();
    options.stream.request.api_key = Some(api_key);
    options
}

async fn live_handoff(target_provider: &str, target_model: &str, echo: &str) {
    let copilot_model = get_model("github-copilot", "gpt-5.5").expect("copilot model");
    let target = get_model(target_provider, target_model).expect("target model");
    let user = json!({ "role": "user", "content": format!("Use the echo tool to echo '{echo}'"), "timestamp": now() });

    let assistant = complete_simple(
        &copilot_model,
        context(
            "You are a helpful assistant. Use the echo tool when asked.",
            std::slice::from_ref(&user),
        ),
        options(key("github-copilot")),
    )
    .await
    .expect("copilot response");
    assert_eq!(
        assistant.stop_reason,
        StopReason::ToolUse,
        "Copilot error: {:?}",
        assistant.error_message
    );
    let tool_call = assistant
        .content
        .iter()
        .find_map(|block| match block {
            AssistantContentBlock::ToolCall(call) => Some(call.clone()),
            AssistantContentBlock::Text(_) | AssistantContentBlock::Thinking(_) => None,
        })
        .expect("tool call");
    if target_provider == "openrouter" {
        assert!(tool_call.id.contains('|'));
    }

    let tool_result = json!({
        "role": "toolResult",
        "toolCallId": tool_call.id,
        "toolName": "echo",
        "content": [{ "type": "text", "text": echo }],
        "isError": false,
        "timestamp": now(),
    });
    let response = complete_simple(
        &target,
        context(
            "You are a helpful assistant.",
            &[
                user,
                serde_json::to_value(Message::Assistant(assistant)).expect("assistant"),
                tool_result,
                json!({ "role": "user", "content": "Say hi", "timestamp": now() }),
            ],
        ),
        options(key(target_provider)),
    )
    .await
    .expect("target response");
    assert_ne!(
        response.stop_reason,
        StopReason::Error,
        "{target_provider} error: {:?}",
        response.error_message
    );
    assert_eq!(response.error_message, None);
}

#[tokio::test]
#[ignore = "needs github-copilot and OPENROUTER_API_KEY credentials; run with --ignored"]
async fn github_copilot_to_openrouter_should_normalize_pipe_separated_ids() {
    live_handoff("openrouter", "openai/gpt-5.5", "hello world").await;
}

#[tokio::test]
#[ignore = "needs github-copilot and openai-codex credentials; run with --ignored"]
async fn github_copilot_to_openai_codex_should_normalize_pipe_separated_ids() {
    live_handoff("openai-codex", "gpt-5.5", "test message").await;
}

fn prefilled_messages() -> Vec<JsonValue> {
    let now = now();
    vec![
        json!({ "role": "user", "content": "Use the echo tool to echo 'hello'", "timestamp": now - 2000 }),
        json!({
            "role": "assistant",
            "content": [{ "type": "toolCall", "id": FAILING_TOOL_CALL_ID, "name": "echo", "arguments": { "message": "hello" } }],
            "api": "openai-responses",
            "provider": "github-copilot",
            "model": "gpt-5.2-codex",
            "usage": {
                "input": 100, "output": 50, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 150,
                "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
            },
            "stopReason": "toolUse",
            "timestamp": now - 1500,
        }),
        json!({
            "role": "toolResult",
            "toolCallId": FAILING_TOOL_CALL_ID,
            "toolName": "echo",
            "content": [{ "type": "text", "text": "hello" }],
            "isError": false,
            "timestamp": now - 1000,
        }),
        json!({ "role": "user", "content": "Say hi", "timestamp": now }),
    ]
}

#[tokio::test]
#[ignore = "needs OPENROUTER_API_KEY; run with --ignored"]
async fn openrouter_should_handle_prefilled_context_with_long_pipe_separated_ids() {
    let model = get_model("openrouter", "openai/gpt-5.5").expect("model");
    let response = complete_simple(
        &model,
        context("You are a helpful assistant.", &prefilled_messages()),
        options(key("openrouter")),
    )
    .await
    .expect("response");
    assert_ne!(
        response.stop_reason,
        StopReason::Error,
        "OpenRouter error: {:?}",
        response.error_message
    );
    if let Some(message) = response.error_message {
        assert!(!message.contains("call_id"));
        assert!(!message.contains("too long"));
    }
}

#[tokio::test]
#[ignore = "needs openai-codex credentials; run with --ignored"]
async fn openai_codex_should_handle_prefilled_context_with_long_pipe_separated_ids() {
    let model = get_model("openai-codex", "gpt-5.5").expect("model");
    let response = complete_simple(
        &model,
        context("You are a helpful assistant.", &prefilled_messages()),
        options(key("openai-codex")),
    )
    .await
    .expect("response");
    assert_ne!(
        response.stop_reason,
        StopReason::Error,
        "Codex error: {:?}",
        response.error_message
    );
    if let Some(message) = response.error_message {
        assert!(!message.contains("id"));
        assert!(!message.contains("additional characters"));
    }
}
