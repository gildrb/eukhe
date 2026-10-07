//! Port of `test/openai-responses-reasoning-replay-e2e.test.ts`. Every case
//! talks to live providers (TS: `describe.skipIf(!OPENAI_API_KEY ||
//! !ANTHROPIC_API_KEY)`).

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_pi_ai::compat::{complete, get_env_api_key, get_model};
use eukhe_pi_ai::types::{OnPayload, ProviderStreamOptions};
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, Context, JsonValue, Model, StopReason, ToolCall,
};
use futures::FutureExt;
use serde_json::json;

fn now() -> u64 {
    u64::try_from(
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_millis(),
    )
    .unwrap_or(u64::MAX)
}

fn test_tool() -> JsonValue {
    json!({
        "name": "double_number",
        "description": "Doubles a number and returns the result",
        "parameters": {
            "type": "object",
            "properties": { "value": { "description": "A number to double", "type": "number" } },
            "required": ["value"],
        },
    })
}

fn context(system_prompt: &str, messages: &[JsonValue]) -> Context {
    serde_json::from_value(json!({
        "systemPrompt": system_prompt,
        "messages": messages,
        "tools": [test_tool()],
    }))
    .expect("context")
}

fn options(api_key: &str, extra: &JsonValue) -> ProviderStreamOptions {
    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = Some(api_key.to_owned());
    options.extra = serde_json::from_value(extra.clone()).expect("extra");
    options
}

/// `onPayload` capturing the last payload.
fn capture_payload() -> (OnPayload<Model>, Arc<Mutex<Option<JsonValue>>>) {
    let captured: Arc<Mutex<Option<JsonValue>>> = Arc::default();
    let sink = Arc::clone(&captured);
    let on_payload: OnPayload<Model> = Arc::new(move |payload, _model| {
        *sink.lock().unwrap_or_else(PoisonError::into_inner) = Some(payload);
        async { Ok(None) }.boxed()
    });
    (on_payload, captured)
}

fn find_tool_call(message: &AssistantMessage) -> Option<ToolCall> {
    message.content.iter().find_map(|block| match block {
        AssistantContentBlock::ToolCall(call) => Some(call.clone()),
        _ => None,
    })
}

fn text_of(message: &AssistantMessage) -> String {
    message
        .content
        .iter()
        .filter_map(|block| match block {
            AssistantContentBlock::Text(text) => Some(text.text.as_str()),
            _ => None,
        })
        .collect()
}

fn assert_no_error(response: &AssistantMessage) {
    assert_ne!(
        response.stop_reason,
        StopReason::Error,
        "Error: {:?}",
        response.error_message
    );
    assert!(response.error_message.as_deref().is_none_or(str::is_empty));
    assert!(!response.content.is_empty());
}

fn log_payload(label: &str, payload: Option<&JsonValue>, log_ids: bool, log_full: bool) {
    let input = payload
        .and_then(|payload| payload["input"].as_array())
        .cloned()
        .unwrap_or_default();
    let function_calls: Vec<&JsonValue> = input
        .iter()
        .filter(|item| item["type"] == "function_call")
        .collect();
    let reasoning_items = input
        .iter()
        .filter(|item| item["type"] == "reasoning")
        .count();
    println!("{label}");
    println!("- function_calls: {}", function_calls.len());
    println!("- reasoning items: {reasoning_items}");
    if log_ids && !function_calls.is_empty() {
        let ids: Vec<&JsonValue> = function_calls.iter().map(|call| &call["id"]).collect();
        println!("- function_call IDs: {ids:?}");
    }
    if log_full {
        println!(
            "- full input: {}",
            serde_json::to_string_pretty(&input).unwrap_or_default()
        );
    }
}

#[tokio::test]
#[ignore = "needs OPENAI_API_KEY and ANTHROPIC_API_KEY; run with --ignored"]
async fn skips_reasoning_only_history_after_an_aborted_turn() {
    let model = get_model("openai", "gpt-5-mini").expect("model");
    let api_key = get_env_api_key("openai", None).expect("Missing OPENAI_API_KEY");

    let user_message = json!({
        "role": "user",
        "content": "Use the double_number tool to double 21.",
        "timestamp": now(),
    });

    let assistant_response = complete(
        &model,
        context(
            "You are a helpful assistant. Use the tool.",
            std::slice::from_ref(&user_message),
        ),
        options(&api_key, &json!({ "reasoningEffort": "high" })),
    )
    .await
    .expect("first response");

    let thinking_block = assistant_response
        .content
        .iter()
        .find(|block| {
            matches!(block, AssistantContentBlock::Thinking(thinking) if thinking.thinking_signature.as_deref().is_some_and(|signature| !signature.is_empty()))
        })
        .cloned()
        .expect("Missing thinking signature from OpenAI Responses");

    let mut corrupted_assistant = assistant_response.clone();
    corrupted_assistant.content = vec![thinking_block];
    corrupted_assistant.stop_reason = StopReason::Aborted;

    let follow_up = json!({
        "role": "user",
        "content": "Say hello to confirm you can continue.",
        "timestamp": now(),
    });

    let context = context(
        "You are a helpful assistant.",
        &[
            user_message,
            serde_json::to_value(&corrupted_assistant).expect("assistant"),
            follow_up,
        ],
    );

    let response = complete(
        &model,
        context,
        options(&api_key, &json!({ "reasoningEffort": "high" })),
    )
    .await
    .expect("response");

    // The key assertion: no 400 error from orphaned reasoning item
    assert_no_error(&response);
}

#[tokio::test]
#[ignore = "needs OPENAI_API_KEY and ANTHROPIC_API_KEY; run with --ignored"]
async fn handles_same_provider_different_model_handoff_with_tool_calls() {
    let model_a = get_model("openai", "gpt-5-mini").expect("model a");
    let model_b = get_model("openai", "gpt-5.5").expect("model b");
    let api_key = get_env_api_key("openai", None).expect("Missing OPENAI_API_KEY");

    let user_message = json!({
        "role": "user",
        "content": "Use the double_number tool to double 21.",
        "timestamp": now(),
    });

    let assistant_response = complete(
        &model_a,
        context(
            "You are a helpful assistant. Always use the tool when asked.",
            std::slice::from_ref(&user_message),
        ),
        options(&api_key, &json!({ "reasoningEffort": "high" })),
    )
    .await
    .expect("first response");

    let tool_call_block = find_tool_call(&assistant_response)
        .expect("Missing tool call from OpenAI Responses - model did not use the tool");

    let tool_result = json!({
        "role": "toolResult",
        "toolCallId": tool_call_block.id,
        "toolName": tool_call_block.name,
        "content": [{ "type": "text", "text": "42" }],
        "isError": false,
        "timestamp": now(),
    });
    let follow_up = json!({
        "role": "user",
        "content": "What was the result? Answer with just the number.",
        "timestamp": now(),
    });

    let context = context(
        "You are a helpful assistant. Answer concisely.",
        &[
            user_message,
            serde_json::to_value(&assistant_response).expect("assistant"),
            tool_result,
            follow_up,
        ],
    );

    let (on_payload, captured_payload) = capture_payload();
    let mut request_options = options(&api_key, &json!({ "reasoningEffort": "high" }));
    request_options.stream.request.on_payload = Some(on_payload);
    let response = complete(&model_b, context, request_options)
        .await
        .expect("response");

    // The key assertion: no 400 error from orphaned function_call
    assert_no_error(&response);

    log_payload(
        "Payload sent to API:",
        captured_payload
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .as_ref(),
        false,
        true,
    );

    assert!(text_of(&response).contains("42"));
}

#[tokio::test]
#[ignore = "needs OPENAI_API_KEY and ANTHROPIC_API_KEY; run with --ignored"]
async fn handles_cross_provider_handoff_from_anthropic_to_openai_codex() {
    let anthropic_model = get_model("anthropic", "claude-sonnet-4-5").expect("anthropic model");
    let codex_model = get_model("openai", "gpt-5.5").expect("codex model");
    let (Some(anthropic_api_key), Some(openai_api_key)) = (
        get_env_api_key("anthropic", None),
        get_env_api_key("openai", None),
    ) else {
        panic!("Missing API keys");
    };

    let user_message = json!({
        "role": "user",
        "content": "Use the double_number tool to double 21.",
        "timestamp": now(),
    });

    let assistant_response = complete(
        &anthropic_model,
        context(
            "You are a helpful assistant. Always use the tool when asked.",
            std::slice::from_ref(&user_message),
        ),
        options(
            &anthropic_api_key,
            &json!({ "thinkingEnabled": true, "thinkingBudgetTokens": 5000 }),
        ),
    )
    .await
    .expect("anthropic response");

    let tool_call_block = find_tool_call(&assistant_response)
        .expect("Missing tool call from Anthropic - model did not use the tool");
    println!("Anthropic tool call ID: {}", tool_call_block.id);

    let tool_result = json!({
        "role": "toolResult",
        "toolCallId": tool_call_block.id,
        "toolName": tool_call_block.name,
        "content": [{ "type": "text", "text": "42" }],
        "isError": false,
        "timestamp": now(),
    });
    let follow_up = json!({
        "role": "user",
        "content": "What was the result? Answer with just the number.",
        "timestamp": now(),
    });

    let context = context(
        "You are a helpful assistant. Answer concisely.",
        &[
            user_message,
            serde_json::to_value(&assistant_response).expect("assistant"),
            tool_result,
            follow_up,
        ],
    );

    let (on_payload, captured_payload) = capture_payload();
    let mut request_options = options(&openai_api_key, &json!({ "reasoningEffort": "high" }));
    request_options.stream.request.on_payload = Some(on_payload);
    let response = complete(&codex_model, context, request_options)
        .await
        .expect("response");

    log_payload(
        "Payload sent to Codex:",
        captured_payload
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .as_ref(),
        true,
        false,
    );

    // The key assertion: no 400 error
    assert_no_error(&response);

    assert!(text_of(&response).contains("42"));
}
