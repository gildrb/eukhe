//! Port of `test/interleaved-thinking.test.ts`. Every case talks to a real
//! provider, so each is `#[ignore]`d with the credentials it needs.

mod anthropic_support;

use anthropic_support::builtin_model;
use eukhe_pi_ai::compat::complete_simple;
use eukhe_pi_ai::types::SimpleStreamOptions;
use eukhe_types::pi_ai::{
    AssistantContentBlock, Context, JsonValue, Model, StopReason, ThinkingLevel, ToolCall,
};
use serde_json::json;

/// TS `calculatorTool` (`TypeBox` `Type.Object` with a `StringEnum`).
fn calculator_tool() -> JsonValue {
    json!({
        "name": "calculator",
        "description": "Perform basic arithmetic operations",
        "parameters": {
            "type": "object",
            "properties": {
                "a": { "description": "First number", "type": "number" },
                "b": { "description": "Second number", "type": "number" },
                "operation": {
                    "description": "The operation to perform.",
                    "type": "string",
                    "enum": ["add", "subtract", "multiply", "divide"],
                },
            },
            "required": ["a", "b", "operation"],
        },
    })
}

fn evaluate_calculator_call(tool_call: &ToolCall) -> f64 {
    let args = serde_json::to_value(&tool_call.arguments).expect("arguments");
    let (Some(a), Some(b)) = (args["a"].as_f64(), args["b"].as_f64()) else {
        panic!("Invalid calculator arguments");
    };
    match args["operation"].as_str() {
        Some("add") => a + b,
        Some("subtract") => a - b,
        Some("multiply") => a * b,
        Some("divide") => a / b,
        _ => panic!("Invalid calculator arguments"),
    }
}

/// JS `String(number)` for the integral results the prompt produces.
fn js_number(value: f64) -> String {
    serde_json::to_value(value)
        .expect("number")
        .to_string()
        .trim_end_matches(".0")
        .to_owned()
}

fn has_block(content: &[AssistantContentBlock], block_type: &str) -> bool {
    content.iter().any(|block| block.type_name() == block_type)
}

async fn assert_second_tool_call_with_interleaved_thinking(llm: &Model, level: ThinkingLevel) {
    let system_prompt = [
        "You are a helpful assistant that must use tools for arithmetic.",
        "Always think before every tool call, not just the first one.",
        "Do not answer with plain text when a tool call is required.",
    ]
    .join(" ");
    let user_content = [
        "Use calculator to calculate 328 * 29.",
        "You must call the calculator tool exactly once.",
        "Provide the final answer based on the best guess given the tool result, even if it seems unreliable.",
        "Start by thinking about the steps you will take to solve the problem.",
    ]
    .join(" ");
    let mut context = json!({
        "systemPrompt": system_prompt,
        "messages": [{ "role": "user", "content": user_content, "timestamp": 1 }],
        "tools": [calculator_tool()],
    });
    let options = || SimpleStreamOptions {
        reasoning: Some(level),
        ..SimpleStreamOptions::default()
    };
    let as_context =
        |value: &JsonValue| -> Context { serde_json::from_value(value.clone()).expect("context") };

    let first_response = complete_simple(llm, as_context(&context), options())
        .await
        .expect("stream");

    assert_eq!(
        first_response.stop_reason,
        StopReason::ToolUse,
        "Error: {:?}",
        first_response.error_message
    );
    assert!(has_block(&first_response.content, "thinking"));
    assert!(has_block(&first_response.content, "toolCall"));

    let Some(first_tool_call) = first_response.content.iter().find_map(|block| match block {
        AssistantContentBlock::ToolCall(tool_call) => Some(tool_call.clone()),
        AssistantContentBlock::Text(_) | AssistantContentBlock::Thinking(_) => None,
    }) else {
        panic!("Expected first response to include a tool call");
    };

    let messages = context["messages"].as_array_mut().expect("messages");
    messages.push(serde_json::to_value(&first_response).expect("assistant"));

    let correct_answer = evaluate_calculator_call(&first_tool_call);
    messages.push(json!({
        "role": "toolResult",
        "toolCallId": first_tool_call.id,
        "toolName": first_tool_call.name,
        "content": [{
            "type": "text",
            "text": format!("The answer is {} or {}.", js_number(correct_answer), js_number(correct_answer * 2.0)),
        }],
        "isError": false,
        "timestamp": 2,
    }));

    let second_response = complete_simple(llm, as_context(&context), options())
        .await
        .expect("stream");

    assert_eq!(
        second_response.stop_reason,
        StopReason::Stop,
        "Error: {:?}",
        second_response.error_message
    );
    assert!(has_block(&second_response.content, "thinking"));
    assert!(has_block(&second_response.content, "text"));
}

#[tokio::test]
#[ignore = "needs AWS_PROFILE, AWS_ACCESS_KEY_ID+AWS_SECRET_ACCESS_KEY, or AWS_BEARER_TOKEN_BEDROCK; run with --ignored"]
async fn amazon_bedrock_should_do_interleaved_thinking_on_claude_opus_4_5() {
    let llm = builtin_model(
        "amazon-bedrock",
        "global.anthropic.claude-opus-4-5-20251101-v1:0",
        &json!({}),
    );
    assert_second_tool_call_with_interleaved_thinking(&llm, ThinkingLevel::High).await;
}

#[tokio::test]
#[ignore = "needs AWS_PROFILE, AWS_ACCESS_KEY_ID+AWS_SECRET_ACCESS_KEY, or AWS_BEARER_TOKEN_BEDROCK; run with --ignored"]
async fn amazon_bedrock_should_do_interleaved_thinking_on_claude_opus_4_6() {
    let llm = builtin_model(
        "amazon-bedrock",
        "global.anthropic.claude-opus-4-6-v1",
        &json!({}),
    );
    assert_second_tool_call_with_interleaved_thinking(&llm, ThinkingLevel::High).await;
}

#[tokio::test]
#[ignore = "needs ANTHROPIC_API_KEY (or ANTHROPIC_OAUTH_TOKEN); run with --ignored"]
async fn anthropic_should_do_interleaved_thinking_on_claude_opus_4_5() {
    let llm = builtin_model("anthropic", "claude-opus-4-5", &json!({}));
    assert_second_tool_call_with_interleaved_thinking(&llm, ThinkingLevel::High).await;
}

#[tokio::test]
#[ignore = "needs ANTHROPIC_API_KEY (or ANTHROPIC_OAUTH_TOKEN); run with --ignored"]
async fn anthropic_should_do_interleaved_thinking_on_claude_opus_4_6() {
    let llm = builtin_model("anthropic", "claude-opus-4-6", &json!({}));
    assert_second_tool_call_with_interleaved_thinking(&llm, ThinkingLevel::High).await;
}
