//! Port of `test/openai-responses-empty-tool-result.test.ts`.

use eukhe_pi_ai::api::openai_responses_shared::{
    convert_responses_messages, ConvertResponsesMessagesOptions,
};
use eukhe_pi_ai::compat::get_model;
use eukhe_pi_ai::utils::transcript::normalize_context;
use eukhe_types::pi_ai::{Context, JsonValue};
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

fn usage() -> JsonValue {
    json!({
        "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
    })
}

fn build_empty_tool_result(tool_call_id: &str, timestamp: u64) -> JsonValue {
    json!({
        "role": "toolResult",
        "toolCallId": tool_call_id,
        "toolName": "bash",
        "content": [{ "type": "text", "text": "" }],
        "isError": false,
        "timestamp": timestamp,
    })
}

#[test]
fn uses_no_tool_output_placeholder_for_empty_tool_results_without_images() {
    let model = get_model("openai", "gpt-4o-mini").expect("model");
    let now = now();
    let assistant = json!({
        "role": "assistant",
        "content": [{ "type": "toolCall", "id": "tool-1", "name": "bash", "arguments": { "command": "true" } }],
        "api": model.api,
        "provider": model.provider,
        "model": model.id,
        "usage": usage(),
        "stopReason": "toolUse",
        "timestamp": now,
    });
    let context: Context = serde_json::from_value(json!({
        "messages": [
            { "role": "user", "content": "Run the command", "timestamp": now - 1 },
            assistant,
            build_empty_tool_result("tool-1", now + 1),
        ],
    }))
    .expect("context");
    let context = normalize_context(context);

    let input = convert_responses_messages(
        &model,
        &context,
        &["openai", "openai-codex", "opencode"],
        &ConvertResponsesMessagesOptions::default(),
    )
    .expect("convert");
    let function_call_output = input
        .iter()
        .find(|item| item["type"] == "function_call_output")
        .expect("function_call_output");

    let output = function_call_output["output"]
        .as_str()
        .expect("string output");
    assert_eq!(output, "(no tool output)");
    assert!(!output.contains("see attached image"));
}
