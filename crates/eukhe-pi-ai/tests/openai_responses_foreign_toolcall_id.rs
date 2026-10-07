//! Port of `test/openai-responses-foreign-toolcall-id.test.ts`.

use eukhe_pi_ai::api::openai_responses_shared::{
    convert_responses_messages, ConvertResponsesMessagesOptions,
};
use eukhe_pi_ai::compat::get_model;
use eukhe_pi_ai::utils::hash::short_hash;
use eukhe_pi_ai::utils::transcript::normalize_context;
use eukhe_types::pi_ai::Context;
use serde_json::json;

const COPILOT_RAW_TOOL_CALL_ID: &str = "call_4VnzVawQXPB9MgYib7CiQFEY|I9b95oN1wD/cHXKTw3PpRkL6KkCtzTJhUxMouMWYwHeTo2j3htzfSk7YPx2vifiIM4g3A8XXyOj8q4Bt6SLUG7gqY1E3ELkrkVQNHglRfUmWj84lqxJY+Puieb3VKyX0FB+83TUzn91cDMF/4gzt990IzqVrc+nIb9RRscRD070Du16q1glydVjWR0SBJsE6TbY/esOjFpqplogQqrajm1eI++f3eLi73R6q7hVusY0QbeFySVxABCjhN0lXB04caBe1rzHjYzul6MAXj7uq+0r17VLq+yrtyYhN12wkmFqHeqTyEei6EFPbMy24Nc+IbJlkP0OCg02W+gOnyBFcbi2ctvJFSOhSjt1CqBdqCnnhwUqXjbWiT0wh3DmLScRgTHmGkaI+oAcQQjfic65nxj+TnEkReA==";

fn now() -> u64 {
    u64::try_from(
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_millis(),
    )
    .unwrap_or(u64::MAX)
}

#[test]
fn hashes_foreign_copilot_tool_item_ids_into_a_bounded_codex_safe_fc_hash_shape() {
    let model = get_model("openai-codex", "gpt-5.5").expect("model");
    let assistant = json!({
        "role": "assistant",
        "content": [{
            "type": "toolCall",
            "id": COPILOT_RAW_TOOL_CALL_ID,
            "name": "edit",
            "arguments": { "path": "src/styles/app.css" },
        }],
        "api": "openai-responses",
        "provider": "github-copilot",
        "model": "gpt-5.5",
        "usage": {
            "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
            "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
        },
        "stopReason": "toolUse",
        "timestamp": now() - 2000,
    });
    let tool_result = json!({
        "role": "toolResult",
        "toolCallId": COPILOT_RAW_TOOL_CALL_ID,
        "toolName": "edit",
        "content": [{ "type": "text", "text": "ok" }],
        "isError": false,
        "timestamp": now() - 1000,
    });
    let context: Context = serde_json::from_value(json!({
        "systemPrompt": "You are concise.",
        "messages": [
            { "role": "user", "content": "Use the tool.", "timestamp": now() - 3000 },
            assistant,
            tool_result,
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
    let function_call = input
        .iter()
        .find(|item| item["type"] == "function_call")
        .expect("Expected function_call item");
    assert_eq!(function_call["type"], "function_call");

    let item_part = COPILOT_RAW_TOOL_CALL_ID
        .split('|')
        .nth(1)
        .expect("item part");
    let expected_item_id = format!("fc_{}", short_hash(item_part));
    let id = function_call["id"].as_str().expect("id");
    assert_eq!(id, expected_item_id);
    assert!(id.len() <= 64);
    let hash = id.strip_prefix("fc_").expect("fc_ prefix");
    assert!(!hash.is_empty() && hash.chars().all(|c| c.is_ascii_alphanumeric()));
}
