//! Port of `test/openai-responses-message-id.test.ts`.

use std::collections::HashSet;

use eukhe_pi_ai::api::openai_responses_shared::{
    convert_responses_messages, ConvertResponsesMessagesOptions,
};
use eukhe_pi_ai::compat::get_model;
use eukhe_pi_ai::utils::transcript::normalize_context;
use eukhe_types::pi_ai::Context;
use serde_json::json;

#[test]
fn generates_unique_fallback_message_ids_for_multiple_text_blocks_in_one_assistant_turn() {
    let model = get_model("openai-codex", "gpt-5.5").expect("model");
    let usage = json!({
        "input": 0,
        "output": 0,
        "cacheRead": 0,
        "cacheWrite": 0,
        "totalTokens": 0,
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
    });
    let assistant = json!({
        "role": "assistant",
        "content": [
            { "type": "thinking", "thinking": "private reasoning" },
            { "type": "text", "text": "visible answer" },
        ],
        "api": "anthropic-messages",
        "provider": "anthropic",
        "model": "claude-opus-4-8",
        "usage": usage,
        "stopReason": "stop",
        "timestamp": 1000,
    });
    let context = normalize_context(
        serde_json::from_value::<Context>(json!({
            "systemPrompt": "You are concise.",
            "messages": [{ "role": "user", "content": "hello", "timestamp": 0 }, assistant],
        }))
        .expect("context"),
    );

    let input = convert_responses_messages(
        &model,
        &context,
        &["openai", "openai-codex", "opencode"],
        &ConvertResponsesMessagesOptions::default(),
    )
    .expect("converts");
    let message_ids: Vec<&str> = input
        .iter()
        .filter(|item| item["type"] == "message")
        .filter_map(|item| item.get("id").and_then(|id| id.as_str()))
        .collect();

    assert_eq!(message_ids, ["msg_pi_1", "msg_pi_1_1"]);
    assert_eq!(
        message_ids.iter().collect::<HashSet<_>>().len(),
        message_ids.len()
    );
}
