//! Port of `test/xiaomi-token-plan-ams-anthropic-empty-signature-smoke.test.ts`.
//! The TS suite is skipped without `XIAOMI_TOKEN_PLAN_AMS_API_KEY`; here it
//! is `#[ignore]`d.

mod anthropic_support;

use anthropic_support::{capturing_on_payload, model, take_payload};
use eukhe_pi_ai::compat::{complete_simple, get_env_api_key, stream_simple};
use eukhe_pi_ai::types::SimpleStreamOptions;
use eukhe_types::pi_ai::{
    AssistantContentBlock, Context, JsonValue, Message, Model, StopReason, ThinkingLevel,
};
use serde_json::json;

const PROVIDER: &str = "xiaomi-token-plan-ams";

fn smoke_model() -> Model {
    model(&json!({
        "id": "mimo-v2.5-pro",
        "name": "MiMo-V2.5-Pro Anthropic smoke",
        "provider": PROVIDER,
        "baseUrl": "https://token-plan-ams.xiaomimimo.com/anthropic",
        "reasoning": true,
        "cost": { "input": 1, "output": 3, "cacheRead": 0.2, "cacheWrite": 0 },
        "contextWindow": 1_048_576,
        "maxTokens": 1024,
        "compat": { "allowEmptySignature": true },
    }))
}

fn make_initial_context() -> Context {
    serde_json::from_value(json!({
        "systemPrompt": "You are concise. Follow the requested output format exactly.",
        "messages": [{
            "role": "user",
            "content": "Think internally if you need to, then reply with exactly this text and nothing else: first-ok",
            "timestamp": 1,
        }],
    }))
    .expect("context")
}

fn options(api_key: &str) -> SimpleStreamOptions {
    let mut options = SimpleStreamOptions::default();
    options.stream.request.api_key = Some(api_key.to_owned());
    options.stream.max_tokens = Some(512);
    options.reasoning = Some(ThinkingLevel::High);
    options
}

async fn capture_replay_payload(context: Context, api_key: &str) -> JsonValue {
    let (on_payload, captured) = capturing_on_payload();
    let mut options = options(api_key);
    options.stream.request.on_payload = Some(on_payload);
    let stream = stream_simple(&smoke_model(), context, options).expect("stream");
    let _ = stream.result().await;
    take_payload(&captured)
}

#[tokio::test]
#[ignore = "needs XIAOMI_TOKEN_PLAN_AMS_API_KEY; run with --ignored"]
async fn reproduces_empty_thinking_signatures_and_preserves_them_for_replay() {
    let api_key = get_env_api_key(PROVIDER, None).expect("XIAOMI_TOKEN_PLAN_AMS_API_KEY");
    let first_context = make_initial_context();
    let first = complete_simple(&smoke_model(), first_context.clone(), options(&api_key))
        .await
        .expect("complete");

    assert_eq!(
        first.stop_reason,
        StopReason::Stop,
        "{:?}",
        first.error_message
    );

    let thinking_blocks: Vec<_> = first
        .content
        .iter()
        .filter_map(|block| match block {
            AssistantContentBlock::Thinking(thinking) => Some(thinking.clone()),
            AssistantContentBlock::Text(_) | AssistantContentBlock::ToolCall(_) => None,
        })
        .collect();
    assert!(!thinking_blocks.is_empty());
    assert!(thinking_blocks
        .iter()
        .any(|block| block.thinking_signature.as_deref() == Some("")));

    let mut replay_context = first_context;
    replay_context.messages.push(Message::Assistant(first));
    replay_context.messages.push(
        serde_json::from_value(json!({
            "role": "user",
            "content": "Reply with exactly this text and nothing else: second-ok",
            "timestamp": 1,
        }))
        .expect("user message"),
    );

    let replay_payload = capture_replay_payload(replay_context, &api_key).await;
    let assistant_payload = replay_payload["messages"]
        .as_array()
        .and_then(|messages| {
            messages
                .iter()
                .find(|message| message["role"] == "assistant")
        })
        .expect("assistant payload");
    let content = assistant_payload["content"]
        .as_array()
        .expect("array content");
    let replayed_thinking: Vec<&JsonValue> = content
        .iter()
        .filter(|block| block["type"] == "thinking")
        .collect();
    let replayed_text: Vec<&JsonValue> = content
        .iter()
        .filter(|block| block["type"] == "text")
        .collect();
    assert_eq!(
        replayed_thinking,
        [&json!({ "type": "thinking", "thinking": thinking_blocks[0].thinking, "signature": "" })]
    );
    assert!(!replayed_text
        .iter()
        .any(|block| block["text"] == json!(thinking_blocks[0].thinking)));
}
