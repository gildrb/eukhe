//! Port of `test/anthropic-opus-4-8-smoke.test.ts` (real API; `#[ignore]`d).

mod anthropic_support;

use std::sync::{Arc, Mutex, PoisonError};

use anthropic_support::builtin_model;
use eukhe_pi_ai::types::SimpleStreamOptions;
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessageEvent, Context, JsonValue, StopReason, ThinkingLevel,
};
use futures::StreamExt;
use serde_json::json;

fn make_context() -> Context {
    serde_json::from_value(json!({
        "systemPrompt": "You are a precise assistant. Follow the user's instructions exactly.",
        "messages": [{
            "role": "user",
            "content": "Compute 48291 * 7317 and 90844 - 17729, add the results, and determine whether the sum is divisible by 11. Reply with exactly this format and nothing else: sum=<sum>; divisibleBy11=<yes|no>",
            "timestamp": 1,
        }],
    }))
    .expect("context")
}

#[tokio::test]
#[ignore = "needs ANTHROPIC_API_KEY; run with --ignored"]
async fn streams_claude_opus_4_8_with_reasoning_enabled() {
    let model = builtin_model("anthropic", "claude-opus-4-8", &json!({}));
    let captured_payload: Arc<Mutex<Option<JsonValue>>> = Arc::default();
    let sink = Arc::clone(&captured_payload);
    let mut options = SimpleStreamOptions {
        reasoning: Some(ThinkingLevel::High),
        ..SimpleStreamOptions::default()
    };
    options.stream.max_tokens = Some(1024);
    options.stream.request.on_payload = Some(Arc::new(move |payload, _model| {
        *sink.lock().unwrap_or_else(PoisonError::into_inner) = Some(payload.clone());
        Box::pin(async move { Ok(Some(payload)) })
    }));
    let s = eukhe_pi_ai::compat::stream_simple(&model, make_context(), options).expect("stream");

    let mut saw_thinking = false;
    let mut events = s.events();
    while let Some(event) = events.next().await {
        if matches!(
            event,
            AssistantMessageEvent::ThinkingStart { .. }
                | AssistantMessageEvent::ThinkingDelta { .. }
                | AssistantMessageEvent::ThinkingEnd { .. }
        ) {
            saw_thinking = true;
        }
    }

    let response = s.result().await;
    assert_eq!(
        response.stop_reason,
        StopReason::Stop,
        "{:?}",
        response.error_message
    );
    assert!(response
        .error_message
        .as_deref()
        .unwrap_or_default()
        .is_empty());
    let payload = captured_payload
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
        .unwrap_or_default();
    assert_eq!(
        payload.get("thinking"),
        Some(&json!({ "type": "adaptive" }))
    );
    assert_eq!(
        payload.get("output_config"),
        Some(&json!({ "effort": "high" }))
    );
    assert!(saw_thinking);

    let Some(AssistantContentBlock::Thinking(thinking_block)) = response
        .content
        .iter()
        .find(|block| matches!(block, AssistantContentBlock::Thinking(_)))
    else {
        panic!("Expected thinking block from Claude Opus 4.8");
    };
    let Some(thinking_signature) = thinking_block.thinking_signature.as_deref() else {
        panic!("Expected thinking signature from Claude Opus 4.8");
    };
    assert!(!thinking_signature.is_empty());

    let text = response
        .content
        .iter()
        .filter_map(|block| match block {
            AssistantContentBlock::Text(text) => Some(text.text.as_str()),
            AssistantContentBlock::Thinking(_) | AssistantContentBlock::ToolCall(_) => None,
        })
        .collect::<String>();
    assert_eq!(text.trim(), "sum=353418362; divisibleBy11=yes");
}
