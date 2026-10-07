//! Port of `test/anthropic-thinking-disable.test.ts`.

mod anthropic_support;

use anthropic_support::{builtin_model, capture_simple_payload};
use eukhe_pi_ai::types::SimpleStreamOptions;
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessageEvent, Context, Model, StopReason, ThinkingLevel,
};
use futures::StreamExt;
use serde_json::json;

fn reasoning(level: ThinkingLevel) -> SimpleStreamOptions {
    SimpleStreamOptions {
        reasoning: Some(level),
        ..SimpleStreamOptions::default()
    }
}

struct RunResult {
    thinking_event_count: usize,
    thinking_char_count: usize,
    text: String,
    content_types: Vec<&'static str>,
}

fn make_e2e_context() -> Context {
    serde_json::from_value(json!({
        "systemPrompt": "You are a precise assistant. Follow the requested output format exactly.",
        "messages": [{
            "role": "user",
            "content": "Before replying, carefully solve 36863 * 5279 internally. Then reply with the word pong repeated exactly 40 times, separated by single spaces. Do not add any other text.",
            "timestamp": 1,
        }],
    }))
    .expect("context")
}

fn count_pongs(text: &str) -> usize {
    regex::Regex::new(r"(?i)\bpong\b")
        .expect("regex")
        .find_iter(text)
        .count()
}

async fn run_without_reasoning(model: &Model) -> RunResult {
    let mut options = SimpleStreamOptions::default();
    options.stream.temperature = Some(0.0);
    options.stream.max_tokens = Some(160);
    let stream =
        eukhe_pi_ai::compat::stream_simple(model, make_e2e_context(), options).expect("stream");

    let mut thinking_event_count = 0;
    let mut thinking_char_count = 0;
    let mut events = stream.events();
    while let Some(event) = events.next().await {
        match &event {
            AssistantMessageEvent::ThinkingStart { .. }
            | AssistantMessageEvent::ThinkingEnd { .. } => {
                thinking_event_count += 1;
            }
            AssistantMessageEvent::ThinkingDelta { delta, .. } => {
                thinking_event_count += 1;
                // JS `delta.length` counts UTF-16 code units.
                thinking_char_count += delta.encode_utf16().count();
            }
            _ => {}
        }
    }

    let response = stream.result().await;
    assert_eq!(
        response.stop_reason,
        StopReason::Stop,
        "{:?}",
        response.error_message
    );

    let text = response
        .content
        .iter()
        .filter_map(|block| match block {
            AssistantContentBlock::Text(text) => Some(text.text.as_str()),
            AssistantContentBlock::Thinking(_) | AssistantContentBlock::ToolCall(_) => None,
        })
        .collect::<String>()
        .trim()
        .to_owned();

    RunResult {
        thinking_event_count,
        thinking_char_count,
        text,
        content_types: response
            .content
            .iter()
            .map(AssistantContentBlock::type_name)
            .collect(),
    }
}

#[tokio::test]
async fn sends_thinking_type_disabled_for_budget_based_reasoning_models_when_thinking_is_off() {
    let payload = capture_simple_payload(
        &builtin_model("anthropic", "claude-sonnet-4-5", &json!({})),
        SimpleStreamOptions::default(),
    )
    .await;

    assert_eq!(
        payload.get("thinking"),
        Some(&json!({ "type": "disabled" }))
    );
    assert_eq!(payload.get("output_config"), None);
}

#[tokio::test]
async fn sends_thinking_type_disabled_for_adaptive_reasoning_models_when_thinking_is_off() {
    let payload = capture_simple_payload(
        &builtin_model("anthropic", "claude-opus-4-6", &json!({})),
        SimpleStreamOptions::default(),
    )
    .await;

    assert_eq!(
        payload.get("thinking"),
        Some(&json!({ "type": "disabled" }))
    );
    assert_eq!(payload.get("output_config"), None);
}

#[tokio::test]
async fn sends_thinking_type_disabled_for_claude_opus_4_8_when_thinking_is_off() {
    let payload = capture_simple_payload(
        &builtin_model("anthropic", "claude-opus-4-8", &json!({})),
        SimpleStreamOptions::default(),
    )
    .await;

    assert_eq!(
        payload.get("thinking"),
        Some(&json!({ "type": "disabled" }))
    );
    assert_eq!(payload.get("output_config"), None);
}

#[tokio::test]
async fn omits_thinking_type_disabled_for_claude_fable_5_when_thinking_is_off() {
    let payload = capture_simple_payload(
        &builtin_model("anthropic", "claude-fable-5", &json!({})),
        SimpleStreamOptions::default(),
    )
    .await;

    assert_eq!(payload.get("thinking"), None);
    assert_eq!(payload.get("output_config"), None);
}

#[tokio::test]
async fn uses_adaptive_thinking_for_claude_opus_4_8_when_reasoning_is_enabled() {
    let payload = capture_simple_payload(
        &builtin_model("anthropic", "claude-opus-4-8", &json!({})),
        reasoning(ThinkingLevel::High),
    )
    .await;

    assert_eq!(
        payload.get("thinking"),
        Some(&json!({ "type": "adaptive", "display": "summarized" }))
    );
    assert_eq!(
        payload.get("output_config"),
        Some(&json!({ "effort": "high" }))
    );
}

#[tokio::test]
async fn uses_adaptive_thinking_for_claude_sonnet_5_when_reasoning_is_enabled() {
    let payload = capture_simple_payload(
        &builtin_model("anthropic", "claude-sonnet-5", &json!({})),
        reasoning(ThinkingLevel::High),
    )
    .await;

    assert_eq!(
        payload.get("thinking"),
        Some(&json!({ "type": "adaptive", "display": "summarized" }))
    );
    assert_eq!(
        payload.get("output_config"),
        Some(&json!({ "effort": "high" }))
    );
}

#[tokio::test]
async fn maps_xhigh_reasoning_to_effort_xhigh_for_claude_opus_4_8() {
    let payload = capture_simple_payload(
        &builtin_model("anthropic", "claude-opus-4-8", &json!({})),
        reasoning(ThinkingLevel::Xhigh),
    )
    .await;

    assert_eq!(
        payload.get("thinking"),
        Some(&json!({ "type": "adaptive", "display": "summarized" }))
    );
    assert_eq!(
        payload.get("output_config"),
        Some(&json!({ "effort": "xhigh" }))
    );
}

#[tokio::test]
#[ignore = "needs ANTHROPIC_API_KEY; run with --ignored"]
async fn disables_thinking_for_claude_reasoning_models() {
    let result =
        run_without_reasoning(&builtin_model("anthropic", "claude-sonnet-4-5", &json!({}))).await;

    assert_eq!(result.thinking_event_count, 0);
    assert_eq!(result.thinking_char_count, 0);
    assert!(!result.content_types.contains(&"thinking"));
    assert!(count_pongs(&result.text) >= 35, "{}", result.text);
}
