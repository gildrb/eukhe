//! eukhe addition: the output cap of an `anthropic-messages` request (the
//! compiled `Fx.cap` and `Fx.adjust`, `laws/facts.bend` `facts_cap_*`,
//! `facts_fit_*`): budget-mode thinking on top of the answer cap with
//! 4000 tokens left for the answer, and no window shrink for a model the
//! Claude API stops at the window.

mod anthropic_support;

use std::sync::{Arc, Mutex, PoisonError};

use anthropic_support::{context, minimal_sse, mock_fetch};
use eukhe_ai::api::anthropic_messages::stream_simple;
use eukhe_ai::types::{OnPayload, SimpleStreamOptions};
use eukhe_ai::utils::estimate::estimate_context_tokens;
use eukhe_types::pi_ai::{JsonValue, Model, ThinkingBudgets, ThinkingLevel, TranscriptContext};
use serde_json::json;

/// A Claude model on the Claude API.
fn claude(id: &str, context_window: u64, max_tokens: u64) -> Model {
    serde_json::from_value(json!({
        "id": id,
        "name": id,
        "api": "anthropic-messages",
        "provider": "anthropic",
        "baseUrl": "https://api.anthropic.com",
        "reasoning": true,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": context_window,
        "maxTokens": max_tokens,
    }))
    .expect("model")
}

fn user(text: &str) -> TranscriptContext {
    context(&json!({ "messages": [{ "role": "user", "content": text, "timestamp": 0 }] }))
}

/// The `onPayload` params of one `streamSimple` call.
async fn payload(
    model: &Model,
    context: &TranscriptContext,
    options: SimpleStreamOptions,
) -> JsonValue {
    let captured: Arc<Mutex<Option<JsonValue>>> = Arc::default();
    let sink = Arc::clone(&captured);
    let on_payload: OnPayload<Model> = Arc::new(move |payload, _model| {
        *sink.lock().unwrap_or_else(PoisonError::into_inner) = Some(payload);
        Box::pin(async { Ok(None) })
    });
    let (fetch, _) = mock_fetch(minimal_sse());
    let mut options = options;
    options.stream.request.api_key = Some("test-key".into());
    options.stream.request.fetch = Some(fetch);
    options.stream.request.on_payload = Some(on_payload);
    stream_simple(model, context, &options).result().await;
    let payload = captured
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone();
    payload.expect("payload captured")
}

/// Regression: budget-mode thinking took its budget out of the cap and
/// kept only 1024 tokens for the answer. The request now carries the
/// catalog max, and a budget past the cap minus 4000 is cut to it.
#[tokio::test]
async fn a_budget_mode_request_sends_the_catalog_max_and_leaves_the_answer_4000_tokens() {
    let options = SimpleStreamOptions {
        reasoning: Some(ThinkingLevel::High),
        thinking_budgets: Some(ThinkingBudgets {
            high: Some(30_000),
            ..ThinkingBudgets::default()
        }),
        ..SimpleStreamOptions::default()
    };
    let params = payload(
        &claude("claude-opus-4-1", 200_000, 32_000),
        &user("Hi"),
        options,
    )
    .await;
    assert_eq!(
        (&params["max_tokens"], &params["thinking"]),
        (
            &json!(32_000),
            &json!({ "type": "enabled", "budget_tokens": 32_000 - 4000, "display": "summarized" })
        )
    );
}

/// A prompt near the window shrinks the cap of a model the API rejects
/// past the window (Claude Opus 4.1), and leaves whole the cap of one the
/// Claude API stops at the window (Claude Sonnet 4.5: the rulebook's
/// `stops_output_at_window`).
#[tokio::test]
async fn a_model_the_claude_api_stops_at_the_window_is_not_shrunk() {
    let context = user(&"word ".repeat(2_000));
    let prompt = estimate_context_tokens(context.messages()).tokens;
    // The request's prompt size as Eukhe sizes it: a tenth on top of the
    // local estimate, 16 tokens of framing for the one message; then 64
    // tokens of headway.
    let window = prompt + prompt.div_ceil(10) + 16 + 64 + 10_000;
    let shrunk = payload(
        &claude("claude-opus-4-1", window, 32_000),
        &context,
        SimpleStreamOptions::default(),
    )
    .await;
    let whole = payload(
        &claude("claude-sonnet-4-5", window, 64_000),
        &context,
        SimpleStreamOptions::default(),
    )
    .await;
    assert_eq!(
        (&shrunk["max_tokens"], &whole["max_tokens"]),
        (&json!(10_000), &json!(64_000)),
        "prompt {prompt}"
    );
}
