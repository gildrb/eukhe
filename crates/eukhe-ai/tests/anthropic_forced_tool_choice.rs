//! eukhe: the provider-neutral forced tool choices on `anthropic-messages`.
//! Manual extended thinking rejects a forced choice, so such a request
//! omits it; a request without thinking or with adaptive thinking keeps it.

mod anthropic_support;

use anthropic_support::{capture_simple_payload, model};
use eukhe_ai::api::simple_options::maps_forced_tool_choice;
use eukhe_ai::types::{SimpleStreamOptions, ThinkingLevel, ToolChoice};
use serde_json::{json, Value};

/// The `tool_choice` of a `streamSimple` payload; `null` when absent.
async fn tool_choice(
    model_overrides: Value,
    reasoning: Option<ThinkingLevel>,
    choice: ToolChoice,
) -> Value {
    let options = SimpleStreamOptions {
        tool_choice: Some(choice),
        reasoning,
        ..SimpleStreamOptions::default()
    };
    let payload = capture_simple_payload(&model(&model_overrides), options).await;
    payload.get("tool_choice").cloned().unwrap_or(Value::Null)
}

fn read() -> ToolChoice {
    ToolChoice::Tool("read".to_owned())
}

#[tokio::test]
async fn forced_choices_map_to_any_and_a_named_tool() {
    assert_eq!(
        (
            tool_choice(json!({}), None, ToolChoice::Required).await,
            tool_choice(json!({}), None, read()).await,
        ),
        (
            json!({ "type": "any" }),
            json!({ "type": "tool", "name": "read" })
        )
    );
}

#[tokio::test]
async fn manual_thinking_omits_a_forced_choice_and_adaptive_thinking_keeps_it() {
    let thinking = json!({ "reasoning": true });
    let adaptive = json!({ "reasoning": true, "compat": { "forceAdaptiveThinking": true } });
    assert_eq!(
        (
            tool_choice(thinking.clone(), Some(ThinkingLevel::High), read()).await,
            tool_choice(
                thinking.clone(),
                Some(ThinkingLevel::High),
                ToolChoice::Required
            )
            .await,
            tool_choice(thinking, Some(ThinkingLevel::High), ToolChoice::Auto).await,
            tool_choice(adaptive, Some(ThinkingLevel::High), read()).await,
        ),
        (
            Value::Null,
            Value::Null,
            json!({ "type": "auto" }),
            json!({ "type": "tool", "name": "read" }),
        )
    );
}

/// `maps_forced_tool_choice` (what the harness escalates to) says a
/// request sends a forced choice exactly when its wire carries one.
#[tokio::test]
async fn the_forced_choice_predicate_matches_the_wire() {
    let cases = [
        (json!({}), None),
        (json!({ "reasoning": true }), None),
        (json!({ "reasoning": true }), Some(ThinkingLevel::High)),
        (
            json!({ "reasoning": true, "compat": { "forceAdaptiveThinking": true } }),
            Some(ThinkingLevel::High),
        ),
    ];
    let mut predicted = Vec::new();
    let mut sent = Vec::new();
    for (overrides, reasoning) in cases {
        predicted.push(maps_forced_tool_choice(&model(&overrides), reasoning));
        sent.push(tool_choice(overrides, reasoning, read()).await != Value::Null);
    }
    assert_eq!(
        (predicted.clone(), sent),
        (vec![true, true, false, true], predicted)
    );
}
