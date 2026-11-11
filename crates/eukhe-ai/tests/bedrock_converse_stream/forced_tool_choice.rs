//! A forced tool choice (`any`, `tool`) on Bedrock, which rejects thinking
//! beside it: a prefix-bound model (Claude Opus, Sonnet and Haiku 5.5, Fable
//! 5) sends `auto` instead unless its thinking is explicitly disabled; any
//! other model keeps the forced choice and sends no additional model fields.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_ai::api::bedrock_converse_stream::stream_simple;
use eukhe_ai::api::simple_options::maps_forced_tool_choice;
use eukhe_ai::types::{SimpleStreamOptions, ThinkingLevel, ToolChoice};
use eukhe_ai::utils::transcript::normalize_context;
use eukhe_types::pi_ai::{Context, Model, StopReason, Tool};
use serde_json::{json, Value};

use super::support::{
    capture_payload_hook, get_model, sonnet_45_model, user, AfterCapture, EnvGuard,
};

fn lookup_tool() -> Tool {
    serde_json::from_value(json!({
        "name": "lookup",
        "description": "Look up a value",
        "parameters": {
            "type": "object",
            "properties": { "value": { "type": "string" } },
            "required": ["value"],
        },
    }))
    .expect("tool")
}

/// The `streamSimple` payload of `model` forcing `lookup` at `reasoning`.
async fn forced_payload(model: &Model, reasoning: Option<ThinkingLevel>) -> Value {
    let _env = EnvGuard::new(&[]).await;
    let slot = Arc::new(Mutex::new(None));
    let mut options = SimpleStreamOptions {
        tool_choice: Some(ToolChoice::Tool("lookup".to_owned())),
        reasoning,
        ..SimpleStreamOptions::default()
    };
    options.stream.request.on_payload =
        Some(capture_payload_hook(slot.clone(), AfterCapture::Throw));
    let context = Context {
        system_prompt: None,
        messages: vec![user("Use the tool")],
        tools: Some(vec![lookup_tool()]),
    };
    let result = stream_simple(model, &normalize_context(context), options)
        .result()
        .await;
    assert_eq!(result.stop_reason, StopReason::Error);
    let payload = slot.lock().unwrap_or_else(PoisonError::into_inner).take();
    payload.expect("Expected Bedrock payload to be captured")
}

/// The `toolChoice` and the thinking type the payload sends.
fn choice_and_thinking(payload: &Value) -> (Value, Value) {
    (
        payload["toolConfig"]["toolChoice"].clone(),
        payload
            .pointer("/additionalModelRequestFields/thinking/type")
            .cloned()
            .unwrap_or(Value::Null),
    )
}

#[tokio::test]
async fn a_forced_choice_becomes_auto_on_prefix_bound_models_and_drops_thinking_elsewhere() {
    let forced = json!({ "tool": { "name": "lookup" } });
    let auto = json!({ "auto": {} });
    let cases = [
        // Prefix-bound, thinking on: auto, thinking kept.
        (
            "global.anthropic.claude-opus-5-5",
            Some(ThinkingLevel::High),
            (auto.clone(), json!("adaptive")),
        ),
        // Prefix-bound, thinking off: no explicit disable, still adaptive.
        (
            "global.anthropic.claude-opus-5-5",
            None,
            (auto.clone(), json!("adaptive")),
        ),
        (
            "anthropic.claude-haiku-5-5",
            Some(ThinkingLevel::High),
            (auto, json!("adaptive")),
        ),
        // Thinking explicitly disabled: the forced choice stays.
        (
            "anthropic.claude-haiku-5-5",
            None,
            (forced.clone(), json!("disabled")),
        ),
        // Not prefix-bound: the forced choice stays, thinking goes.
        (
            "global.anthropic.claude-opus-4-8",
            Some(ThinkingLevel::High),
            (forced.clone(), Value::Null),
        ),
    ];
    for (id, reasoning, expected) in cases {
        let model = get_model("amazon-bedrock", id);
        let payload = forced_payload(&model, reasoning).await;
        assert_eq!(
            choice_and_thinking(&payload),
            expected,
            "{id} {reasoning:?}"
        );
    }
    // Manual (budget) thinking keeps the forced choice too and drops the
    // thinking fields.
    let payload = forced_payload(&sonnet_45_model(), Some(ThinkingLevel::High)).await;
    assert_eq!(choice_and_thinking(&payload), (forced, Value::Null));
    assert_eq!(payload.get("additionalModelRequestFields"), None);
}

/// `maps_forced_tool_choice` (what the harness escalates to) says a Bedrock
/// request sends a forced choice exactly when its wire carries one.
#[tokio::test]
async fn the_forced_choice_predicate_matches_the_bedrock_wire() {
    let mut predicted = Vec::new();
    let mut sent = Vec::new();
    let models = [
        get_model("amazon-bedrock", "global.anthropic.claude-opus-5-5"),
        get_model("amazon-bedrock", "anthropic.claude-haiku-5-5"),
        get_model("amazon-bedrock", "global.anthropic.claude-opus-4-8"),
        sonnet_45_model(),
    ];
    for model in &models {
        for reasoning in [None, Some(ThinkingLevel::High)] {
            predicted.push(maps_forced_tool_choice(model, reasoning));
            let payload = forced_payload(model, reasoning).await;
            sent.push(payload["toolConfig"]["toolChoice"].get("tool").is_some());
        }
    }
    assert_eq!(predicted, sent);
}
