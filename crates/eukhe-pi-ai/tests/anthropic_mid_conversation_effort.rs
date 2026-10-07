//! Port of `test/anthropic-mid-conversation-effort.test.ts`.

mod anthropic_support;

use std::fmt::Write;

use anthropic_support::{
    builtin_model, capturing_on_payload, context, mock_fetch, model, take_payload, MockResponse,
};
use eukhe_pi_ai::api::anthropic_messages::stream;
use eukhe_pi_ai::types::ProviderStreamOptions;
use eukhe_types::pi_ai::{AssistantMessage, CacheRetention, JsonValue, Model, StopReason};
use serde_json::json;

fn managed_model(provider: &str) -> Model {
    model(&json!({
        "id": "claude-fable-5-1",
        "name": "Claude Fable 5.1",
        "provider": provider,
        "baseUrl": "http://127.0.0.1:9",
        "reasoning": true,
        "thinkingLevelMap": { "off": null, "minimal": "low", "low": "low", "medium": "medium", "high": "high", "max": "max" },
        "contextWindow": 200_000,
        "maxTokens": 32000,
        "compat": { "forceAdaptiveThinking": true, "supportsMidConvoEffort": true },
    }))
}

fn assistant(model: &Model, level: Option<&str>) -> JsonValue {
    let mut message = json!({
        "role": "assistant",
        "content": [
            { "type": "thinking", "thinking": "reasoning", "thinkingSignature": "signature" },
            { "type": "text", "text": "answer" },
        ],
        "api": "anthropic-messages",
        "provider": model.provider,
        "model": model.id,
    });
    if let Some(level) = level {
        message["providerThinkingLevel"] = json!(level);
    }
    let rest = json!({
        "usage": {
            "input": 0,
            "output": 0,
            "cacheRead": 0,
            "cacheWrite": 0,
            "totalTokens": 0,
            "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
        },
        "stopReason": "stop",
        "timestamp": 1,
    });
    for (key, value) in rest.as_object().expect("object") {
        message[key] = value.clone();
    }
    message
}

struct Captured {
    payload: JsonValue,
    message: AssistantMessage,
}

async fn capture(model: &Model, ctx: &JsonValue, effort: Option<&str>) -> Captured {
    let (on_payload, captured) = capturing_on_payload();
    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = Some("test-key".into());
    options.stream.cache_retention = Some(CacheRetention::None);
    options.stream.request.on_payload = Some(on_payload);
    options.extra.insert("thinkingEnabled".into(), json!(true));
    if let Some(effort) = effort {
        options.extra.insert("effort".into(), json!(effort));
    }
    let message = stream(model, &context(ctx), options).result().await;
    Captured {
        payload: take_payload(&captured),
        message,
    }
}

fn user(text: &str, timestamp: u64) -> JsonValue {
    json!({ "role": "user", "content": text, "timestamp": timestamp })
}

fn effort_messages(payload: &JsonValue) -> Vec<JsonValue> {
    payload["messages"]
        .as_array()
        .expect("messages")
        .iter()
        .filter(|message| message["role"] == "system")
        .cloned()
        .collect()
}

#[tokio::test]
async fn reconstructs_an_exact_historical_marker_prefix_and_appends_the_current_marker() {
    let model = managed_model("anthropic");
    let first = capture(
        &model,
        &json!({ "messages": [user("one", 1)] }),
        Some("low"),
    )
    .await;
    let second = capture(
        &model,
        &json!({ "messages": [user("one", 1), assistant(&model, Some("low")), user("two", 2)] }),
        Some("high"),
    )
    .await;

    assert_eq!(
        first.payload["messages"],
        json!([
            { "role": "user", "content": "one" },
            { "role": "system", "content": [], "output_config": { "effort": "low" } },
        ])
    );
    let first_messages = first.payload["messages"].as_array().expect("messages");
    let second_messages = second.payload["messages"].as_array().expect("messages");
    assert_eq!(
        &second_messages[..first_messages.len()],
        first_messages.as_slice()
    );
    assert_eq!(
        second_messages.last(),
        Some(&json!({ "role": "system", "content": [], "output_config": { "effort": "high" } }))
    );
    assert_eq!(
        first.payload.get("output_config"),
        Some(&json!({ "effort": "high" }))
    );
    assert_eq!(
        second.payload.get("output_config"),
        Some(&json!({ "effort": "high" }))
    );
    assert_eq!(
        second.payload.get("thinking"),
        Some(&json!({
            "type": "adaptive",
            "display": "summarized",
            "block_binding": { "prefix_mismatch_behavior": "drop_block" },
        }))
    );
    assert_eq!(
        first.message.provider_thinking_level.as_deref(),
        Some("low")
    );
}

async fn preserves_native_effort(effort: &str) {
    let model = managed_model("anthropic");
    let Captured { payload, message } = capture(
        &model,
        &json!({ "messages": [user("one", 1)] }),
        Some(effort),
    )
    .await;
    assert_eq!(
        effort_messages(&payload),
        vec![json!({ "role": "system", "content": [], "output_config": { "effort": effort } })]
    );
    assert_eq!(message.provider_thinking_level.as_deref(), Some(effort));
}

#[tokio::test]
async fn preserves_native_effort_low() {
    preserves_native_effort("low").await;
}

#[tokio::test]
async fn preserves_native_effort_medium() {
    preserves_native_effort("medium").await;
}

#[tokio::test]
async fn preserves_native_effort_high() {
    preserves_native_effort("high").await;
}

#[tokio::test]
async fn preserves_native_effort_xhigh() {
    preserves_native_effort("xhigh").await;
}

#[tokio::test]
async fn preserves_native_effort_max() {
    preserves_native_effort("max").await;
}

#[tokio::test]
async fn defaults_omitted_effort_to_high_and_still_enables_drop_block() {
    let Captured { payload, message } = capture(
        &managed_model("anthropic"),
        &json!({ "messages": [user("one", 1)] }),
        None,
    )
    .await;
    assert_eq!(
        payload["messages"].as_array().expect("messages").last(),
        Some(&json!({ "role": "system", "content": [], "output_config": { "effort": "high" } }))
    );
    assert_eq!(
        payload["thinking"]["block_binding"]["prefix_mismatch_behavior"],
        "drop_block"
    );
    assert_eq!(message.provider_thinking_level.as_deref(), Some("high"));
}

#[tokio::test]
async fn does_not_invent_markers_for_legacy_or_other_provider_assistants() {
    let model = managed_model("anthropic");
    let legacy = assistant(&model, None);
    let mut other_provider = assistant(&model, Some("low"));
    other_provider["provider"] = json!("other-provider");
    let Captured { payload, .. } = capture(
        &model,
        &json!({ "messages": [user("one", 1), legacy, user("two", 2), other_provider, user("three", 3)] }),
        Some("medium"),
    )
    .await;
    assert_eq!(
        effort_messages(&payload),
        vec![json!({ "role": "system", "content": [], "output_config": { "effort": "medium" } })]
    );
}

#[tokio::test]
async fn leaves_unsupported_models_on_top_level_effort() {
    let mut value = serde_json::to_value(managed_model("anthropic")).expect("model json");
    value["compat"] = json!({ "forceAdaptiveThinking": true });
    let model: Model = serde_json::from_value(value).expect("model");
    let Captured { payload, message } = capture(
        &model,
        &json!({ "messages": [user("one", 1)] }),
        Some("low"),
    )
    .await;
    assert_eq!(
        payload["messages"],
        json!([{ "role": "user", "content": "one" }])
    );
    assert_eq!(
        payload.get("output_config"),
        Some(&json!({ "effort": "low" }))
    );
    assert_eq!(
        payload.get("thinking"),
        Some(&json!({ "type": "adaptive", "display": "summarized" }))
    );
    assert_eq!(message.provider_thinking_level, None);
}

#[tokio::test]
async fn sends_the_effort_and_binding_beta_headers() {
    let events = [
        json!({
            "type": "message_start",
            "message": {
                "id": "msg_test",
                "model": "claude-fable-5-1",
                "usage": { "input_tokens": 1, "output_tokens": 0 },
            },
        }),
        json!({
            "type": "message_delta",
            "delta": { "stop_reason": "end_turn" },
            "usage": { "input_tokens": 1, "output_tokens": 1 },
        }),
        json!({ "type": "message_stop" }),
    ];
    let mut body = String::new();
    for event in &events {
        let name = event["type"].as_str().unwrap_or("");
        write!(body, "event: {name}\ndata: {event}\n\n").expect("write to String");
    }
    let (fetch, captured) = mock_fetch(MockResponse::sse(body));
    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = Some("test-key".into());
    options.stream.cache_retention = Some(CacheRetention::None);
    options.stream.request.fetch = Some(fetch);
    let result = stream(
        &managed_model("anthropic"),
        &context(&json!({ "messages": [user("one", 1)] })),
        options,
    )
    .result()
    .await;

    assert_eq!(
        result.stop_reason,
        StopReason::Stop,
        "{:?}",
        result.error_message
    );
    let requests = anthropic_support::requests(&captured);
    let beta_header = requests
        .last()
        .and_then(|request| request.header("anthropic-beta"))
        .unwrap_or_default();
    assert!(
        beta_header.contains("mid-conversation-output-config-2026-07-01"),
        "{beta_header}"
    );
    assert!(
        beta_header.contains("thinking-binding-controls-2026-08-01"),
        "{beta_header}"
    );
}

fn as_json(model: &Model) -> JsonValue {
    serde_json::to_value(model).expect("model json")
}

#[test]
fn generates_exact_model_and_transport_gates() {
    let direct = as_json(&builtin_model("anthropic", "claude-fable-5-1", &json!({})));
    let open_router = as_json(&builtin_model(
        "openrouter",
        "anthropic/claude-fable-5.1",
        &json!({}),
    ));
    let unsupported = as_json(&builtin_model("anthropic", "claude-opus-4-8", &json!({})));
    assert_eq!(direct["compat"]["supportsMidConvoEffort"], true);
    assert_eq!(
        direct["thinkingLevelMap"].get("off"),
        Some(&JsonValue::Null)
    );
    assert_eq!(open_router["api"], "anthropic-messages");
    assert_eq!(open_router["baseUrl"], "https://openrouter.ai/api");
    assert_eq!(open_router["compat"]["supportsMidConvoEffort"], true);
    assert_eq!(unsupported["compat"].get("supportsMidConvoEffort"), None);
    // OpenRouter rejects configuration_update on Opus 5 but accepts it on Fable 5.1.
    assert_eq!(
        as_json(&builtin_model(
            "openrouter",
            "anthropic/claude-opus-5",
            &json!({})
        ))["compat"]
            .get("supportsMidConvoEffort"),
        None
    );
    assert_eq!(
        as_json(&builtin_model("anthropic", "claude-opus-5", &json!({})))["compat"]
            .get("allowedFallbackModels"),
        None
    );
}
