//! Port of `test/anthropic-empty-thinking-signature-compat.test.ts`.

mod anthropic_support;

use anthropic_support::{capturing_on_payload, model, take_payload};
use eukhe_pi_ai::compat::{get_model, get_models, stream_simple};
use eukhe_pi_ai::types::SimpleStreamOptions;
use eukhe_types::pi_ai::{Context, JsonValue, Model};
use serde_json::json;

fn make_model(allow_empty_signature: Option<bool>) -> Model {
    let mut overrides = json!({
        "id": "mimo-v2.5-pro",
        "name": "MiMo-V2.5-Pro",
        "provider": "xiaomi-token-plan-ams",
        "baseUrl": "http://127.0.0.1:9/anthropic",
        "reasoning": true,
        "contextWindow": 1_048_576,
        "maxTokens": 1024,
    });
    if let Some(allow_empty_signature) = allow_empty_signature {
        overrides["compat"] = json!({ "allowEmptySignature": allow_empty_signature });
    }
    model(&overrides)
}

fn make_context_value(
    thinking_signature: &str,
    thinking: &str,
    provider: &str,
    model: &str,
) -> JsonValue {
    json!({
        "messages": [
            { "role": "user", "content": "first", "timestamp": 1 },
            {
                "role": "assistant",
                "content": [{ "type": "thinking", "thinking": thinking, "thinkingSignature": thinking_signature }],
                "provider": provider,
                "api": "anthropic-messages",
                "model": model,
                "timestamp": 1,
                "usage": {
                    "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
                    "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
                },
                "stopReason": "stop",
            },
            { "role": "user", "content": "second", "timestamp": 1 },
        ],
    })
}

fn make_context(thinking_signature: &str) -> JsonValue {
    make_context_value(
        thinking_signature,
        "internal reasoning",
        "xiaomi-token-plan-ams",
        "mimo-v2.5-pro",
    )
}

async fn capture_payload(model: &Model, context: &JsonValue) -> JsonValue {
    let (on_payload, captured) = capturing_on_payload();
    let mut options = SimpleStreamOptions::default();
    options.stream.request.api_key = Some("fake-key".into());
    options.stream.request.on_payload = Some(on_payload);
    let context: Context = serde_json::from_value(context.clone()).expect("context");
    let stream = stream_simple(model, context, options).expect("stream");
    let _ = stream.result().await;
    take_payload(&captured)
}

fn assistant_content(payload: &JsonValue) -> JsonValue {
    payload["messages"]
        .as_array()
        .and_then(|messages| {
            messages
                .iter()
                .find(|message| message["role"] == "assistant")
        })
        .map(|message| message["content"].clone())
        .expect("assistant message")
}

fn compat_value(model: &Model, key: &str) -> JsonValue {
    serde_json::to_value(model).expect("model json")["compat"][key].clone()
}

#[tokio::test]
async fn converts_empty_signature_thinking_to_text_by_default() {
    let payload = capture_payload(&make_model(None), &make_context("")).await;
    assert_eq!(
        assistant_content(&payload),
        json!([{ "type": "text", "text": "internal reasoning" }])
    );
}

#[tokio::test]
async fn preserves_empty_thinking_text_when_the_signature_is_present() {
    let payload = capture_payload(
        &make_model(None),
        &make_context_value(
            "signed-thinking",
            "",
            "xiaomi-token-plan-ams",
            "mimo-v2.5-pro",
        ),
    )
    .await;
    assert_eq!(
        assistant_content(&payload),
        json!([{ "type": "thinking", "thinking": "", "signature": "signed-thinking" }])
    );
}

#[tokio::test]
async fn preserves_empty_signature_thinking_when_allow_empty_signature_is_enabled() {
    let payload = capture_payload(&make_model(Some(true)), &make_context(" ")).await;
    assert_eq!(
        assistant_content(&payload),
        json!([{ "type": "thinking", "thinking": "internal reasoning", "signature": "" }])
    );
}

// Regression for #9676: Vercel AI Gateway emits unsigned thinking for translated models.
#[test]
fn allows_empty_thinking_signatures_for_every_vercel_ai_gateway_model() {
    let models = get_models("vercel-ai-gateway");
    assert!(!models.is_empty());
    assert!(models
        .iter()
        .all(|model| compat_value(model, "allowEmptySignature") == json!(true)));
}

// Regression for #9323: Fireworks emits unsigned thinking that must survive replay.
#[tokio::test]
async fn preserves_unsigned_thinking_for_fireworks() {
    for model_id in [
        "accounts/fireworks/models/deepseek-v4p1-flash",
        "accounts/fireworks/models/qwen3p8-max",
        "accounts/fireworks/models/qwen3p8-2p4t-a95b",
        "accounts/fireworks/models/nemotron-3-ultra-nvfp4",
    ] {
        let model = get_model("fireworks", model_id).expect("fireworks model");
        assert_eq!(
            compat_value(&model, "allowEmptySignature"),
            json!(true),
            "{model_id}"
        );
        let mut context = make_context_value("", "internal reasoning", "fireworks", model_id);
        context["messages"][1]["content"]
            .as_array_mut()
            .expect("assistant content")
            .push(json!({ "type": "text", "text": "answer" }));
        let payload = capture_payload(&model, &context).await;
        assert_eq!(
            assistant_content(&payload),
            json!([
                { "type": "thinking", "thinking": "internal reasoning", "signature": "" },
                { "type": "text", "text": "answer" },
            ]),
            "{model_id}"
        );
    }
}

// Regression for #9323: opting into unsigned replay must not change cross-model conversion.
#[tokio::test]
async fn still_converts_cross_model_fireworks_thinking_to_text() {
    let model = get_model("fireworks", "accounts/fireworks/models/deepseek-v4p1-flash")
        .expect("fireworks model");
    let payload = capture_payload(
        &model,
        &make_context_value(
            "",
            "internal reasoning",
            "fireworks",
            "accounts/fireworks/models/nemotron-3-ultra-nvfp4",
        ),
    )
    .await;
    assert_eq!(
        assistant_content(&payload),
        json!([{ "type": "text", "text": "internal reasoning" }])
    );
}

#[tokio::test]
async fn allows_empty_signatures_for_kimi_coding() {
    for model_id in ["k3"] {
        let model = get_model("kimi-coding", model_id).expect("kimi-coding model");
        assert_eq!(
            compat_value(&model, "allowEmptySignature"),
            json!(true),
            "{model_id}"
        );

        let payload = capture_payload(
            &model,
            &make_context_value(" ", "internal reasoning", "kimi-coding", model_id),
        )
        .await;
        assert_eq!(
            assistant_content(&payload),
            json!([{ "type": "thinking", "thinking": "internal reasoning", "signature": "" }]),
            "{model_id}"
        );
    }
}
