//! Port of `test/bedrock-thinking-payload.test.ts`.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_ai::api::bedrock_converse_stream::stream;
use eukhe_ai::types::ProviderStreamOptions;
use eukhe_ai::utils::transcript::normalize_context;
use eukhe_types::pi_ai::{Context, JsonValue, Model, StopReason};
use serde_json::{json, Value};

use super::support::{capture_payload_hook, get_model, options, user, AfterCapture, EnvGuard};

const THINKING_BINDING_CONTROLS_BETA: &str = "thinking-binding-controls-2026-08-01";

fn adaptive_with_binding() -> Value {
    json!({
        "type": "adaptive",
        "display": "summarized",
        "block_binding": { "prefix_mismatch_behavior": "drop_block" },
    })
}

async fn capture(model: &Model, context: Context, mut options: ProviderStreamOptions) -> JsonValue {
    let _env = EnvGuard::new(&[]).await;
    let slot = Arc::new(Mutex::new(None));
    options.stream.request.on_payload =
        Some(capture_payload_hook(slot.clone(), AfterCapture::Throw));
    let result = stream(model, &normalize_context(context), options)
        .result()
        .await;
    assert_eq!(result.stop_reason, StopReason::Error);
    let payload = slot.lock().unwrap_or_else(PoisonError::into_inner).take();
    payload.expect("Expected Bedrock payload to be captured before request abort")
}

async fn capture_payload(model: &Model, extra: Value) -> Value {
    let mut extra = extra;
    if extra.get("reasoning").is_none() {
        extra["reasoning"] = json!("high");
    }
    let context = Context {
        system_prompt: None,
        messages: vec![user("Hello")],
        tools: None,
    };
    capture(model, context, options(extra)).await
}

fn fields(payload: &Value) -> &Value {
    &payload["additionalModelRequestFields"]
}

/// The catalog's Opus 4.8 row: its thinking-level map sends native `xhigh`
/// (the effort comes from the map, not from the model id).
fn opus_48() -> Model {
    get_model("amazon-bedrock", "global.anthropic.claude-opus-4-8")
}

#[tokio::test]
async fn uses_adaptive_thinking_for_claude_opus_4_8_when_reasoning_is_enabled() {
    assert_adaptive("global.anthropic.claude-opus-4-8", "high", "high").await;
}

#[tokio::test]
async fn maps_xhigh_reasoning_to_effort_xhigh_for_claude_opus_4_8() {
    assert_adaptive(&opus_48().id, "xhigh", "xhigh").await;
}

/// Adaptive thinking without block binding: omp binds only prefix-bound
/// models (`classes/anthropic.kdl` `thinking-prefix-binding`: Fable 5.1+,
/// Opus, Sonnet and Haiku 5.5).
async fn assert_adaptive(model_id: &str, reasoning: &str, effort: &str) {
    let model = get_model("amazon-bedrock", model_id);
    let payload = capture_payload(&model, json!({ "reasoning": reasoning })).await;
    assert_eq!(
        fields(&payload),
        &json!({
            "thinking": { "type": "adaptive", "display": "summarized" },
            "output_config": { "effort": effort },
        }),
        "{model_id}"
    );
}

#[tokio::test]
async fn uses_adaptive_thinking_for_claude_fable_5_when_reasoning_is_enabled() {
    assert_adaptive("global.anthropic.claude-fable-5", "high", "high").await;
}

#[tokio::test]
async fn uses_adaptive_thinking_for_claude_sonnet_5_when_reasoning_is_enabled() {
    assert_adaptive("global.anthropic.claude-sonnet-5", "high", "high").await;
}

#[tokio::test]
async fn uses_adaptive_thinking_for_claude_opus_5_when_reasoning_is_enabled() {
    assert_adaptive("global.anthropic.claude-opus-5", "high", "high").await;
}

#[tokio::test]
async fn maps_xhigh_reasoning_to_effort_xhigh_for_claude_opus_5() {
    assert_adaptive("global.anthropic.claude-opus-5", "xhigh", "xhigh").await;
}

#[tokio::test]
async fn maps_xhigh_reasoning_to_effort_xhigh_for_claude_fable_5() {
    assert_adaptive("global.anthropic.claude-fable-5", "xhigh", "xhigh").await;
}

/// omp binds signed thinking only on prefix-bound models (Fable 5.1+, Opus,
/// Sonnet and Haiku 5.5); the 4.7 to 5 line sends no `block_binding` and
/// no binding beta.
#[tokio::test]
async fn block_binding_goes_only_to_prefix_bound_models() {
    let mut bound = Vec::new();
    for model_id in [
        "global.anthropic.claude-opus-4-7",
        "global.anthropic.claude-opus-4-8",
        "global.anthropic.claude-opus-5",
        "global.anthropic.claude-sonnet-5",
        "global.anthropic.claude-fable-5",
        "global.anthropic.claude-fable-5-1",
        "global.anthropic.claude-haiku-5-5",
        "global.anthropic.claude-sonnet-5-5",
        "global.anthropic.claude-opus-5-5",
    ] {
        let model = get_model("amazon-bedrock", model_id);
        let payload = capture_payload(&model, json!({})).await;
        let binding = fields(&payload)["thinking"].get("block_binding").is_some();
        let beta = fields(&payload).get("anthropic_beta")
            == Some(&json!([THINKING_BINDING_CONTROLS_BETA]));
        assert_eq!(binding, beta, "{model_id}");
        if binding {
            bound.push(model_id);
        }
    }
    assert_eq!(
        bound,
        [
            "global.anthropic.claude-fable-5-1",
            "global.anthropic.claude-haiku-5-5",
            "global.anthropic.claude-sonnet-5-5",
            "global.anthropic.claude-opus-5-5",
        ]
    );
}

// https://github.com/earendil-works/pi/issues/10324
#[tokio::test]
async fn sends_block_binding_and_the_binding_beta_for_claude_opus_5_5() {
    let model = get_model("amazon-bedrock", "global.anthropic.claude-opus-5-5");
    let payload = capture_payload(&model, json!({})).await;
    assert_eq!(fields(&payload)["thinking"], adaptive_with_binding());
    assert_eq!(
        fields(&payload)["anthropic_beta"],
        json!([THINKING_BINDING_CONTROLS_BETA])
    );
}

// Bedrock rejects block_binding on 4.6 models (#10324).
#[tokio::test]
async fn omits_block_binding_for_opus_4_6() {
    let model = get_model("amazon-bedrock", "global.anthropic.claude-opus-4-6-v1");
    let payload = capture_payload(&model, json!({})).await;
    assert_eq!(
        fields(&payload)["thinking"],
        json!({ "type": "adaptive", "display": "summarized" })
    );
    assert!(fields(&payload).get("anthropic_beta").is_none());
}

/// omp makes only Opus 4.6 adaptive on Bedrock (`amazon-bedrock.kdl`
/// `thinking-mode "anthropic-adaptive"` under `family "opus"`, revision
/// 4.6): Sonnet 4.6 there, regional profiles included, takes budget
/// thinking.
#[tokio::test]
async fn sonnet_4_6_takes_budget_thinking_on_bedrock() {
    for model_id in [
        "anthropic.claude-sonnet-4-6",
        "eu.anthropic.claude-sonnet-4-6",
        "global.anthropic.claude-sonnet-4-6",
    ] {
        let model = get_model("amazon-bedrock", model_id);
        let payload = capture_payload(&model, json!({ "reasoning": "low" })).await;
        assert_eq!(
            fields(&payload),
            &json!({ "thinking": { "type": "enabled", "budget_tokens": 2048, "display": "summarized" } }),
            "{model_id}"
        );
    }
}

#[tokio::test]
async fn omits_display_for_govcloud_model_ids_on_non_adaptive_claude_thinking() {
    let model = Model {
        id: "us-gov.anthropic.claude-sonnet-4-5-20250929-v1:0".into(),
        name: "Claude Sonnet 4.5 (GovCloud)".into(),
        ..get_model(
            "amazon-bedrock",
            "us.anthropic.claude-sonnet-4-5-20250929-v1:0",
        )
    };
    let payload = capture_payload(&model, json!({})).await;
    assert_eq!(
        fields(&payload)["thinking"],
        json!({ "type": "enabled", "budget_tokens": 16384 })
    );
    assert!(fields(&payload).get("anthropic_beta").is_none());
}

#[tokio::test]
async fn omits_display_for_govcloud_regions_on_adaptive_claude_thinking() {
    let payload = capture_payload(&opus_48(), json!({ "region": "us-gov-west-1" })).await;
    assert_eq!(fields(&payload)["thinking"], json!({ "type": "adaptive" }));
    assert_eq!(
        fields(&payload)["output_config"],
        json!({ "effort": "high" })
    );
    assert!(fields(&payload).get("anthropic_beta").is_none());
}

#[tokio::test]
#[ignore = "needs AWS credentials (AWS_PROFILE, AWS_ACCESS_KEY_ID+AWS_SECRET_ACCESS_KEY, or AWS_BEARER_TOKEN_BEDROCK); run with --ignored"]
async fn uses_the_model_max_tokens_cap_instead_of_bedrocks_4096_token_default_for_adaptive_claude_models(
) {
    assert!(super::has_bedrock_credentials());
    let model = Model {
        max_tokens: 6000,
        ..get_model("amazon-bedrock", "global.anthropic.claude-sonnet-4-6")
    };
    let context = normalize_context(Context {
        system_prompt: Some(
            "You are a deterministic text generator. Follow the requested output format exactly."
                .into(),
        ),
        messages: vec![user(
            "Output exactly 5200 repetitions of the token alpha, separated by single spaces. Do not number them. Do not use markdown. Do not add any other text.",
        )],
        tools: None,
    });
    let response = stream(&model, &context, options(json!({ "reasoning": "low" })))
        .result()
        .await;
    assert_ne!(
        response.stop_reason,
        StopReason::Error,
        "{:?}",
        response.error_message
    );
    assert!(response.usage.output > 4096);
}

fn profile_model(name: &str, base: &str) -> Model {
    Model {
        id: "arn:aws:bedrock:us-east-1:123456789012:application-inference-profile/my-profile"
            .into(),
        name: name.into(),
        ..get_model("amazon-bedrock", base)
    }
}

#[tokio::test]
async fn uses_adaptive_thinking_when_model_name_contains_the_model_name_but_arn_does_not() {
    let model = profile_model("Claude Opus 4.6", "global.anthropic.claude-opus-4-6-v1");
    let payload = capture_payload(&model, json!({})).await;
    assert_eq!(
        fields(&payload)["thinking"],
        json!({ "type": "adaptive", "display": "summarized" })
    );
    assert_eq!(
        fields(&payload)["output_config"],
        json!({ "effort": "high" })
    );
}

#[tokio::test]
async fn injects_cache_points_when_model_name_identifies_a_supported_claude_model() {
    let model = profile_model("Claude Sonnet 4.6", "global.anthropic.claude-opus-4-6-v1");
    let context = Context {
        system_prompt: Some("You are helpful.".into()),
        messages: vec![user("Hello")],
        tools: None,
    };
    let payload = capture(&model, context, ProviderStreamOptions::default()).await;
    let system = payload["system"].as_array().expect("system");
    assert_eq!(system.len(), 2);
    assert!(system[1].get("cachePoint").is_some());
    let messages = payload["messages"].as_array().expect("messages");
    let last = messages.last().expect("message")["content"]
        .as_array()
        .expect("content")
        .last()
        .cloned()
        .expect("block");
    assert!(last.get("cachePoint").is_some());
}

/// eukhe addition: with a cache breakpoint the shared prefix and the
/// session's tail are system blocks of their own, each with a cache point.
#[tokio::test]
async fn a_cache_breakpoint_gives_the_shared_prefix_its_own_cache_point() {
    let model = profile_model("Claude Sonnet 4.6", "global.anthropic.claude-opus-4-6-v1");
    let system: eukhe_types::pi_ai::Message = serde_json::from_value(json!({
        "role": "system",
        "content": "",
        "sections": { "core": "Core.", "cwd": "Working directory: /a" },
        "timestamp": 0,
    }))
    .expect("system message");
    let context = Context {
        system_prompt: None,
        messages: vec![system, user("Hello")],
        tools: None,
    };
    let mut options = ProviderStreamOptions::default();
    options.stream.system_cache_breakpoint = Some("core".into());
    let payload = capture(&model, context, options).await;
    assert_eq!(
        payload["system"],
        json!([
            { "text": "Core." },
            { "cachePoint": { "type": "default" } },
            { "text": "Working directory: /a" },
            { "cachePoint": { "type": "default" } },
        ])
    );
}

#[tokio::test]
async fn falls_back_to_fixed_budget_thinking_for_non_adaptive_claude_via_model_name() {
    let model = profile_model(
        "Claude Sonnet 4.5",
        "us.anthropic.claude-sonnet-4-5-20250929-v1:0",
    );
    let payload = capture_payload(&model, json!({})).await;
    assert_eq!(fields(&payload)["thinking"]["type"], json!("enabled"));
    assert!(fields(&payload)["thinking"]["budget_tokens"].is_number());
    assert!(fields(&payload).get("anthropic_beta").is_none());
}

/// omp (`amazon-bedrock.ts` `buildAdditionalModelRequestFields`) adds the
/// interleaved-thinking beta to budget thinking only when the caller sets
/// `interleavedThinking`; its agent never does.
#[tokio::test]
async fn budget_thinking_sends_the_interleaved_beta_only_when_asked() {
    let model = get_model(
        "amazon-bedrock",
        "global.anthropic.claude-opus-4-5-20251101-v1:0",
    );
    let unasked = capture_payload(&model, json!({ "reasoning": "low" })).await;
    let asked = capture_payload(
        &model,
        json!({ "reasoning": "low", "interleavedThinking": true }),
    )
    .await;
    assert_eq!(
        (fields(&unasked), &fields(&asked)["anthropic_beta"]),
        (
            &json!({ "thinking": { "type": "enabled", "budget_tokens": 2048, "display": "summarized" } }),
            &json!(["interleaved-thinking-2025-05-14"])
        )
    );
}

// Regression for #9331: the configured thinking level never reached OpenAI models on Bedrock.
#[tokio::test]
async fn sends_reasoning_as_reasoning_effort_for_gpt_6_and_gpt_5_6() {
    for (reasoning, effort) in [
        ("minimal", "low"),
        ("low", "low"),
        ("medium", "medium"),
        ("high", "high"),
        ("xhigh", "xhigh"),
        ("max", "max"),
    ] {
        for id in [
            "global.openai.gpt-6-sol",
            "us.openai.gpt-6-luna",
            "global.openai.gpt-5.6-sol",
        ] {
            let payload = capture_payload(
                &get_model("amazon-bedrock", id),
                json!({ "reasoning": reasoning }),
            )
            .await;
            assert_eq!(
                fields(&payload),
                &json!({ "reasoning": { "effort": effort } }),
                "{id}"
            );
        }
    }
}

#[tokio::test]
async fn sends_reasoning_effort_when_only_model_name_identifies_a_gpt_model() {
    let model = profile_model("GPT-6 Sol", "global.openai.gpt-6-sol");
    let payload = capture_payload(&model, json!({ "reasoning": "medium" })).await;
    assert_eq!(
        fields(&payload),
        &json!({ "reasoning": { "effort": "medium" } })
    );
}

fn budget_thinking(budget: u64) -> Value {
    json!({ "thinking": { "type": "enabled", "budget_tokens": budget, "display": "summarized" } })
}

/// omp (`amazon-bedrock.ts` `buildAdditionalModelRequestFields`) sends
/// every reasoning model outside the adaptive and effort modes Anthropic's
/// budget thinking block: gpt-oss, Nova, `DeepSeek`, GLM, Grok before 4.6 and
/// the rest, with the default budget of the level (high past high).
#[tokio::test]
async fn non_claude_budget_models_send_the_thinking_budget() {
    for model_id in [
        "openai.gpt-oss-120b-1:0",
        "amazon.nova-2-lite-v1:0",
        "deepseek.v3.2",
        "zai.glm-5",
        "xai.grok-4.3",
    ] {
        let model = get_model("amazon-bedrock", model_id);
        for (reasoning, budget) in [("minimal", 1024), ("medium", 8192), ("xhigh", 16384)] {
            let payload = capture_payload(&model, json!({ "reasoning": reasoning })).await;
            assert_eq!(
                fields(&payload),
                &budget_thinking(budget),
                "{model_id} {reasoning}"
            );
        }
    }
}

/// omp's effort mode on Bedrock (`amazon-bedrock.kdl`: Grok 4.6+, the
/// `*.moonshotai.kimi-k3` profiles) sends `reasoning.effort`.
#[tokio::test]
async fn effort_mode_models_send_a_nested_reasoning_effort() {
    for model_id in [
        "xai.grok-4.6",
        "global.xai.grok-4.7",
        "us.moonshotai.kimi-k3",
    ] {
        let model = get_model("amazon-bedrock", model_id);
        for effort in ["low", "high"] {
            let payload = capture_payload(&model, json!({ "reasoning": effort })).await;
            assert_eq!(
                fields(&payload),
                &json!({ "reasoning": { "effort": effort } }),
                "{model_id}"
            );
        }
    }
}

#[tokio::test]
async fn sends_no_reasoning_fields_when_reasoning_is_off() {
    let context = Context {
        system_prompt: None,
        messages: vec![user("Hello")],
        tools: None,
    };
    let payload = capture(
        &get_model("amazon-bedrock", "global.openai.gpt-6-sol"),
        context,
        ProviderStreamOptions::default(),
    )
    .await;
    assert_eq!(payload.get("additionalModelRequestFields"), None);
}

async fn off_fields(model_id: &str) -> Option<Value> {
    let context = Context {
        system_prompt: None,
        messages: vec![user("Hello")],
        tools: None,
    };
    let model = get_model("amazon-bedrock", model_id);
    let payload = capture(&model, context, ProviderStreamOptions::default()).await;
    payload.get("additionalModelRequestFields").cloned()
}

/// omp with thinking off (`amazon-bedrock.ts`
/// `buildAdditionalModelRequestFields` and the binding step of
/// `streamBedrock`): Claude Haiku 5.5 takes the explicit `disabled` with
/// the lowest effort (`compat.disabledThinking`); the other prefix-bound
/// models think adaptively without a thinking field, so they send the bare
/// adaptive tag with the block binding and its beta; the rest send nothing.
#[tokio::test]
async fn thinking_off_is_disabled_on_haiku_5_5_and_the_bare_binding_on_prefix_bound_claude() {
    assert_eq!(
        off_fields("global.anthropic.claude-haiku-5-5").await,
        Some(json!({
            "thinking": { "type": "disabled" },
            "output_config": { "effort": "low" },
        }))
    );
    for model_id in [
        "global.anthropic.claude-sonnet-5-5",
        "global.anthropic.claude-opus-5-5",
        "global.anthropic.claude-fable-5-1",
    ] {
        assert_eq!(
            off_fields(model_id).await,
            Some(json!({
                "thinking": {
                    "type": "adaptive",
                    "block_binding": { "prefix_mismatch_behavior": "drop_block" },
                },
                "anthropic_beta": [THINKING_BINDING_CONTROLS_BETA],
            })),
            "{model_id}"
        );
    }
    for model_id in [
        "global.anthropic.claude-opus-4-8",
        "global.anthropic.claude-opus-4-6-v1",
        "global.anthropic.claude-sonnet-4-6",
    ] {
        assert_eq!(off_fields(model_id).await, None, "{model_id}");
    }
}
