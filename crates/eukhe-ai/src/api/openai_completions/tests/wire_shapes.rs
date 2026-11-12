//! The reasoning fields of the shipped `openai-completions` models match
//! the expected wire fields for each provider, model and thinking level.
//! Each table row is one catalog model at one level; only the effort
//! fields are compared.

use std::sync::PoisonError;

use serde_json::json;

use super::support::{payload_recorder, sse_fetch, stop_chunks};
use crate::providers::all::get_builtin_model;
use crate::types::{
    Context, JsonValue, Model, ProviderEnv, ProviderRequestOptions, SimpleStreamOptions,
    StreamOptions, ThinkingLevel,
};

/// The request fields that carry a reasoning control.
const EFFORT_FIELDS: [&str; 6] = [
    "reasoning_effort",
    "thinking",
    "enable_thinking",
    "preserve_thinking",
    "chat_template_kwargs",
    "reasoning",
];

fn model(provider: &str, id: &str) -> Model {
    get_builtin_model(provider, id).unwrap_or_else(|| panic!("missing model {provider}/{id}"))
}

/// The thinking levels a row names; `off` sends no reasoning option.
fn level(name: &str) -> Option<ThinkingLevel> {
    match name {
        "off" => None,
        other => Some(
            serde_json::from_value(json!(other))
                .unwrap_or_else(|_| panic!("unknown thinking level {other}")),
        ),
    }
}

/// The first payload of one `streamSimple` call at `reasoning`. The env
/// configures Cloudflare AI Gateway's account and gateway.
async fn payload(model: &Model, reasoning: Option<ThinkingLevel>) -> JsonValue {
    let (fetch, _requests) = sse_fetch(stop_chunks());
    let (hook, seen) = payload_recorder();
    let options = SimpleStreamOptions {
        stream: StreamOptions {
            request: ProviderRequestOptions {
                api_key: Some("test-key".to_owned()),
                fetch: Some(fetch),
                on_payload: Some(hook),
                env: Some(ProviderEnv::from([
                    ("CLOUDFLARE_ACCOUNT_ID".to_owned(), "account-id".to_owned()),
                    ("CLOUDFLARE_GATEWAY_ID".to_owned(), "gateway-id".to_owned()),
                ])),
                ..ProviderRequestOptions::default()
            },
            ..StreamOptions::default()
        },
        reasoning,
        ..SimpleStreamOptions::default()
    };
    let context: Context = serde_json::from_value(json!({
        "messages": [{ "role": "user", "content": "test", "timestamp": 0 }],
    }))
    .expect("valid context JSON");
    let message = super::support::builtin()
        .stream_simple(model, context, options.into())
        .result()
        .await;
    let payloads = seen.lock().unwrap_or_else(PoisonError::into_inner);
    payloads
        .first()
        .cloned()
        .unwrap_or_else(|| panic!("no payload captured: {:?}", message.error_message))
}

/// The effort fields of the payload `provider/id` sends at `level_name`.
async fn effort_fields(provider: &str, id: &str, level_name: &str) -> JsonValue {
    let payload = payload(&model(provider, id), level(level_name)).await;
    let fields: serde_json::Map<String, JsonValue> = EFFORT_FIELDS
        .iter()
        .filter_map(|key| {
            payload
                .get(*key)
                .map(|value| ((*key).to_owned(), value.clone()))
        })
        .collect();
    JsonValue::Object(fields)
}

/// Every `(provider, id, level)` row sends `expected` effort fields.
async fn assert_rows(rows: &[(&str, &str, &str)], expected: impl Fn(&str) -> JsonValue) {
    let mut mismatches = Vec::new();
    for (provider, id, level_name) in rows {
        let sent = effort_fields(provider, id, level_name).await;
        let want = expected(level_name);
        if sent != want {
            mismatches.push(format!(
                "{provider}/{id} {level_name}: sent {sent}, expected {want}"
            ));
        }
    }
    assert!(mismatches.is_empty(), "{}", mismatches.join("\n"));
}

/// Every model of `providers` at every level in `levels`.
fn catalog_rows<'a>(
    providers: &[&'a str],
    keep: impl Fn(&Model) -> bool,
    levels: &[&'a str],
) -> Vec<(&'a str, String, &'a str)> {
    let mut rows = Vec::new();
    for provider in providers {
        for model in crate::providers::all::get_builtin_models(provider) {
            if keep(&model) {
                for level_name in levels {
                    rows.push((*provider, model.id.clone(), *level_name));
                }
            }
        }
    }
    rows
}

/// [`catalog_rows`] in the shape [`assert_rows`] takes.
fn borrowed<'a>(rows: &'a [(&'a str, String, &'a str)]) -> Vec<(&'a str, &'a str, &'a str)> {
    rows.iter()
        .map(|(provider, id, level_name)| (*provider, id.as_str(), *level_name))
        .collect()
}

const THINKING_LEVELS: [&str; 6] = ["minimal", "low", "medium", "high", "xhigh", "max"];

/// Xiaomi `MiMo` on the first-party hosts (`xiaomi`, the token plans) takes
/// no `reasoning_effort` and speaks the `zai` dialect, so a thinking level
/// sends only
/// `thinking: { type: "enabled" }` and off sends `{ type: "disabled" }`.
#[tokio::test]
async fn xiaomi_mimo_sends_thinking_without_reasoning_effort() {
    let providers = [
        "xiaomi",
        "xiaomi-token-plan-ams",
        "xiaomi-token-plan-cn",
        "xiaomi-token-plan-sgp",
    ];
    let mut levels = THINKING_LEVELS.to_vec();
    levels.push("off");
    let rows = catalog_rows(&providers, |model| model.reasoning, &levels);
    assert!(!rows.is_empty());
    assert_rows(&borrowed(&rows), |level_name| {
        if level_name == "off" {
            json!({ "thinking": { "type": "disabled" } })
        } else {
            json!({ "thinking": { "type": "enabled" } })
        }
    })
    .await;
}

/// Moonshot-native Kimi (`moonshot` provider, the `zai` dialect) supports
/// `reasoning_effort` (only Grok, Xiaomi `MiMo` and pre-5.2 Z.AI GLM lack
/// it). K2.6 keeps every earlier turn's thinking
/// (`thinkingKeep: "all"`): a level sends
/// `thinking: { type: "enabled", keep: "all" }` plus `reasoning_effort`.
/// K2.7 Code always thinks (`requiresEnabledThinking`, disable mode
/// `omit`): a level sends `reasoning_effort` alone.
#[tokio::test]
async fn moonshot_kimi_sends_reasoning_effort_and_k2_6_keeps_thinking() {
    for provider in ["moonshotai", "moonshotai-cn"] {
        for (level_name, effort) in [
            ("minimal", "minimal"),
            ("low", "low"),
            ("medium", "medium"),
            ("high", "high"),
            ("xhigh", "high"),
        ] {
            assert_rows(&[(provider, "kimi-k2.6", level_name)], |_| {
                json!({
                    "reasoning_effort": effort,
                    "thinking": { "type": "enabled", "keep": "all" },
                })
            })
            .await;
            for id in ["kimi-k2.7-code", "kimi-k2.7-code-highspeed"] {
                assert_rows(
                    &[(provider, id, level_name)],
                    |_| json!({ "reasoning_effort": effort }),
                )
                .await;
            }
        }
    }
}

/// A Kimi model always sends an output cap: a request without a caller's
/// cap carries the catalog max on every host whose rulebook rule does not
/// leave the default cap out.
#[tokio::test]
async fn kimi_always_sends_an_output_cap() {
    for provider in ["moonshotai", "moonshotai-cn"] {
        for id in [
            "kimi-k2.6",
            "kimi-k2.7-code",
            "kimi-k2.7-code-highspeed",
            "kimi-k3",
        ] {
            for level_name in ["off", "high"] {
                let payload = payload(&model(provider, id), level(level_name)).await;
                assert!(
                    payload.get("max_tokens").is_some_and(JsonValue::is_u64),
                    "{provider}/{id} {level_name}: no max_tokens in {payload}"
                );
            }
        }
    }
}

/// A chat-completions reasoning model whose id names Qwen.
fn is_qwen_chat(model: &Model) -> bool {
    model.reasoning
        && model.api == "openai-completions"
        && model.id.to_ascii_lowercase().contains("qwen")
}

/// Qwen on Hugging Face, Cloudflare Workers AI and `OpenCode` speaks the
/// `qwen` dialect (Qwen off Fireworks/Venice/NVIDIA is `qwen`) whose
/// disable mode is `qwen-enable-thinking-false`: a level sends
/// `enable_thinking: true` and no `reasoning_effort`; off sends `false`.
#[tokio::test]
async fn qwen_sends_enable_thinking_without_reasoning_effort() {
    let rows = catalog_rows(
        &["huggingface", "cloudflare-ai-gateway", "opencode"],
        is_qwen_chat,
        &THINKING_LEVELS,
    );
    assert!(!rows.is_empty());
    assert_rows(&borrowed(&rows), |_| json!({ "enable_thinking": true })).await;
    assert_rows(
        &[
            ("huggingface", "Qwen/Qwen3-32B", "off"),
            (
                "cloudflare-ai-gateway",
                "workers-ai/@cf/qwen/qwen3-30b-a3b-fp8",
                "off",
            ),
            ("opencode", "qwen3.8-max", "off"),
        ],
        |_| json!({ "enable_thinking": false }),
    )
    .await;
}

/// Cloudflare Workers AI chat models (Qwen aside) take `OpenAI`-style
/// `reasoning_effort` (only Grok, Xiaomi `MiMo` and pre-5.2 Z.AI GLM lack
/// it; the dialect is `openai`, `DeepSeek` included).
#[tokio::test]
async fn cloudflare_workers_ai_sends_reasoning_effort() {
    let rows = catalog_rows(
        &["cloudflare-ai-gateway"],
        |model| {
            model.reasoning
                && model.api == "openai-completions"
                && model.id.starts_with("workers-ai/")
                && !is_qwen_chat(model)
        },
        &["high"],
    );
    assert!(!rows.is_empty());
    assert_rows(&borrowed(&rows), |_| json!({ "reasoning_effort": "high" })).await;
}

/// `OpenCode`'s Kimi K2.6 and `OpenCode` Go's `DeepSeek` lanes speak the
/// `openai` dialect (`zai` is only for Moonshot-native Kimi, Z.AI, Zhipu and
/// Xiaomi `MiMo`): a level sends `reasoning_effort` alone, no `thinking`
/// object. `OpenCode` Go's `LongCat` 2.5 Preview has no effort tiers: a
/// level sends no effort.
#[tokio::test]
async fn opencode_kimi_and_deepseek_send_reasoning_effort_only() {
    assert_rows(
        &[
            ("opencode", "kimi-k2.6", "high"),
            ("opencode-go", "deepseek-v4-pro", "high"),
            ("opencode-go", "deepseek-v4-flash-vision-exp", "high"),
            ("opencode-go", "deepseek-v4.1-flash", "high"),
        ],
        |_| json!({ "reasoning_effort": "high" }),
    )
    .await;
    assert_rows(
        &[("opencode-go", "longcat-2.5-preview-free", "high")],
        |_| json!({}),
    )
    .await;
}

/// Off on a model of the `openai` dialect (disable mode `lowest-effort`)
/// sends the model's lowest offered effort, not nothing, and not `"none"` where
/// that lowest effort matches the model's ladder.
#[tokio::test]
async fn off_sends_the_lowest_offered_effort() {
    assert_rows(
        &[
            ("huggingface", "google/gemma-4-26B-A4B-it", "off"),
            ("huggingface", "google/gemma-4-31B-it", "off"),
            ("huggingface", "moonshotai/Kimi-K2.5", "off"),
            ("huggingface", "moonshotai/Kimi-K2.6", "off"),
        ],
        |_| json!({ "reasoning_effort": "minimal" }),
    )
    .await;
    assert_rows(
        &[
            ("huggingface", "deepseek-ai/DeepSeek-V4.1-Flash", "off"),
            ("huggingface", "XiaomiMiMo/MiMo-V2.5", "off"),
            ("huggingface", "XiaomiMiMo/MiMo-V2.5-Pro", "off"),
        ],
        |_| json!({ "reasoning_effort": "low" }),
    )
    .await;
}

/// Fireworks is a chat-completions provider (no Anthropic route; effort
/// thinking) whose effort map sends
/// minimal as `"none"`: every catalog model is `openai-completions` and a
/// level sends `reasoning_effort` (off: the lowest offered effort).
#[tokio::test]
async fn fireworks_models_send_chat_completions_reasoning_effort() {
    let other_api: Vec<String> = crate::providers::all::get_builtin_models("fireworks")
        .into_iter()
        .filter(|model| model.api != "openai-completions")
        .map(|model| format!("{} ({})", model.id, model.api))
        .collect();
    assert!(other_api.is_empty(), "not chat-completions: {other_api:?}");
    let effort = |effort: &str| json!({ "reasoning_effort": effort });
    for (id, level_name, want) in [
        ("deepseek-v4p1-flash", "off", effort("low")),
        ("deepseek-v4p1-flash", "high", effort("high")),
        ("ember-1", "off", effort("none")),
        ("ember-1", "medium", effort("medium")),
        ("gpt-oss-120b", "low", effort("low")),
        ("inkling", "off", effort("none")),
        ("inkling", "minimal", effort("none")),
        ("inkling", "high", effort("high")),
        ("nemotron-3-ultra-nvfp4", "minimal", effort("none")),
        ("qwen3p8-max", "low", effort("low")),
        ("minimax-m3", "high", json!({})),
    ] {
        let id = format!("accounts/fireworks/models/{id}");
        assert_rows(&[("fireworks", id.as_str(), level_name)], |_| want.clone()).await;
    }
}

/// `OpenCode` Go serves `MiniMax` M3 on chat completions with
/// `reasoning_effort`, not as an Anthropic body.
#[tokio::test]
async fn opencode_go_minimax_m3_sends_chat_completions_reasoning_effort() {
    assert_eq!(model("opencode-go", "minimax-m3").api, "openai-completions");
    assert_rows(
        &[("opencode-go", "minimax-m3", "high")],
        |_| json!({ "reasoning_effort": "high" }),
    )
    .await;
}

/// The output-cap field `payload` carries, if any.
fn cap_field(payload: &JsonValue) -> Option<&'static str> {
    ["max_tokens", "max_completion_tokens"]
        .into_iter()
        .find(|key| payload.get(*key).is_some())
}

/// The output-cap field is `max_tokens` on Fireworks and on the `OpenCode`
/// Go `DeepSeek` V4 Flash/Pro lanes, else `max_completion_tokens` (Cloudflare
/// Workers AI,
/// `OpenCode`, `OpenCode` Go).
#[tokio::test]
async fn output_cap_field_matches_the_reference() {
    let expected_field = |provider: &str, id: &str| match (provider, id) {
        ("fireworks", _) | ("opencode-go", "deepseek-v4-flash" | "deepseek-v4-pro") => "max_tokens",
        _ => "max_completion_tokens",
    };
    let mut wrong = Vec::new();
    for (provider, prefix) in [
        ("fireworks", ""),
        ("cloudflare-ai-gateway", "workers-ai/"),
        ("opencode", ""),
        ("opencode-go", ""),
    ] {
        for model in crate::providers::all::get_builtin_models(provider) {
            if model.api != "openai-completions" || !model.id.starts_with(prefix) {
                continue;
            }
            let payload = payload(&model, level("high").filter(|_| model.reasoning)).await;
            let sent = cap_field(&payload);
            let field = expected_field(provider, &model.id);
            if sent.is_some_and(|sent| sent != field) {
                wrong.push(format!(
                    "{provider}/{}: {sent:?}, expected {field}",
                    model.id
                ));
            }
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}
