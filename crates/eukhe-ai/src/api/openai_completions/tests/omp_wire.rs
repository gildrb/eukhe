//! The reasoning fields of the shipped `openai-completions` models match
//! what oh-my-pi (omp) sends for the same provider, model and thinking
//! level (the omp-vs-eukhe wire comparison). Each table row is one
//! catalog model at one level; only the effort fields are compared.

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
                "{provider}/{id} {level_name}: sent {sent}, omp {want}"
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

/// omp: Xiaomi `MiMo` on the first-party hosts (`xiaomi`, the token plans)
/// resolves `supportsReasoningEffort: false` (catalog `compat/resolve.ts`
/// `isXiaomiMimo`) with the `zai` dialect, so a thinking level sends only
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

/// omp: Moonshot-native Kimi (`moonshot` provider, the `zai` dialect of
/// `classes/kimi.kdl` / `providers/moonshot.kdl`) supports
/// `reasoning_effort` (catalog `compat/resolve.ts`: only Grok, Xiaomi `MiMo`
/// and pre-5.2 Z.AI GLM lack it). K2.6 keeps every earlier turn's thinking
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

/// omp: a Kimi model always sends an output cap (catalog
/// `compat/resolve.ts` `alwaysSendMaxTokens: facts.is("kimi")`), also where
/// the catalog max is the whole window and the cap would otherwise be left
/// to the provider.
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

/// omp: Qwen on Hugging Face, Cloudflare Workers AI and `OpenCode` resolves
/// the `qwen` dialect (catalog `compat/resolve.ts` `thinkingFormat`: Qwen
/// off Fireworks/Venice/NVIDIA is `qwen`) whose disable mode is
/// `qwen-enable-thinking-false` (`ai/src/providers/openai-shared.ts`
/// `applyChatCompletionsCompatPolicy`): a level sends
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
