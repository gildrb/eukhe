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
