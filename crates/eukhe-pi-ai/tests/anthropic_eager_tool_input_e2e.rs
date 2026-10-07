//! Port of `test/anthropic-eager-tool-input-e2e.test.ts`.
//!
//! TS generates one `it.skipIf(!apiKey)` per provider; here each probe group
//! is one `#[ignore]`d test that runs every provider case with a key
//! (`get_env_api_key`, or `PI_TEST_GITHUB_COPILOT_TOKEN` for
//! `github-copilot`) and reports all failures. TS `{ retry: 2 }` is kept as
//! up to three attempts per case.

mod anthropic_support;

use std::cmp::Ordering;

use anthropic_support::resolve_test_api_key;
use eukhe_pi_ai::compat::{complete, get_env_api_key, get_models, get_providers};
use eukhe_pi_ai::types::ProviderStreamOptions;
use eukhe_types::pi_ai::{Context, Model, StopReason};
use serde_json::json;

struct E2eCase {
    name: String,
    provider: String,
    model: Model,
    api_key: Option<String>,
}

fn get_e2e_api_key(provider: &str) -> Option<String> {
    if provider == "github-copilot" {
        return resolve_test_api_key("github-copilot");
    }
    get_env_api_key(provider, None)
}

fn get_anthropic_messages_models(provider: &str) -> Vec<Model> {
    get_models(provider)
        .into_iter()
        .filter(|model| model.api == "anthropic-messages")
        .collect()
}

fn anthropic_messages_cases() -> Vec<E2eCase> {
    get_providers()
        .into_iter()
        .flat_map(|provider| {
            get_anthropic_messages_models(provider)
                .into_iter()
                .map(move |model| E2eCase {
                    name: format!("{provider}/{}", model.id),
                    provider: provider.to_owned(),
                    model,
                    api_key: get_e2e_api_key(provider),
                })
        })
        .collect()
}

fn get_probe_priority(model: &Model) -> f64 {
    let model_id = model.id.to_lowercase();
    let mut priority = model.cost.input + model.cost.output;

    // Prefer current Claude 4 Haiku routes when present: they are cheap and avoid
    // stale Claude 3.x aliases that can remain in catalogs after upstream removal.
    if model_id.contains("haiku") && (model_id.contains("4-5") || model_id.contains("4.5")) {
        priority -= 1000.0;
    } else if model_id.contains("sonnet") && (model_id.contains("4-") || model_id.contains("4.")) {
        priority -= 750.0;
    } else if model_id.contains("claude") && (model_id.contains("4-") || model_id.contains("4.")) {
        priority -= 500.0;
    }

    priority
}

fn select_one_case_per_provider(cases: Vec<E2eCase>) -> Vec<E2eCase> {
    let mut by_provider: Vec<(String, Vec<E2eCase>)> = Vec::new();
    for test_case in cases {
        match by_provider
            .iter_mut()
            .find(|(provider, _)| *provider == test_case.provider)
        {
            Some((_, provider_cases)) => provider_cases.push(test_case),
            None => by_provider.push((test_case.provider.clone(), vec![test_case])),
        }
    }
    by_provider
        .into_iter()
        .filter_map(|(_, mut provider_cases)| {
            provider_cases.sort_by(|a, b| {
                get_probe_priority(&a.model)
                    .partial_cmp(&get_probe_priority(&b.model))
                    .unwrap_or(Ordering::Equal)
                    .then_with(|| a.model.id.cmp(&b.model.id))
            });
            provider_cases.into_iter().next()
        })
        .collect()
}

fn with_eager_tool_input_streaming(model: &Model) -> Model {
    let mut value = serde_json::to_value(model).expect("model json");
    let mut compat = value.get("compat").cloned().unwrap_or_else(|| json!({}));
    compat["supportsEagerToolInputStreaming"] = json!(true);
    value["compat"] = compat;
    serde_json::from_value(value).expect("model")
}

/// `Err` describes the failed expectation.
async fn expect_tool_enabled_request_accepted(model: &Model, api_key: &str) -> Result<(), String> {
    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = Some(api_key.to_owned());
    options.stream.max_tokens = Some(128);
    options.extra.insert("thinkingEnabled".into(), json!(false));
    let context: Context = serde_json::from_value(json!({
        "systemPrompt": "You are a concise assistant. Use tools when useful.",
        "messages": [{
            "role": "user",
            "content": "Call echo_value with value set to eager-input-streaming-compat.",
            "timestamp": 1,
        }],
        "tools": [{
            "name": "echo_value",
            "description": "Echo a string value",
            "parameters": {
                "type": "object",
                "properties": { "value": { "description": "The value to echo", "type": "string" } },
                "required": ["value"],
            },
        }],
    }))
    .expect("context");
    let response = complete(model, context, options)
        .await
        .map_err(|error| error.to_string())?;

    if let Some(message) = response.error_message.filter(|message| !message.is_empty()) {
        return Err(message);
    }
    if response.stop_reason == StopReason::Error {
        return Err("stopReason was error".to_owned());
    }
    Ok(())
}

/// Runs each keyed case with TS `{ retry: 2 }` and panics listing failures.
async fn run_probe_cases(cases: Vec<(String, Model, Option<String>)>, label: &str) {
    let mut failures = Vec::new();
    for (name, model, api_key) in cases {
        let Some(api_key) = api_key else { continue };
        let mut last = Ok(());
        for _attempt in 0..3 {
            last = expect_tool_enabled_request_accepted(&model, &api_key).await;
            if last.is_ok() {
                break;
            }
        }
        if let Err(error) = last {
            failures.push(format!("{name} {label}: {error}"));
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

#[test]
fn covers_every_generated_anthropic_messages_model() {
    let mut expected_models: Vec<String> = get_providers()
        .into_iter()
        .flat_map(|provider| {
            get_anthropic_messages_models(provider)
                .into_iter()
                .map(move |model| format!("{provider}/{}", model.id))
        })
        .collect();
    let mut names: Vec<String> = anthropic_messages_cases()
        .into_iter()
        .map(|test_case| test_case.name)
        .collect();
    names.sort();
    expected_models.sort();
    assert_eq!(names, expected_models);
}

#[tokio::test]
#[ignore = "needs provider API keys (env, PI_TEST_GITHUB_COPILOT_TOKEN); run with --ignored"]
async fn generated_compatibility_settings_accept_configured_tool_streaming() {
    let cases = select_one_case_per_provider(anthropic_messages_cases())
        .into_iter()
        .map(|test_case| (test_case.name, test_case.model, test_case.api_key))
        .collect();
    run_probe_cases(cases, "accepts configured tool streaming").await;
}

#[tokio::test]
#[ignore = "needs provider API keys (env, PI_TEST_GITHUB_COPILOT_TOKEN); run with --ignored"]
async fn forced_eager_input_streaming_probe_accepts_forced_eager_input_streaming() {
    let eligible: Vec<E2eCase> = anthropic_messages_cases()
        .into_iter()
        .filter(|test_case| {
            serde_json::to_value(&test_case.model).expect("model json")["compat"]
                ["supportsEagerToolInputStreaming"]
                != json!(false)
        })
        .collect();
    let cases = select_one_case_per_provider(eligible)
        .into_iter()
        .map(|test_case| {
            let model = with_eager_tool_input_streaming(&test_case.model);
            (test_case.name, model, test_case.api_key)
        })
        .collect();
    run_probe_cases(cases, "accepts forced eager_input_streaming").await;
}
