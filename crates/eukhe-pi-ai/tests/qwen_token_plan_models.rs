//! Port of `test/qwen-token-plan-models.test.ts`. The `it.each` rows over
//! model lists run as one test looping every row (failures name the row).
//! Cases asserting on the `openai-completions` request payload
//! (`enable_thinking`, `reasoning_effort`) are deferred to that module.

mod common;

use common::assert_match_object;
use eukhe_pi_ai::compat::{find_env_keys, get_models};
use eukhe_types::pi_ai::{Model, ProviderEnv};
use serde_json::json;

const TEXT_MODELS: [&str; 16] = [
    "MiniMax-M2.5",
    "deepseek-v3.2",
    "deepseek-v4-flash",
    "deepseek-v4-pro",
    "glm-5",
    "glm-5.1",
    "glm-5.2",
    "kimi-k2.5",
    "kimi-k2.6",
    "kimi-k2.7-code",
    "qwen3.6-flash",
    "qwen3.6-plus",
    "qwen3.7-max",
    "qwen3.7-plus",
    "qwen3.8-flash",
    "qwen3.8-max",
];

const INDIVIDUAL_TEXT_MODELS: [&str; 9] = [
    "deepseek-v4-flash-0731",
    "deepseek-v4-pro",
    "deepseek-v4-pro-0813",
    "glm-5.2",
    "qwen3.6-flash",
    "qwen3.7-max",
    "qwen3.7-plus",
    "qwen3.8-flash",
    "qwen3.8-max",
];

const IMAGE_MODELS: [&str; 4] = [
    "qwen-image-2.0",
    "qwen-image-2.0-pro",
    "wan2.7-image",
    "wan2.7-image-pro",
];

const QWEN_REASONING_EFFORT_MODELS: [&str; 5] = [
    "deepseek-v4-flash",
    "deepseek-v4-pro",
    "glm-5",
    "glm-5.1",
    "glm-5.2",
];
const QWEN38_MODELS: [&str; 2] = ["qwen3.8-flash", "qwen3.8-max"];

fn qwen_reasoning_effort_model_cases() -> Vec<(&'static str, &'static str)> {
    let mut cases: Vec<(&str, &str)> = ["qwen-token-plan", "qwen-token-plan-cn"]
        .into_iter()
        .flat_map(|provider| {
            QWEN_REASONING_EFFORT_MODELS
                .into_iter()
                .map(move |model_id| (provider, model_id))
        })
        .collect();
    cases.extend(
        [
            "deepseek-v4-flash-0731",
            "deepseek-v4-pro",
            "deepseek-v4-pro-0813",
            "glm-5.2",
        ]
        .into_iter()
        .map(|model_id| ("qwen-token-plan-individual", model_id)),
    );
    cases
}

fn qwen38_model_cases() -> Vec<(&'static str, &'static str)> {
    [
        "qwen-token-plan",
        "qwen-token-plan-cn",
        "qwen-token-plan-individual",
    ]
    .into_iter()
    .flat_map(|provider| {
        QWEN38_MODELS
            .into_iter()
            .map(move |model_id| (provider, model_id))
    })
    .collect()
}

fn model_ids(provider: &str) -> Vec<String> {
    get_models(provider)
        .into_iter()
        .map(|model| model.id)
        .collect()
}

fn find(provider: &str, model_id: &str) -> Model {
    get_models(provider)
        .into_iter()
        .find(|candidate| candidate.id == model_id)
        .unwrap_or_else(|| panic!("Missing model: {provider}/{model_id}"))
}

// #9021
#[test]
fn exposes_exactly_the_documented_individual_text_models() {
    let mut ids = model_ids("qwen-token-plan-individual");
    ids.sort();
    let mut expected = INDIVIDUAL_TEXT_MODELS.map(str::to_owned).to_vec();
    expected.sort();
    assert_eq!(ids, expected);
}

#[test]
fn reuses_the_international_token_plan_environment_variable() {
    let env = ProviderEnv::from([("QWEN_TOKEN_PLAN_API_KEY".to_owned(), "test".to_owned())]);
    assert_eq!(
        find_env_keys("qwen-token-plan-individual", Some(&env)),
        Some(vec!["QWEN_TOKEN_PLAN_API_KEY".to_owned()])
    );
}

fn exposes_all_text_models_on(provider: &str) {
    let ids = model_ids(provider);
    for expected in TEXT_MODELS {
        assert!(
            ids.iter().any(|id| id == expected),
            "{provider} should include {expected}"
        );
    }
}

#[test]
fn exposes_all_text_models_on_qwen_token_plan() {
    exposes_all_text_models_on("qwen-token-plan");
}

#[test]
fn exposes_all_text_models_on_qwen_token_plan_cn() {
    exposes_all_text_models_on("qwen-token-plan-cn");
}

fn omits_image_models_from(provider: &str) {
    let ids = model_ids(provider);
    for excluded in IMAGE_MODELS {
        assert!(
            !ids.iter().any(|id| id == excluded),
            "{provider} should not include {excluded}"
        );
    }
}

#[test]
fn omits_image_models_from_qwen_token_plan() {
    omits_image_models_from("qwen-token-plan");
}

#[test]
fn omits_image_models_from_qwen_token_plan_cn() {
    omits_image_models_from("qwen-token-plan-cn");
}

#[test]
fn exposes_qwen_reasoning_effort_levels_for_each_provider_model() {
    for (provider, model_id) in qwen_reasoning_effort_model_cases() {
        let model = find(provider, model_id);
        assert_match_object(
            &model.thinking_level_map,
            &json!({
                "minimal": null,
                "low": null,
                "medium": null,
                "high": "high",
                "xhigh": null,
                "max": "max",
            }),
        );
    }
}

#[test]
fn exposes_qwen3_8_reasoning_effort_levels_for_each_provider_model() {
    for (provider, model_id) in qwen38_model_cases() {
        let model = find(provider, model_id);
        assert_match_object(
            &model.thinking_level_map,
            &json!({
                "minimal": null,
                "low": "low",
                "medium": "medium",
                "high": null,
                "xhigh": "xhigh",
                "max": null,
            }),
        );
    }
}

fn omits_retired_qwen3_8_max_preview_on(provider: &str) {
    assert!(!model_ids(provider)
        .iter()
        .any(|id| id == "qwen3.8-max-preview"));
}

#[test]
fn omits_retired_qwen3_8_max_preview_on_qwen_token_plan() {
    omits_retired_qwen3_8_max_preview_on("qwen-token-plan");
}

#[test]
fn omits_retired_qwen3_8_max_preview_on_qwen_token_plan_cn() {
    omits_retired_qwen3_8_max_preview_on("qwen-token-plan-cn");
}

#[test]
fn omits_retired_qwen3_8_max_preview_on_qwen_token_plan_individual() {
    omits_retired_qwen3_8_max_preview_on("qwen-token-plan-individual");
}
