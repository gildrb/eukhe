//! Port of `test/model-catalog-types.test.ts`. The TS `expectTypeOf`
//! literal-type checks become runtime checks of the same values: Rust
//! catalogs are maps of owned strings, not literal types.

mod common;

use common::assert_match_object;
use eukhe_pi_ai::providers::github_copilot_models::GITHUB_COPILOT_MODELS;
use eukhe_pi_ai::providers::xai_models::XAI_MODELS;
use eukhe_types::pi_ai::Model;

fn xai(id: &str) -> &'static Model {
    XAI_MODELS.get(id).expect("xai model")
}

fn copilot(id: &str) -> &'static Model {
    GITHUB_COPILOT_MODELS.get(id).expect("copilot model")
}

#[test]
fn derives_model_api_id_and_provider_literals_from_grouped_model_data() {
    assert_eq!(xai("grok-4.5").api, "openai-responses");
    assert_eq!(xai("grok-4.5").id, "grok-4.5");
    assert_eq!(xai("grok-4.5").provider, "xai");
    assert_eq!(xai("grok-4.6").api, "openai-responses");
    assert_eq!(xai("grok-4.6").id, "grok-4.6");
    assert_eq!(xai("grok-4.7").api, "openai-responses");
    assert_eq!(xai("grok-4.7").id, "grok-4.7");
    assert_eq!(xai("grok-4.3").api, "openai-responses");
}

#[test]
fn routes_github_copilot_grok_4_5_through_the_responses_api() {
    assert_eq!(copilot("grok-4.5").api, "openai-responses");
}

// Regression test for https://github.com/earendil-works/pi/issues/9209
#[test]
fn routes_all_github_copilot_gpt_models_through_the_responses_api() {
    let gpt_models: Vec<&Model> = GITHUB_COPILOT_MODELS
        .values()
        .filter(|model| model.id.starts_with("gpt-"))
        .collect();
    assert!(!gpt_models.is_empty());
    assert!(gpt_models
        .iter()
        .all(|model| model.api == "openai-responses"));
    assert_eq!(copilot("gpt-6-astra").api, "openai-responses");
    for model_id in ["gpt-6-sol", "gpt-6-luna"] {
        let model = copilot(model_id);
        assert_eq!(model.api, "openai-responses");
        assert_match_object(
            model,
            &serde_json::json!({
                "api": "openai-responses",
                "contextWindow": 1_000_000,
                "maxTokens": 128_000,
                "thinkingLevelMap": { "off": "none", "max": "max" },
            }),
        );
    }
}
