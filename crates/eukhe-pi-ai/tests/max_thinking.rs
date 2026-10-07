//! Port of `test/max-thinking.test.ts`.
//!
//! "sends max to the Codex Responses API for %s" asserts the request payload
//! built by the `openai-codex-responses` module and is deferred to that
//! module's port.

use eukhe_pi_ai::compat::get_model;
use eukhe_pi_ai::models::{clamp_thinking_level, get_supported_thinking_levels};
use eukhe_types::pi_ai::{Model, ModelThinkingLevel};
use serde_json::json;

fn levels(model: &Model) -> Vec<&'static str> {
    get_supported_thinking_levels(model)
        .into_iter()
        .map(ModelThinkingLevel::as_str)
        .collect()
}

fn completions_model(id: &str, name: &str, thinking_level_map: Option<serde_json::Value>) -> Model {
    let mut value = json!({
        "id": id,
        "name": name,
        "api": "openai-completions",
        "provider": "test",
        "baseUrl": "https://example.com/v1",
        "reasoning": true,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 128_000,
        "maxTokens": 4096,
    });
    if let Some(map) = thinking_level_map {
        value["thinkingLevelMap"] = map;
    }
    serde_json::from_value(value).expect("model")
}

#[test]
fn is_opt_in_for_ordinary_reasoning_models() {
    let model = completions_model("ordinary-reasoning", "Ordinary Reasoning", None);

    assert_eq!(levels(&model), ["off", "minimal", "low", "medium", "high"]);
    assert_eq!(
        clamp_thinking_level(&model, ModelThinkingLevel::Max),
        ModelThinkingLevel::High
    );
}

/// TS `it.each`: one case per model id.
#[test]
fn exposes_xhigh_and_max_for_openai_codex() {
    for model_id in [
        "gpt-5.6-luna",
        "gpt-5.6-sol",
        "gpt-5.6-terra",
        "gpt-6-luna",
        "gpt-6-sol",
    ] {
        let model = get_model("openai-codex", model_id)
            .unwrap_or_else(|| panic!("openai-codex/{model_id} is defined"));
        let map = model.thinking_level_map.as_ref().expect("thinkingLevelMap");
        assert_eq!(
            map.get(&ModelThinkingLevel::Xhigh),
            Some(&Some("xhigh".to_owned())),
            "{model_id}"
        );
        assert_eq!(
            map.get(&ModelThinkingLevel::Max),
            Some(&Some("max".to_owned())),
            "{model_id}"
        );
        assert_eq!(
            levels(&model),
            ["off", "minimal", "low", "medium", "high", "xhigh", "max"],
            "{model_id}"
        );
    }
}

#[test]
fn supports_a_hole_between_high_and_max() {
    let model = completions_model(
        "high-and-max",
        "High and Max",
        Some(json!({ "xhigh": null, "max": "max" })),
    );

    assert_eq!(
        levels(&model),
        ["off", "minimal", "low", "medium", "high", "max"]
    );
    assert_eq!(
        clamp_thinking_level(&model, ModelThinkingLevel::Xhigh),
        ModelThinkingLevel::Max
    );
}
