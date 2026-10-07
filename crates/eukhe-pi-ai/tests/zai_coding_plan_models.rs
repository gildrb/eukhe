//! Port of `test/zai-coding-plan-models.test.ts`.

mod common;

use common::{assert_json_eq, assert_match_object};
use eukhe_pi_ai::providers::all::get_builtin_model;
use eukhe_types::pi_ai::Model;
use serde_json::json;

fn model(provider: &str, id: &str) -> Model {
    get_builtin_model(provider, id).expect("builtin model")
}

#[test]
fn exposes_glm_4_6v_on_the_china_coding_plan_catalog() {
    assert_match_object(
        &get_builtin_model("zai-coding-cn", "glm-4.6v"),
        &json!({
            "id": "glm-4.6v",
            "provider": "zai-coding-cn",
            "api": "openai-completions",
            "baseUrl": "https://open.bigmodel.cn/api/coding/paas/v4",
            "reasoning": true,
            "input": ["text", "image"],
            "cost": { "input": 0.3, "output": 0.9, "cacheRead": 0, "cacheWrite": 0 },
            "contextWindow": 128_000,
            "maxTokens": 32768,
            "compat": {
                "maxTokensField": "max_tokens",
                "thinkingFormat": "zai",
                "zaiToolStream": true,
            },
        }),
    );
}

#[test]
fn uses_api_equivalent_reference_costs_for_coding_plan_models() {
    let reference = json!({ "input": 1.4, "output": 4.4, "cacheRead": 0.26, "cacheWrite": 0 });
    assert_json_eq(&model("zai", "glm-5.2").cost, &reference);
    for provider in ["zai", "zai-coding-cn"] {
        assert_json_eq(&model(provider, "glm-5.3").cost, &reference);
    }
}

#[test]
fn keeps_zero_costs_for_coding_plan_models_without_a_matching_api_price() {
    let zero_cost = json!({ "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 });

    assert_json_eq(&model("zai", "glm-5.2-highspeed").cost, &zero_cost);

    for provider in ["zai", "zai-coding-cn"] {
        assert_json_eq(&model(provider, "glm-5.3-highspeed").cost, &zero_cost);
    }
}
