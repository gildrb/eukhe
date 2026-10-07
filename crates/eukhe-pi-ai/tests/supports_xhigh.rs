//! Port of `test/supports-xhigh.test.ts`.

use eukhe_pi_ai::compat::get_model;
use eukhe_pi_ai::models::get_supported_thinking_levels;
use eukhe_types::pi_ai::{Model, ModelThinkingLevel};
use serde_json::{json, Value};

fn model(provider: &str, id: &str) -> Model {
    get_model(provider, id).unwrap_or_else(|| panic!("{provider}/{id} is defined"))
}

fn levels(model: &Model) -> Vec<&'static str> {
    get_supported_thinking_levels(model)
        .into_iter()
        .map(ModelThinkingLevel::as_str)
        .collect()
}

/// TS `toMatchObject`: objects match as subsets, arrays element-wise with
/// equal length, numbers by value.
fn assert_matches_object(actual: &Value, expected: &Value, path: &str) {
    match (actual, expected) {
        (Value::Object(actual), Value::Object(expected)) => {
            for (key, expected) in expected {
                let actual = actual
                    .get(key)
                    .unwrap_or_else(|| panic!("{path}.{key} is missing"));
                assert_matches_object(actual, expected, &format!("{path}.{key}"));
            }
        }
        (Value::Array(actual), Value::Array(expected)) => {
            assert_eq!(actual.len(), expected.len(), "{path} length");
            for (index, (actual, expected)) in actual.iter().zip(expected).enumerate() {
                assert_matches_object(actual, expected, &format!("{path}[{index}]"));
            }
        }
        (Value::Number(actual), Value::Number(expected)) => {
            assert_eq!(actual.as_f64(), expected.as_f64(), "{path}");
        }
        (actual, expected) => assert_eq!(actual, expected, "{path}"),
    }
}

fn assert_model_matches(model: &Model, expected: &Value) {
    let actual = serde_json::to_value(model).expect("model json");
    assert_matches_object(
        &actual,
        expected,
        &format!("{}/{}", model.provider, model.id),
    );
}

#[test]
fn includes_max_but_not_xhigh_for_anthropic_opus_4_6_on_anthropic_messages_api() {
    let levels = levels(&model("anthropic", "claude-opus-4-6"));
    assert!(levels.contains(&"max"));
    assert!(!levels.contains(&"xhigh"));
}

#[test]
fn includes_xhigh_and_max_for_anthropic_opus_4_8_on_anthropic_messages_api() {
    let levels = levels(&model("anthropic", "claude-opus-4-8"));
    assert!(levels.contains(&"xhigh"));
    assert!(levels.contains(&"max"));
}

#[test]
fn includes_xhigh_and_max_for_anthropic_opus_5_on_anthropic_messages_api() {
    let levels = levels(&model("anthropic", "claude-opus-5"));
    assert!(levels.contains(&"xhigh"));
    assert!(levels.contains(&"max"));
}

#[test]
fn includes_claude_opus_5_5_with_its_always_on_effort_levels_and_official_pricing() {
    let model = model("anthropic", "claude-opus-5-5");
    assert_model_matches(
        &model,
        &json!({
            "cost": { "input": 4, "output": 20, "cacheRead": 0.2, "cacheWrite": 5 },
            "contextWindow": 1_000_000,
            "maxTokens": 128_000,
            "compat": {
                "forceAdaptiveThinking": true,
                "supportsMidConvoEffort": true,
                "supportsMidConvoSystemMessages": true,
                "supportsMidConvoToolChanges": true,
            },
        }),
    );
    assert_eq!(levels(&model), ["low", "medium", "high", "xhigh", "max"]);
}

#[test]
fn includes_claude_sonnet_5_5_with_managed_effort_levels_and_official_pricing() {
    let model = model("anthropic", "claude-sonnet-5-5");
    assert_model_matches(
        &model,
        &json!({
            "cost": { "input": 2, "output": 10, "cacheRead": 0.2, "cacheWrite": 2.5 },
            "contextWindow": 1_000_000,
            "maxTokens": 128_000,
            "compat": {
                "forceAdaptiveThinking": true,
                "supportsMidConvoEffort": true,
                "supportsMidConvoSystemMessages": true,
                "supportsMidConvoToolChanges": true,
                "supportsTemperature": false,
            },
        }),
    );
    assert_eq!(levels(&model), ["low", "medium", "high", "xhigh", "max"]);
}

#[test]
fn includes_max_but_not_xhigh_for_anthropic_sonnet_4_6_on_anthropic_messages_api() {
    let levels = levels(&model("anthropic", "claude-sonnet-4-6"));
    assert!(levels.contains(&"max"));
    assert!(!levels.contains(&"xhigh"));
}

#[test]
fn includes_xhigh_and_max_for_anthropic_sonnet_5_on_anthropic_messages_api() {
    let levels = levels(&model("anthropic", "claude-sonnet-5"));
    assert!(levels.contains(&"xhigh"));
    assert!(levels.contains(&"max"));
}

#[test]
fn includes_xhigh_and_max_but_not_off_for_anthropic_claude_fable_5_on_anthropic_messages_api() {
    let levels = levels(&model("anthropic", "claude-fable-5"));
    assert!(levels.contains(&"xhigh"));
    assert!(levels.contains(&"max"));
    assert!(!levels.contains(&"off"));
}

#[test]
fn does_not_include_xhigh_or_max_for_claude_sonnet_4_5() {
    let levels = levels(&model("anthropic", "claude-sonnet-4-5"));
    assert!(!levels.contains(&"xhigh"));
    assert!(!levels.contains(&"max"));
}

/// TS `it.each`: one case per model id.
#[test]
fn includes_xhigh_for_openai_codex_models() {
    for model_id in [
        "gpt-5.5",
        "gpt-5.6-sol",
        "gpt-5.6-terra",
        "gpt-5.6-luna",
        "gpt-6-astra",
        "gpt-6-sol",
        "gpt-6-luna",
        "gpt-6.1-sol",
    ] {
        assert!(
            levels(&model("openai-codex", model_id)).contains(&"xhigh"),
            "{model_id}"
        );
    }
}

/// TS `it.each`: one case per model id.
#[test]
fn includes_xhigh_and_max_for_openai_models() {
    for model_id in [
        "gpt-5.6-sol",
        "gpt-5.6-terra",
        "gpt-5.6-luna",
        "gpt-6-sol",
        "gpt-6-luna",
    ] {
        assert_eq!(
            levels(&model("openai", model_id)),
            ["off", "low", "medium", "high", "xhigh", "max"],
            "{model_id}"
        );
    }
}

/// `OpenAI` and Codex reject reasoning.effort "none" for GPT-6.1 Sol.
#[test]
fn does_not_support_off_for_gpt_6_1_sol() {
    let expected: [(&str, &[&str]); 3] = [
        ("openai", &["low", "medium", "high", "xhigh", "max"]),
        ("azure", &["low", "medium", "high", "xhigh", "max"]),
        (
            "openai-codex",
            &["minimal", "low", "medium", "high", "xhigh", "max"],
        ),
    ];
    for (provider, expected_levels) in expected {
        let model = model(provider, "gpt-6.1-sol");
        assert_eq!(levels(&model), expected_levels, "{provider}");
        assert_eq!(
            model
                .thinking_level_map
                .as_ref()
                .and_then(|map| map.get(&ModelThinkingLevel::Off)),
            Some(&None),
            "{provider}"
        );
    }
}

/// TS `it.each`: one case per model id.
#[test]
fn includes_official_metadata_for_openai_and_codex() {
    let cases: [(&str, [f64; 4]); 3] = [
        ("gpt-6-sol", [2.0, 10.0, 0.2, 2.5]),
        ("gpt-6-luna", [0.1, 0.5, 0.01, 0.125]),
        ("gpt-6.1-sol", [2.0, 10.0, 0.1, 2.5]),
    ];
    for (model_id, [input, output, cache_read, cache_write]) in cases {
        for provider in ["openai", "openai-codex"] {
            assert_model_matches(
                &model(provider, model_id),
                &json!({
                    "input": ["text", "image"],
                    "cost": {
                        "input": input,
                        "output": output,
                        "cacheRead": cache_read,
                        "cacheWrite": cache_write,
                        "tiers": [
                            {
                                "inputTokensAbove": 272_000,
                                "input": input * 2.0,
                                "output": output * 1.5,
                                "cacheRead": cache_read * 2.0,
                                "cacheWrite": cache_write * 2.0,
                            },
                        ],
                    },
                    "contextWindow": 272_000,
                    "maxTokens": 128_000,
                    "compat": {
                        "supportsAdditionalTools": true,
                        "supportsMidConvoSystemMessages": true,
                        "supportsOpenAIGrammarTools": true,
                        "supportsToolSearch": true,
                    },
                }),
            );
        }
    }
}

#[test]
fn includes_only_medium_high_xhigh_for_openai_gpt_5_5_pro() {
    assert_eq!(
        levels(&model("openai", "gpt-5.5-pro")),
        ["medium", "high", "xhigh"]
    );
}

#[test]
fn includes_only_medium_high_xhigh_for_openrouter_gpt_5_5_pro() {
    assert_eq!(
        levels(&model("openrouter", "openai/gpt-5.5-pro")),
        ["medium", "high", "xhigh"]
    );
}

#[test]
fn includes_low_high_max_plus_off_for_deepseek_v4_1_flash_on_the_deepseek_provider() {
    assert_eq!(
        levels(&model("deepseek", "deepseek-flash")),
        ["off", "low", "high", "max"]
    );
}

#[test]
fn includes_low_high_max_plus_off_for_deepseek_v4_flash_on_opencode_go() {
    assert_eq!(
        levels(&model("opencode-go", "deepseek-v4-flash")),
        ["off", "low", "high", "max"]
    );
}

#[test]
fn preserves_low_high_max_metadata_for_deepseek_v4_1_flash_on_openrouter() {
    assert_eq!(
        levels(&model("openrouter", "deepseek/deepseek-v4.1-flash")),
        ["off", "low", "high", "max"]
    );
}

#[test]
fn preserves_low_high_max_metadata_for_deepseek_v4_1_flash_on_opencode_go() {
    assert_eq!(
        levels(&model("opencode-go", "deepseek-v4.1-flash")),
        ["low", "high", "max"]
    );
}

#[test]
fn excludes_thinking_off_for_moonshot_kimi_k2_7_code_models() {
    for provider in ["moonshotai", "moonshotai-cn"] {
        assert_eq!(
            levels(&model(provider, "kimi-k2.7-code")),
            ["minimal", "low", "medium", "high"],
            "{provider}"
        );
    }
}

/// TS `it.each`: one case per provider.
#[test]
fn uses_the_verified_effort_options_for_kimi_k3() {
    for provider in ["moonshotai", "moonshotai-cn"] {
        assert_eq!(
            levels(&model(provider, "kimi-k3")),
            ["low", "high", "max"],
            "{provider}"
        );
    }
}

#[test]
fn includes_only_low_high_max_for_kimi_coding_k3() {
    assert_eq!(levels(&model("kimi-coding", "k3")), ["low", "high", "max"]);
}

#[test]
fn includes_only_high_for_opencode_grok_build() {
    assert_eq!(levels(&model("opencode", "grok-build-0.1")), ["high"]);
}

#[test]
fn includes_only_high_xhigh_plus_off_for_deepseek_v4_flash_on_openrouter() {
    assert_eq!(
        levels(&model("openrouter", "deepseek/deepseek-v4-flash")),
        ["off", "high", "xhigh"]
    );
}

#[test]
fn includes_max_but_not_xhigh_for_openrouter_opus_4_6_openai_completions_api() {
    let levels = levels(&model("openrouter", "anthropic/claude-opus-4.6"));
    assert!(levels.contains(&"max"));
    assert!(!levels.contains(&"xhigh"));
}

#[test]
fn includes_xhigh_and_max_for_bedrock_claude_opus_5() {
    let levels = levels(&model("amazon-bedrock", "global.anthropic.claude-opus-5"));
    assert!(levels.contains(&"xhigh"));
    assert!(levels.contains(&"max"));
}

#[test]
fn includes_xhigh_but_not_off_or_max_for_xai_grok_4_6() {
    assert_eq!(
        levels(&model("xai", "grok-4.6")),
        ["low", "medium", "high", "xhigh"]
    );
}

#[test]
fn includes_xhigh_and_max_but_not_off_for_bedrock_claude_fable_5() {
    let levels = levels(&model("amazon-bedrock", "global.anthropic.claude-fable-5"));
    assert!(levels.contains(&"xhigh"));
    assert!(levels.contains(&"max"));
    assert!(!levels.contains(&"off"));
}
