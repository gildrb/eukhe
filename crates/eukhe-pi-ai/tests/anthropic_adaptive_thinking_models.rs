//! Port of `test/anthropic-adaptive-thinking-models.test.ts`.

use eukhe_pi_ai::compat::{get_models, get_providers};
use eukhe_types::pi_ai::Model;

const EXPECTED_CURRENT_ADAPTIVE_THINKING_MODELS: [&str; 16] = [
    "anthropic/claude-fable-5",
    "anthropic/claude-opus-4-8",
    "anthropic/claude-opus-5",
    "anthropic/claude-sonnet-5",
    "cloudflare-ai-gateway/claude-fable-5",
    "fireworks/accounts/fireworks/models/deepseek-v4p1-flash",
    "fireworks/accounts/fireworks/models/gpt-oss-120b",
    "fireworks/accounts/fireworks/models/qwen3p8-max",
    "kimi-coding/kimi-for-coding",
    "kimi-coding/k3",
    "kimi-coding/kimi-for-coding-highspeed",
    "opencode/claude-opus-4-8",
    "opencode/claude-opus-5",
    "vercel-ai-gateway/anthropic/claude-opus-4.8",
    "vercel-ai-gateway/anthropic/claude-opus-5",
    "vercel-ai-gateway/anthropic/claude-sonnet-5",
];

fn get_all_models() -> Vec<Model> {
    get_providers().into_iter().flat_map(get_models).collect()
}

/// `model.compat?.forceAdaptiveThinking === true`.
fn force_adaptive_thinking(model: &Model) -> bool {
    let value = serde_json::to_value(model).expect("model json");
    value["compat"]["forceAdaptiveThinking"] == serde_json::Value::Bool(true)
}

#[test]
fn marks_built_in_anthropic_messages_models_that_use_adaptive_thinking() {
    let mut flagged_models: Vec<String> = get_all_models()
        .iter()
        .filter(|model| model.api == "anthropic-messages")
        .filter(|model| force_adaptive_thinking(model))
        .map(|model| format!("{}/{}", model.provider, model.id))
        .collect();
    flagged_models.sort();

    for expected in EXPECTED_CURRENT_ADAPTIVE_THINKING_MODELS {
        assert!(
            flagged_models.iter().any(|model| model == expected),
            "missing {expected} in {flagged_models:?}"
        );
    }
    let pattern = regex::Regex::new(
        r"(opus[-.](4[-.][678]|5)|sonnet[-.]4[-.]6|sonnet[-.]5|fable[-.]5|kimi-coding/)",
    )
    .expect("regex");
    let allowed: Vec<String> = flagged_models
        .iter()
        // Regression for #9323: Fireworks uses catalog effort metadata and
        // verified fallbacks, not a fixed set of adaptive model names.
        .filter(|model_id| model_id.starts_with("fireworks/") || pattern.is_match(model_id))
        .cloned()
        .collect();
    assert_eq!(flagged_models, allowed);
}
