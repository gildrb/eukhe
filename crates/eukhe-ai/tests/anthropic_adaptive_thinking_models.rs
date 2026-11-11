//! Port of `test/anthropic-adaptive-thinking-models.test.ts`.

use eukhe_ai::providers::all::{get_builtin_models, get_builtin_providers};
use eukhe_types::pi_ai::Model;

const EXPECTED_CURRENT_ADAPTIVE_THINKING_MODELS: [&str; 14] = [
    "anthropic/claude-fable-5",
    "anthropic/claude-haiku-5-5",
    "anthropic/claude-opus-4-8",
    "anthropic/claude-opus-5",
    "anthropic/claude-sonnet-5",
    "cloudflare-ai-gateway/claude-fable-5",
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
    get_builtin_providers()
        .into_iter()
        .flat_map(get_builtin_models)
        .collect()
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
    // The adaptive model names, `.` read as `-` (opus 4.6-4.8 and 5, sonnet
    // 4.6 and 5, haiku 5.5, fable 5, kimi-coding).
    let adaptive_names = [
        "opus-4-6",
        "opus-4-7",
        "opus-4-8",
        "opus-5",
        "sonnet-4-6",
        "sonnet-5",
        "haiku-5-5",
        "fable-5",
        "kimi-coding/",
    ];
    let allowed: Vec<String> = flagged_models
        .iter()
        .filter(|model_id| {
            let dashed = model_id.replace('.', "-");
            adaptive_names.iter().any(|name| dashed.contains(name))
        })
        .cloned()
        .collect();
    assert_eq!(flagged_models, allowed);
}
