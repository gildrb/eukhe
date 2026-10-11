//! Port of `openrouter-cache-control-models.test.ts`.

use crate::providers::all::get_builtin_model;

fn keeps_completions_cache_control_for(model_id: &str) {
    let model = get_builtin_model("openrouter", model_id)
        .unwrap_or_else(|| panic!("missing catalog model {model_id}"));
    let value = serde_json::to_value(&model).expect("serialize model");
    assert_eq!(value["api"], "openai-completions", "{model_id}");
    assert_eq!(
        value["compat"]["cacheControlFormat"], "anthropic",
        "{model_id}"
    );
}

#[test]
fn keeps_completions_cache_control_for_claude_fable_latest() {
    keeps_completions_cache_control_for("~anthropic/claude-fable-latest");
}

#[test]
fn keeps_completions_cache_control_for_claude_haiku_latest() {
    keeps_completions_cache_control_for("~anthropic/claude-haiku-latest");
}

#[test]
fn keeps_completions_cache_control_for_claude_opus_latest() {
    keeps_completions_cache_control_for("~anthropic/claude-opus-latest");
}

#[test]
fn keeps_completions_cache_control_for_claude_sonnet_latest() {
    keeps_completions_cache_control_for("~anthropic/claude-sonnet-latest");
}
