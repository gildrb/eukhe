//! Port of `test/together-models.test.ts`.

mod common;

use std::sync::{Mutex, PoisonError};

use common::{assert_json_eq, assert_match_object};
use eukhe_pi_ai::compat::{find_env_keys, get_env_api_key, get_model};
use eukhe_types::pi_ai::Model;
use serde_json::json;

/// Serializes process-env mutation within this binary.
static ENV_LOCK: Mutex<()> = Mutex::new(());

/// Restores `TOGETHER_API_KEY` on drop (the TS `afterEach`).
struct RestoreEnv(Option<String>);

impl Drop for RestoreEnv {
    fn drop(&mut self) {
        match &self.0 {
            Some(value) => std::env::set_var("TOGETHER_API_KEY", value),
            None => std::env::remove_var("TOGETHER_API_KEY"),
        }
    }
}

fn together(id: &str) -> Model {
    get_model("together", id).expect("together model")
}

fn compat(model: &Model) -> serde_json::Value {
    serde_json::to_value(&model.compat).expect("serialize compat")
}

#[test]
fn registers_the_default_kimi_k3_model_via_openai_compatible_chat_completions_api() {
    let model = together("moonshotai/Kimi-K3");

    assert_eq!(model.api, "openai-completions");
    assert_eq!(model.provider, "together");
    assert_eq!(model.base_url, "https://api.together.ai/v1");
    assert!(model.reasoning);
    assert_json_eq(
        &model.thinking_level_map,
        &json!({ "minimal": null, "low": null, "medium": null }),
    );
    assert_json_eq(&model.input, &json!(["text", "image"]));
    assert_eq!(model.context_window, 1_048_576);
    assert_eq!(model.max_tokens, 131_072);
    assert_json_eq(
        &model.cost,
        &json!({ "input": 3, "output": 15, "cacheRead": 0.3, "cacheWrite": 0 }),
    );
    assert_json_eq(
        &model.compat,
        &json!({
            "supportsStore": false,
            "supportsDeveloperRole": false,
            "supportsReasoningEffort": false,
            "maxTokensField": "max_tokens",
            "thinkingFormat": "together",
            "supportsStrictMode": false,
            "supportsLongCacheRetention": false,
        }),
    );
}

#[test]
fn models_together_reasoning_controls_from_the_together_api_surface() {
    let gpt_oss = together("openai/gpt-oss-120b");
    assert_json_eq(
        &gpt_oss.thinking_level_map,
        &json!({
            "off": null,
            "minimal": null,
            "low": "low",
            "medium": "medium",
            "high": "high",
            "max": null,
            "xhigh": null,
        }),
    );
    assert_match_object(
        &gpt_oss.compat,
        &json!({ "supportsReasoningEffort": true, "thinkingFormat": "openai" }),
    );

    let deep_seek_v4 = together("deepseek-ai/DeepSeek-V4-Pro-0813");
    assert_json_eq(
        &deep_seek_v4.thinking_level_map,
        &json!({ "minimal": null, "low": null, "medium": null, "high": "high", "xhigh": null }),
    );
    assert_match_object(
        &deep_seek_v4.compat,
        &json!({ "supportsReasoningEffort": true, "thinkingFormat": "together" }),
    );

    let minimax = together("MiniMaxAI/MiniMax-M2.7");
    assert_json_eq(
        &minimax.thinking_level_map,
        &json!({ "off": null, "minimal": null, "low": null, "medium": null }),
    );
    let minimax_compat = compat(&minimax);
    assert_eq!(minimax_compat.get("thinkingFormat"), None);
    assert_eq!(
        minimax_compat.get("supportsReasoningEffort"),
        Some(&json!(false))
    );
}

#[test]
fn resolves_together_api_key_from_the_environment() {
    let _lock = ENV_LOCK.lock().unwrap_or_else(PoisonError::into_inner);
    let _restore = RestoreEnv(std::env::var("TOGETHER_API_KEY").ok());
    std::env::set_var("TOGETHER_API_KEY", "test-together-key");

    assert_eq!(
        find_env_keys("together", None),
        Some(vec!["TOGETHER_API_KEY".to_owned()])
    );
    assert_eq!(
        get_env_api_key("together", None).as_deref(),
        Some("test-together-key")
    );
}
