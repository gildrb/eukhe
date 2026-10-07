//! Port of `test/baseten-models.test.ts`. Assertions on the request payload
//! built by the `openai-completions` module are deferred to that module.

mod common;

use std::sync::{Mutex, PoisonError};

use common::{assert_json_eq, assert_match_object};
use eukhe_pi_ai::compat::{find_env_keys, get_env_api_key, get_model};
use eukhe_pi_ai::models::get_supported_thinking_levels;
use eukhe_types::pi_ai::{Model, ModelThinkingLevel};
use serde_json::json;

/// Serializes process-env mutation within this binary.
static ENV_LOCK: Mutex<()> = Mutex::new(());

/// Restores `BASETEN_API_KEY` on drop (the TS `afterEach`).
struct RestoreEnv(Option<String>);

impl Drop for RestoreEnv {
    fn drop(&mut self) {
        match &self.0 {
            Some(value) => std::env::set_var("BASETEN_API_KEY", value),
            None => std::env::remove_var("BASETEN_API_KEY"),
        }
    }
}

fn baseten(id: &str) -> Model {
    get_model("baseten", id).expect("baseten model")
}

#[test]
fn keeps_both_glm_5_2_endpoints_text_only() {
    assert_json_eq(&baseten("zai-org/GLM-5.2").input, &json!(["text"]));
    assert_json_eq(&baseten("zai-org/GLM-5.2-Fast").input, &json!(["text"]));
}

/// The catalog half of the TS case; its `chat_template_args` payload
/// assertions are deferred to the `openai-completions` module.
#[test]
fn models_kimi_k2_6_reasoning_as_an_explicit_off_on_toggle() {
    let model = baseten("moonshotai/Kimi-K2.6");

    assert_json_eq(
        &model.thinking_level_map,
        &json!({
            "off": "off",
            "minimal": null,
            "low": null,
            "medium": null,
            "high": "high",
            "xhigh": null,
            "max": null,
        }),
    );
    assert_match_object(
        &model.compat,
        &json!({
            "supportsReasoningEffort": false,
            "thinkingFormat": "baseten",
            "chatTemplateArgs": { "enable_thinking": { "$var": "thinking.enabled" } },
        }),
    );
    assert_eq!(
        get_supported_thinking_levels(&model),
        [ModelThinkingLevel::Off, ModelThinkingLevel::High]
    );
}

#[test]
fn resolves_baseten_api_key_from_the_environment() {
    let _lock = ENV_LOCK.lock().unwrap_or_else(PoisonError::into_inner);
    let _restore = RestoreEnv(std::env::var("BASETEN_API_KEY").ok());
    std::env::set_var("BASETEN_API_KEY", "test-baseten-key");

    assert_eq!(
        find_env_keys("baseten", None),
        Some(vec!["BASETEN_API_KEY".to_owned()])
    );
    assert_eq!(
        get_env_api_key("baseten", None).as_deref(),
        Some("test-baseten-key")
    );
}
