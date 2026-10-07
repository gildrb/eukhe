//! Port of `test/fireworks-models.test.ts`: the catalog, thinking-level, and
//! env cases. Request-payload assertions (`openai-completions`,
//! `anthropic-messages`) and the local-server "Anthropic-compatible session
//! affinity and tool compat" suite are deferred to those API modules.

mod common;

use std::sync::{Mutex, PoisonError};

use common::assert_json_eq;
use eukhe_pi_ai::compat::{find_env_keys, get_env_api_key, get_model};
use eukhe_pi_ai::models::get_supported_thinking_levels;
use eukhe_types::pi_ai::Model;
use serde_json::{json, Value};

/// Serializes process-env mutation within this binary.
static ENV_LOCK: Mutex<()> = Mutex::new(());

/// Restores `FIREWORKS_API_KEY` on drop (the TS `afterEach`).
struct RestoreEnv(Option<String>);

impl Drop for RestoreEnv {
    fn drop(&mut self) {
        match &self.0 {
            Some(value) => std::env::set_var("FIREWORKS_API_KEY", value),
            None => std::env::remove_var("FIREWORKS_API_KEY"),
        }
    }
}

fn fireworks(id: &str) -> Model {
    get_model("fireworks", id).expect("fireworks model")
}

/// `model.compat?.<field>`; `None` for undefined.
fn compat_field(model: &Model, field: &str) -> Option<Value> {
    serde_json::to_value(&model.compat)
        .expect("serialize compat")
        .get(field)
        .cloned()
}

fn value<T: serde::Serialize>(value: &T) -> Value {
    serde_json::to_value(value).expect("serialize")
}

#[test]
fn registers_non_glm_non_kimi_k3_models_via_anthropic_compatible_messages_api() {
    let model = fireworks("accounts/fireworks/models/deepseek-v4p1-flash");

    assert_eq!(model.api, "anthropic-messages");
    assert_eq!(model.provider, "fireworks");
    assert_eq!(model.base_url, "https://api.fireworks.ai/inference");
    assert!(model.reasoning);
    assert_json_eq(&model.input, &json!(["text", "image"]));
}

#[test]
fn aligns_glm_5_3_fast_with_glm_5_3s_openai_compatible_config() {
    let base = fireworks("accounts/fireworks/models/glm-5p3");
    let fast = fireworks("accounts/fireworks/routers/glm-5p3-fast");

    assert_eq!(fast.api, base.api);
    assert_eq!(fast.base_url, base.base_url);
    assert_eq!(value(&fast.compat), value(&base.compat));
    assert_eq!(
        value(&fast.thinking_level_map),
        value(&base.thinking_level_map)
    );
}

/// The catalog half of the TS case; its `reasoning_effort` payload assertion
/// is deferred to the `openai-completions` module.
#[test]
fn routes_kimi_k3_through_the_openai_compatible_api_with_native_effort_controls() {
    let base = fireworks("accounts/fireworks/models/kimi-k3");
    let fast = fireworks("accounts/fireworks/routers/kimi-k3-fast");
    let compat = json!({
        "supportsStore": false,
        "supportsDeveloperRole": false,
        "supportsStrictMode": true,
        "requiresReasoningContentOnAssistantMessages": true,
        "thinkingFormat": "openai",
        "supportsMidConvoSystemMessages": true,
        "supportsMidConvoToolAdditions": true,
        "sendSessionAffinityHeaders": true,
        "supportsLongCacheRetention": false,
    });
    let thinking_level_map = json!({
        "off": null,
        "minimal": null,
        "low": "low",
        "medium": null,
        "high": "high",
        "xhigh": null,
        "max": "max",
    });

    assert_eq!(base.api, "openai-completions");
    assert_eq!(base.base_url, "https://api.fireworks.ai/inference/v1");
    assert_json_eq(&base.compat, &compat);
    assert_json_eq(&base.thinking_level_map, &thinking_level_map);
    assert_eq!(fast.api, base.api);
    assert_eq!(fast.base_url, base.base_url);
    assert_json_eq(&fast.compat, &compat);
    assert_json_eq(&fast.thinking_level_map, &thinking_level_map);
}

/// Regression for #9323. The catalog half of the TS case; its `thinking` /
/// `output_config` payload assertions are deferred to the
/// `anthropic-messages` module.
fn sends_native_messages_effort_levels_for(model_id: &str, levels: &Value) {
    let model = fireworks(model_id);
    assert_eq!(model.api, "anthropic-messages");
    assert_eq!(
        compat_field(&model, "forceAdaptiveThinking"),
        Some(json!(true))
    );
    assert_json_eq(&get_supported_thinking_levels(&model), levels);
}

#[test]
fn sends_native_messages_effort_levels_for_deepseek_v4p1_flash() {
    sends_native_messages_effort_levels_for(
        "accounts/fireworks/models/deepseek-v4p1-flash",
        &json!(["off", "low", "high", "max"]),
    );
}

#[test]
fn sends_native_messages_effort_levels_for_qwen3p8_max() {
    sends_native_messages_effort_levels_for(
        "accounts/fireworks/models/qwen3p8-max",
        &json!(["off", "low", "medium", "xhigh"]),
    );
}

#[test]
fn sends_native_messages_effort_levels_for_qwen3p8_2p4t_a95b() {
    sends_native_messages_effort_levels_for(
        "accounts/fireworks/models/qwen3p8-2p4t-a95b",
        &json!(["off", "low", "medium", "xhigh"]),
    );
}

// Regression for #9323: accepted aliases are not distinct native effort levels.
fn exposes_distinct_native_effort_levels_for(model_id: &str) {
    assert_json_eq(
        &get_supported_thinking_levels(&fireworks(model_id)),
        &json!(["low", "high", "max"]),
    );
}

#[test]
fn exposes_distinct_native_effort_levels_for_glm_5p3() {
    exposes_distinct_native_effort_levels_for("accounts/fireworks/models/glm-5p3");
}

#[test]
fn exposes_distinct_native_effort_levels_for_glm_5p3_fast() {
    exposes_distinct_native_effort_levels_for("accounts/fireworks/routers/glm-5p3-fast");
}

#[test]
fn exposes_distinct_native_effort_levels_for_kimi_k3() {
    exposes_distinct_native_effort_levels_for("accounts/fireworks/models/kimi-k3");
}

#[test]
fn exposes_distinct_native_effort_levels_for_kimi_k3_fast() {
    exposes_distinct_native_effort_levels_for("accounts/fireworks/routers/kimi-k3-fast");
}

/// The catalog half of the TS case; its budget-based `thinking` payload
/// assertion is deferred to the `anthropic-messages` module.
#[test]
fn keeps_toggle_only_messages_models_without_a_verified_fallback_on_budget_based_thinking() {
    let model = fireworks("accounts/fireworks/models/nemotron-3-ultra-nvfp4");
    assert_eq!(compat_field(&model, "forceAdaptiveThinking"), None);
}

#[test]
fn resolves_fireworks_api_key_from_the_environment() {
    let _lock = ENV_LOCK.lock().unwrap_or_else(PoisonError::into_inner);
    let _restore = RestoreEnv(std::env::var("FIREWORKS_API_KEY").ok());
    std::env::set_var("FIREWORKS_API_KEY", "test-fireworks-key");

    assert_eq!(
        find_env_keys("fireworks", None),
        Some(vec!["FIREWORKS_API_KEY".to_owned()])
    );
    assert_eq!(
        get_env_api_key("fireworks", None).as_deref(),
        Some("test-fireworks-key")
    );
}

#[test]
fn sets_fireworks_specific_compat_for_session_affinity_and_unsupported_tool_fields() {
    let model = fireworks("accounts/fireworks/models/nemotron-3-ultra-nvfp4");

    assert!(model.compat.is_some());
    assert_eq!(
        compat_field(&model, "sendSessionAffinityHeaders"),
        Some(json!(true))
    );
    assert_eq!(
        compat_field(&model, "supportsEagerToolInputStreaming"),
        Some(json!(false))
    );
    assert_eq!(
        compat_field(&model, "supportsCacheControlOnTools"),
        Some(json!(false))
    );
    assert_eq!(
        compat_field(&model, "supportsLongCacheRetention"),
        Some(json!(false))
    );
    assert_eq!(
        compat_field(&model, "allowEmptySignature"),
        Some(json!(true))
    );
}
