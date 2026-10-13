//! The model-registry unit battery: the in-memory catalog, the auth
//! filters, the models.json merges, and the provider headers.
use super::*;
use crate::auth::manager::{AuthStorage, NoOAuth};
use crate::auth::types::AuthStorageData;
use std::sync::Arc;

fn auth_with(data: &serde_json::Value) -> AuthStorage {
    let data = AuthStorageData(data.as_object().cloned().unwrap_or_default());
    AuthStorage::in_memory(&data, Arc::new(NoOAuth))
}

/// Like [`auth_with`] but with ambient `PRIME_API_KEY`/`PRIME_TEAM_ID`
/// ignored: the stored credential is the only source, so credential
/// tests are hermetic on boxes that carry Prime Inference env vars.
fn auth_without_env(data: &serde_json::Value) -> AuthStorage {
    let data = AuthStorageData(data.as_object().cloned().unwrap_or_default());
    AuthStorage::in_memory_without_env(&data, Arc::new(NoOAuth))
}

fn model(id: &str, provider: &str) -> Model {
    serde_json::from_value(serde_json::json!({
        "id": id, "name": id, "api": "openai-completions", "provider": provider,
        "baseUrl": "https://example.com", "reasoning": false, "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 1000, "maxTokens": 100
    }))
    .unwrap()
}

#[test]
fn in_memory_loads_built_in_catalog() {
    let registry = ModelRegistry::in_memory(auth_with(&serde_json::json!({})));
    assert!(registry.get_error().is_none());
    assert!(!registry.get_all().is_empty());
    // Bundled private model is present in the unfiltered catalog.
    assert!(registry
        .get_all()
        .iter()
        .any(|m| m.id == "internal/glm-5.2-fast"));
}

/// TS `755-configured-max-tokens.test.ts`: built-in catalog models stay
/// unmarked when no override configures `maxTokens` — the default 32000
/// ceiling keeps applying to them (901 of the catalog's models declare
/// more than 32000 and their request size must not change).
#[test]
fn built_in_catalog_models_stay_unmarked() {
    let registry = ModelRegistry::in_memory(auth_with(&serde_json::json!({})));
    assert!(!registry.get_all().is_empty());
    assert!(registry
        .get_all()
        .iter()
        .all(|model| !model.max_tokens_explicit));
}

#[test]
fn available_filters_by_configured_auth() {
    let auth = auth_with(&serde_json::json!({
        "anthropic": { "type": "api_key", "key": "sk-ant" }
    }));
    let registry = ModelRegistry::in_memory(auth);
    // Stored credential authorizes the provider.
    assert!(registry.has_configured_auth(&model("m", "anthropic")));
    // An unconfigured provider (no stored cred, no env var, no models.json
    // key) is auth-gated out. The name is deliberately obscure so ambient
    // environment variables cannot authorize it.
    assert!(!registry.has_configured_auth(&model("m", "zz-no-provider")));
    // Available is a subset of all.
    let all = registry.get_all();
    let available = registry.get_available();
    assert!(available.iter().all(|available_model| {
        all.iter().any(|model| {
            model.id == available_model.id && model.provider == available_model.provider
        })
    }));
}

#[test]
fn rlm_searchable_models_gate_one_stale_provider_across_its_models() {
    // The per-provider status memo must answer every model of a
    // provider with the same probe result: a stale provider's whole
    // model list stays gated while a second authed provider keeps its
    // models searchable.
    let mut auth = auth_without_env(&serde_json::json!({
        "anthropic": { "type": "api_key", "key": "sk-ant" },
        "openai": { "type": "api_key", "key": "sk-oai" }
    }));
    assert!(auth.mark_auth_stale("anthropic"));
    let registry = ModelRegistry::in_memory(auth);
    let searchable = registry.get_rlm_searchable_models();
    assert!(searchable.iter().all(|model| model.provider != "anthropic"));
    assert!(searchable.iter().any(|model| model.provider == "openai"));
    // `has_auth` is stale-aware (a marked credential is not
    // "configured"), so the available set gates the stale provider's
    // models too - the same semantics at the tip and with the memo.
    let available = registry.get_available();
    assert!(!available.iter().any(|model| model.provider == "anthropic"));
    assert!(available.iter().any(|model| model.provider == "openai"));
    assert!(available
        .iter()
        .all(|model| model.provider != "zz-no-provider"));
}

#[test]
fn models_json_custom_models_and_auth_header() {
    let dir = tempfile::tempdir().unwrap();
    let models_path = dir.path().join("models.json");
    std::fs::write(
        &models_path,
        r#"{ "providers": { "custom": {
            "baseUrl": "https://custom.example", "apiKey": "custom-key",
            "api": "openai-completions", "authHeader": true,
            "models": [ { "id": "my-model" } ]
        } } }"#,
    )
    .unwrap();
    let auth = auth_with(&serde_json::json!({}));
    let mut registry = ModelRegistry::create(auth, &models_path);
    assert!(registry.get_error().is_none());
    let custom = registry
        .get_all()
        .iter()
        .find(|m| m.provider == "custom" && m.id == "my-model")
        .expect("custom model merged")
        .clone();
    assert_eq!(custom.base_url, "https://custom.example");
    // models.json apiKey makes the provider available.
    assert!(registry.get_available().iter().any(|m| m.id == "my-model"));
    let auth_result = registry.get_api_key_and_headers(&custom, None);
    assert!(auth_result.ok);
    assert_eq!(auth_result.api_key.as_deref(), Some("custom-key"));
    assert_eq!(
        auth_result.headers.as_ref().unwrap().get("Authorization"),
        Some(&"Bearer custom-key".to_string())
    );
}

#[test]
fn models_json_error_keeps_built_ins() {
    let dir = tempfile::tempdir().unwrap();
    let models_path = dir.path().join("models.json");
    std::fs::write(&models_path, "{ not json").unwrap();
    let registry = ModelRegistry::create(auth_with(&serde_json::json!({})), &models_path);
    assert!(registry.get_error().is_some());
    assert!(!registry.get_all().is_empty());
}

#[test]
fn header_precedence_model_over_provider() {
    let mut registry = ModelRegistry::in_memory(auth_with(&serde_json::json!({
        "anthropic": { "type": "api_key", "key": "sk-ant" }
    })));
    let mut m = model("m", "anthropic");
    m.headers = Some(BTreeMap::from([(
        "X-Model".to_string(),
        "model".to_string(),
    )]));
    let result = registry.get_api_key_and_headers(&m, None);
    assert_eq!(result.api_key.as_deref(), Some("sk-ant"));
    assert_eq!(
        result.headers.as_ref().unwrap().get("X-Model").unwrap(),
        "model"
    );
    // Request headers win over everything.
    let request = BTreeMap::from([("X-Model".to_string(), "request".to_string())]);
    let result = registry.get_api_key_and_headers(&m, Some(&request));
    assert_eq!(
        result.headers.as_ref().unwrap().get("X-Model").unwrap(),
        "request"
    );
}

#[test]
fn undeclared_private_ids_are_not_authorized() {
    let registry = ModelRegistry::in_memory(auth_with(&serde_json::json!({})));
    let private_model = model("internal/custom-private", "prime-inference");
    assert!(!registry.is_authorized_private_model(&private_model));
}

#[test]
fn a_stored_copilot_credential_rewrites_its_models_base_url() {
    // TS `githubCopilotOAuthProvider.modifyModels`: the token's
    // proxy endpoint wins.
    let auth = auth_without_env(&serde_json::json!({
        "github-copilot": {
            "type": "oauth",
            "access": "tid=1;exp=2;proxy-ep=proxy.enterprise.githubcopilot.com",
            "refresh": "gh", "expires": 4_102_444_800_000i64
        }
    }));
    let registry = ModelRegistry::in_memory(auth);
    let grok = registry
        .get_all()
        .iter()
        .find(|model| model.provider == "github-copilot")
        .expect("the copilot models render");
    assert_eq!(grok.base_url, "https://api.enterprise.githubcopilot.com");
    // An enterprise credential without a proxy endpoint routes onto
    // the enterprise API.
    let auth = auth_without_env(&serde_json::json!({
        "github-copilot": {
            "type": "oauth",
            "access": "plain-token", "refresh": "gh", "expires": 4_102_444_800_000i64,
            "enterpriseUrl": "company.ghe.com"
        }
    }));
    let registry = ModelRegistry::in_memory(auth);
    let grok = registry
        .get_all()
        .iter()
        .find(|model| model.provider == "github-copilot")
        .expect("the copilot models render");
    assert_eq!(grok.base_url, "https://copilot-api.company.ghe.com");
}

/// The registry over a `models.json` that defines the catalog's
/// non-reasoning completions-API xai model (the compiled pi-ai xai models
/// already ride the responses API, so the subscription switch is pinned on
/// a completions entry the catalog ships).
fn registry_with_completions_grok(auth: AuthStorage, dir: &tempfile::TempDir) -> ModelRegistry {
    let models_path = dir.path().join("models.json");
    std::fs::write(
        &models_path,
        r#"{ "providers": { "xai": {
            "baseUrl": "https://api.x.ai/v1", "api": "openai-completions",
            "models": [ {
                "id": "grok-4.20-0309-non-reasoning", "name": "Grok 4.20 (Non-Reasoning)",
                "reasoning": false, "input": ["text", "image"],
                "contextWindow": 2000000, "maxTokens": 30000
            } ]
        } } }"#,
    )
    .unwrap();
    let registry = ModelRegistry::create(auth, &models_path);
    assert!(registry.get_error().is_none(), "{:?}", registry.get_error());
    registry
}

fn completions_grok(registry: &ModelRegistry) -> &Model {
    registry
        .get_all()
        .iter()
        .find(|model| model.provider == "xai" && model.id == "grok-4.20-0309-non-reasoning")
        .expect("the xai model renders")
}

#[test]
fn a_stored_xai_subscription_switches_its_models_onto_responses() {
    let auth = auth_without_env(&serde_json::json!({
        "xai": {
            "type": "oauth",
            "access": "grok",
            "refresh": "r",
            "expires": 4_102_444_800_000i64,
        }
    }));
    let dir = tempfile::tempdir().unwrap();
    let registry = registry_with_completions_grok(auth, &dir);
    let grok = completions_grok(&registry);
    assert_eq!(grok.api, "openai-responses");
    assert_eq!(grok.base_url, "https://api.x.ai/v1");
    // The catalog's xai model is non-reasoning: "off" is the only
    // supported level whatever the subscription map nulls (the
    // helper answers the non-reasoning branch first).
    let supported = eukhe_types::ai::thinking_levels::get_supported_thinking_levels(grok);
    assert_eq!(supported, vec![ModelThinkingLevel::Off]);
    // The compat is the shared-key-only object (TS
    // `supportsLongCacheRetention: false`); the responses provider
    // decodes it directly (its own test covers the decode).
    let compat = grok.compat.as_ref().expect("the compat rides the model");
    assert_eq!(
        compat.raw.get("supportsLongCacheRetention"),
        Some(&serde_json::json!(false))
    );
}

/// TS `getXaiSubscriptionModel` fills only an absent `thinkingLevelMap`:
/// a model keeps the levels its catalog row declares under the
/// subscription, and a model without a map gets every level unsupported.
#[test]
fn a_subscription_model_keeps_its_own_thinking_level_map() {
    let mut grok = model("grok-build-0.1", "xai");
    grok.reasoning = true;
    grok.thinking_level_map =
        Some(std::iter::once((ModelThinkingLevel::Off, Some("none".to_string()))).collect());
    let adapted = xai_subscription_model(&grok);
    assert_eq!(adapted.thinking_level_map, grok.thinking_level_map);

    let bare = model("grok-4.5", "xai");
    assert!(bare.thinking_level_map.is_none());
    let adapted = xai_subscription_model(&bare);
    let map = adapted.thinking_level_map.expect("a map is filled in");
    assert_eq!(map.len(), 7);
    assert!(map.values().all(Option::is_none));
}

#[test]
fn without_a_stored_xai_subscription_the_models_stay_on_completions() {
    let dir = tempfile::tempdir().unwrap();
    let registry = registry_with_completions_grok(auth_without_env(&serde_json::json!({})), &dir);
    let grok = completions_grok(&registry);
    assert_eq!(grok.api, "openai-completions");
    assert!(grok.thinking_level_map.is_none());
    assert!(grok.compat.is_none());
}
