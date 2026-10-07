//! The pi-ai model collection of a durable eukhe session and the model of a
//! new root conversation.
//!
//! [`create_models`] registers every built-in pi-ai provider (the eukhe
//! `prime-inference` provider included), composes the user's
//! `<agent_dir>/models.json` over them (`compose`), and wires two
//! persistent stores (`stores`):
//!
//! - credentials: a pi-ai `CredentialStore` over eukhe's
//!   `<agent_dir>/auth.json`, through eukhe's own `FileAuthStorageBackend`
//!   (same file, same lock directory, same atomic 0600 writes, same
//!   process-local serialization), so the old engine and this one share one
//!   document;
//! - dynamic catalogs: a `ModelsStore` at `<agent_dir>/models-store.json`
//!   (the pi coding-agent `FileModelsStore`, also over the auth backend).
//!
//! Catalog refresh: `create_models` awaits an offline refresh
//! (`allowNetwork: false`), which restores the last persisted Prime Inference
//! catalog without touching the network, then starts the network refresh in
//! the background (unless `EUKHE_OFFLINE` is set). The Prime provider gates
//! its own fetch to once an hour; a failed or slow fetch never delays or
//! fails session open, and the compiled offline catalog serves until a fetch
//! succeeds — the same no-cold-start posture as eukhe's catalog chain.
//!
//! # auth.json mapping
//!
//! eukhe entries (`crate::auth::AuthCredential`) map to pi-ai credentials:
//!
//! | eukhe entry | pi-ai credential |
//! |---|---|
//! | `{type:"api_key", key, primeTeam?:{teamId,…}}` | `ApiKeyCredential { key, env: { PRIME_TEAM_ID: teamId } }` |
//! | `{type:"api_key", key, env?}` | `ApiKeyCredential { key, env }` (`env` is pi-ai's field) |
//! | `{type:"oauth", access, refresh, expires, accountId?, enterpriseUrl?, …}` | `OAuthCredential { access, refresh, expires, extra: {accountId, enterpriseUrl, …} }` |
//! | `{type:"mcp_static_token", …}` and other eukhe-only types | not a pi-ai credential: `read` gives `None`, `list` skips it |
//!
//! Field names are identical on both sides (`access`, `refresh`, `expires`
//! in epoch milliseconds, `accountId`, `enterpriseUrl`); OAuth extras round
//! trip verbatim. An OAuth entry without a string `refresh` token is invalid
//! for pi-ai (the TS `ReadOnlyAuthStorage` rule) and its read fails with
//! `Invalid auth.json credential for provider "<id>"`.
//!
//! Reads apply eukhe's resolution rules: a stored key goes through
//! `resolve_config_value` (`!command`, env var name, or literal; the TS
//! `AuthStorage.read`), and for `prime-inference` a non-empty `PRIME_API_KEY`
//! hides the stored key (eukhe resolves the Prime environment key before the
//! stored one) while the stored team survives, and a non-empty
//! `PRIME_TEAM_ID` hides the stored team (the env pin owns the team).
//!
//! Writes (OAuth refresh, login, logout) rewrite only the provider's entry:
//! OAuth credentials in the pi-ai shape (a superset the old engine reads),
//! api-key credentials as `{type, key, primeTeam?, env?}`, keeping the
//! stored `primeTeam` when the key is unchanged. The OAuth refresh runs
//! outside the document lock (eukhe's load-then-lock shape: a token fetch
//! never holds the file lock); the write re-reads under the lock and, when
//! another writer changed the entry meanwhile, keeps that writer's newer
//! credential and writes nothing.
//!
//! # models.json
//!
//! eukhe's schema (`crate::models::custom`) with eukhe's semantics: provider
//! `baseUrl`/`compat` apply to the provider's built-in models,
//! `modelOverrides` deep-merge into built-in models, `models` add or replace
//! models (defaulting `api`/`baseUrl` from the provider's first built-in
//! model), model `headers` ride the model, provider `headers` and
//! `authHeader` ride every request, and the provider `apiKey` (a config
//! value) applies when neither a stored credential nor the provider's
//! environment key resolves.

mod compose;
mod stores;

use std::path::Path;
use std::sync::Arc;

use eukhe_chord::context::Context;
use eukhe_durable::harness::types::ModelRef;
use eukhe_pi_ai::auth::{AuthContext, AuthOperationOptions};
use eukhe_pi_ai::models::{
    clamp_thinking_level, create_models as create_pi_models, CreateModelsOptions, Models,
    ModelsRefreshOptions,
};
use eukhe_pi_ai::providers::all::builtin_providers;
use eukhe_pi_ai::utils::abort::operation_signal;
use eukhe_types::pi_ai::{Model, ModelThinkingLevel};
use serde_json::{json, Value};

use super::deps::ModelRequest;
use crate::models::{
    find_initial_model, model_allowed, resolve_cli_model, resolve_model_scope_from_models,
    InitialModelOptions, ModelAllowlistRefusal,
};
use crate::settings::SettingsManager;

/// Errors building the model collection or resolving a model.
#[derive(Debug, thiserror::Error)]
pub enum ModelsError {
    /// `models.json` could not be read, parsed, or validated, or a model it
    /// defines is not a valid model. The message names the file.
    #[error("{0}")]
    ModelsJson(String),
    /// Reading the credentials or the model catalog failed.
    #[error("Failed to determine the available models: {0}")]
    Catalog(String),
    /// The requested model does not resolve (eukhe's `--model` messages).
    #[error("{0}")]
    Requested(String),
    /// The model resolves only to a template rebuilt for an unknown id;
    /// pi-ai serves registered models only.
    #[error(
        "Model \"{provider}/{model_id}\" not found. Use \"eukhe model list\" to see available models."
    )]
    ModelNotFound { provider: String, model_id: String },
    /// The resolved model is outside the settings `allowedModels` allowlist.
    #[error(transparent)]
    NotAllowed(#[from] ModelAllowlistRefusal),
    /// The global settings could not be read, so the allowlist policy is
    /// unknown: resolution fails closed.
    #[error(
        "The daemon model allowlist could not be read ({reason}); refusing to resolve model \"{selector}\" -- the daemon fails closed instead of bypassing the configured allowedModels policy. Fix settings.json and retry."
    )]
    AllowlistUnreadable { reason: String, selector: String },
    /// The caller's context was cancelled.
    #[error("Model resolution was cancelled")]
    Cancelled,
}

/// The model and thinking level of a new conversation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedModel {
    pub model: ModelRef,
    pub thinking: ModelThinkingLevel,
}

/// `eukhe_pi_ai::models::Models` with every built-in pi-ai provider,
/// credentials from eukhe's auth storage, custom providers/models from
/// eukhe `models.json`, and Prime Inference through the pi-ai
/// `prime-inference` provider. See the module docs for the stores and the
/// refresh policy.
///
/// # Errors
///
/// [`ModelsError::ModelsJson`] when `models.json` is unreadable or invalid;
/// [`ModelsError::Cancelled`] when `cx` is cancelled during the offline
/// catalog restore.
pub async fn create_models(agent_dir: &Path, cx: &Context) -> Result<Models, ModelsError> {
    let network = if crate::models::private_auth::is_offline_mode_enabled() {
        CatalogNetwork::Offline
    } else {
        CatalogNetwork::Background
    };
    build_models(agent_dir, None, network, cx).await
}

/// Whether [`build_models`] starts the network catalog refresh.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CatalogNetwork {
    /// Refresh from the network in the background after the offline restore.
    Background,
    /// Offline restore only (`EUKHE_OFFLINE`).
    Offline,
}

/// [`create_models`] with an injectable auth context (`None`: the process
/// environment and file system).
async fn build_models(
    agent_dir: &Path,
    auth_context: Option<Arc<dyn AuthContext>>,
    network: CatalogNetwork,
    cx: &Context,
) -> Result<Models, ModelsError> {
    let models = create_pi_models(CreateModelsOptions {
        credentials: Some(Arc::new(stores::AuthJsonCredentialStore::new(
            agent_dir.join("auth.json"),
        ))),
        models_store: Some(Arc::new(stores::FileModelsStore::new(
            agent_dir.join("models-store.json"),
        ))),
        auth_context,
    });
    for provider in compose::compose_providers(builtin_providers(), &agent_dir.join("models.json"))?
    {
        models.set_provider(provider);
    }

    let restored = models
        .refresh(ModelsRefreshOptions {
            allow_network: Some(false),
            signal: cx.abort_signal(),
            ..ModelsRefreshOptions::default()
        })
        .await;
    if restored.aborted {
        return Err(ModelsError::Cancelled);
    }
    for (provider, error) in &restored.errors {
        tracing::warn!(%provider, "restoring the persisted model catalog failed: {error}");
    }
    match network {
        CatalogNetwork::Offline => {}
        CatalogNetwork::Background => {
            let background = models.clone();
            tokio::spawn(async move {
                let refreshed = background.refresh(ModelsRefreshOptions::default()).await;
                for (provider, error) in &refreshed.errors {
                    tracing::warn!(%provider, "refreshing the model catalog failed: {error}");
                }
            });
        }
    }
    Ok(models)
}

/// Model + thinking of a new root conversation, as eukhe's daemon resolves
/// a fresh session (`AgentSessionEngine::resolve_registry_model` and
/// `effective_thinking`):
///
/// 1. `requested` resolves against the full catalog like `--provider` +
///    `--model` (`resolve_cli_model`), whether or not it has credentials;
/// 2. otherwise the startup chain over the models with credentials
///    (`find_initial_model`): the settings `enabledModels` scope (the saved
///    default when in scope, else the first scoped model), the settings
///    `defaultProvider`/`defaultModel`, the featured default, the first
///    available model;
/// 3. the result must pass the settings `allowedModels` allowlist (no
///    fallback on refusal; an unreadable global settings document fails
///    closed);
/// 4. thinking: `requested_thinking`, else the model pattern's `:level`,
///    else the scoped entry's `:level`, else `defaultThinkingLevel`, else
///    `medium` — clamped to the model's supported levels.
///
/// `Ok(None)` when nothing was requested and no model has credentials.
///
/// # Errors
///
/// [`ModelsError::Requested`] / [`ModelsError::ModelNotFound`] for a
/// requested model that does not resolve, the allowlist errors,
/// [`ModelsError::Catalog`] when the credential checks fail, and
/// [`ModelsError::Cancelled`] when `cx` is cancelled.
pub async fn resolve_session_model(
    models: &Models,
    settings: &SettingsManager,
    requested: Option<&ModelRequest>,
    requested_thinking: Option<ModelThinkingLevel>,
    cx: &Context,
) -> Result<Option<ResolvedModel>, ModelsError> {
    let signal = operation_signal(cx.abort_signal());
    let all = models.get_models(None);
    let available = models
        .get_available(None, AuthOperationOptions::with_signal(signal.clone()))
        .await
        .map_err(|error| {
            if signal.aborted() {
                ModelsError::Cancelled
            } else {
                ModelsError::Catalog(error.to_string())
            }
        })?;
    let all_legacy = legacy_models(&all)?;
    let available_legacy = legacy_models(&available)?;

    let (model, pattern_thinking) = if let Some(requested) = requested {
        let result = resolve_cli_model(
            requested.provider.as_deref(),
            &requested.pattern,
            &all_legacy,
        );
        let Some(resolved) = result.model else {
            let selector = match &requested.provider {
                Some(provider) => format!("{provider}/{}", requested.pattern),
                None => requested.pattern.clone(),
            };
            return Err(ModelsError::Requested(result.error.unwrap_or_else(|| {
                format!(
                    "Model \"{selector}\" not found. Use \"eukhe model list\" to see available models."
                )
            })));
        };
        let thinking = result.thinking_level.and_then(agent_thinking_level);
        (catalog_model(&all, &resolved)?, thinking)
    } else {
        let patterns = settings.get_enabled_models().unwrap_or_default();
        let scoped = if patterns.is_empty() {
            Vec::new()
        } else {
            resolve_model_scope_from_models(&patterns, &available_legacy)
        };
        let mut options = InitialModelOptions {
            cli_provider: None,
            cli_model: None,
            scoped_models: &scoped,
            is_continuing: false,
            default_provider: settings.get_default_provider(),
            default_model_id: settings.get_default_model(),
            all_models: &all_legacy,
            available_models: &available_legacy,
        };
        let mut picked = find_initial_model(&options);
        if let Some(rebuilt) = picked.as_ref().filter(|model| !in_catalog(&all, model)) {
            // eukhe rebuilds a saved default missing from the catalog on the
            // provider's template; pi-ai `Models` serves registered models
            // only, so the chain continues past the saved default.
            tracing::warn!(
                provider = %rebuilt.provider,
                model = %rebuilt.id,
                "the saved default model is not in the catalog; using the next startup default"
            );
            options.default_model_id = None;
            picked = find_initial_model(&options);
        }
        let Some(picked) = picked else {
            return Ok(None);
        };
        let thinking = scoped
            .iter()
            .find(|scoped| scoped.model.provider == picked.provider && scoped.model.id == picked.id)
            .and_then(|scoped| scoped.thinking_level)
            .and_then(agent_thinking_level);
        (catalog_model(&all, &picked)?, thinking)
    };

    enforce_allowlist(settings, &format!("{}/{}", model.provider, model.id))?;
    let thinking = requested_thinking
        .or(pattern_thinking)
        .or_else(|| {
            settings
                .get_default_thinking_level()
                .map(super::thinking_level)
        })
        .unwrap_or(ModelThinkingLevel::Medium);
    Ok(Some(ResolvedModel {
        thinking: clamp_thinking_level(&model, thinking),
        model: ModelRef {
            provider: model.provider,
            model_id: model.id,
        },
    }))
}

/// The resolver's view of a pi-ai model: eukhe's resolver matches on
/// provider, id, and name only.
fn legacy_models(models: &[Model]) -> Result<Vec<eukhe_types::ai::Model>, ModelsError> {
    models
        .iter()
        .map(|model| {
            serde_json::from_value(json!({
                "id": model.id,
                "name": model.name,
                "api": model.api,
                "provider": model.provider,
                "baseUrl": model.base_url,
                "reasoning": model.reasoning,
                "input": [],
                "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
                "contextWindow": model.context_window,
                "maxTokens": model.max_tokens,
            }))
            .map_err(|error| {
                ModelsError::Catalog(format!(
                    "model {}/{} cannot be matched: {error}",
                    model.provider, model.id
                ))
            })
        })
        .collect()
}

fn in_catalog(all: &[Model], model: &eukhe_types::ai::Model) -> bool {
    all.iter()
        .any(|entry| entry.provider == model.provider && entry.id == model.id)
}

fn catalog_model(all: &[Model], model: &eukhe_types::ai::Model) -> Result<Model, ModelsError> {
    all.iter()
        .find(|entry| entry.provider == model.provider && entry.id == model.id)
        .cloned()
        .ok_or_else(|| ModelsError::ModelNotFound {
            provider: model.provider.clone(),
            model_id: model.id.clone(),
        })
}

/// A `model:level` suffix level as a pi-ai level (same wire names).
fn agent_thinking_level(level: eukhe_agent::types::ThinkingLevel) -> Option<ModelThinkingLevel> {
    let wire = serde_json::to_value(level).ok()?;
    wire.as_str().and_then(ModelThinkingLevel::parse)
}

/// The daemon's `allowedModels` gate (`eukhe-daemon` `model_allowlist`):
/// unset is unrestricted, a configured list refuses other models, and an
/// unreadable or malformed global document fails closed.
fn enforce_allowlist(settings: &SettingsManager, selector: &str) -> Result<(), ModelsError> {
    let unreadable = |reason: String| ModelsError::AllowlistUnreadable {
        reason,
        selector: selector.to_owned(),
    };
    if let Some(error) = settings.global_load_error() {
        return Err(unreadable(error.to_owned()));
    }
    if let Some(patterns) = settings.get_allowed_models() {
        if model_allowed(selector, &patterns) {
            return Ok(());
        }
        return Err(ModelsError::NotAllowed(ModelAllowlistRefusal {
            selector: selector.to_owned(),
        }));
    }
    if let Some(raw) = settings.global_raw() {
        if !raw.is_object() {
            return Err(unreadable(
                "the global settings document is not a JSON object".to_owned(),
            ));
        }
        let malformed = match raw.get("allowedModels") {
            None | Some(Value::Null) => false,
            Some(value) => value
                .as_array()
                .is_none_or(|items| items.iter().any(|item| item.as_str().is_none())),
        };
        if malformed {
            return Err(unreadable(
                "allowedModels is present but is not an array of strings".to_owned(),
            ));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use eukhe_chord::context::BACKGROUND_CONTEXT;
    use eukhe_pi_ai::auth::{ApiKeyResolveInput, ModelAuth};
    use eukhe_pi_ai::providers::all::get_builtin_models;
    use eukhe_types::pi_ai::{Modality, ProviderHeaders};
    use futures::future::BoxFuture;

    use super::*;
    use crate::settings::types::Settings;

    /// No ambient credentials: no environment variables, no credential files.
    struct EmptyAuthContext;

    impl AuthContext for EmptyAuthContext {
        fn env<'a>(&'a self, _name: &'a str) -> BoxFuture<'a, Option<String>> {
            Box::pin(async { None })
        }

        fn file_exists<'a>(&'a self, _path: &'a str) -> BoxFuture<'a, bool> {
            Box::pin(async { false })
        }
    }

    const BATTERY_MODELS_JSON: &str = r#"{
        // comments and trailing commas are allowed, like today
        "providers": {
            "battery": {
                "baseUrl": "http://127.0.0.1:9/v1",
                "apiKey": "battery-key",
                "api": "openai-completions",
                "headers": { "X-Battery": "1" },
                "models": [
                    { "id": "mock-reason", "reasoning": true, "contextWindow": 64000,
                      "maxTokens": 4096, "headers": { "X-Model": "m" } },
                    { "id": "mock-plain", "input": ["text", "image"] },
                ],
            },
        },
    }"#;

    async fn offline_models(agent_dir: &Path) -> Result<Models, ModelsError> {
        build_models(
            agent_dir,
            Some(Arc::new(EmptyAuthContext)),
            CatalogNetwork::Offline,
            &BACKGROUND_CONTEXT,
        )
        .await
    }

    async fn battery_models(agent_dir: &Path, models_json: &str) -> Models {
        std::fs::write(agent_dir.join("models.json"), models_json).unwrap();
        offline_models(agent_dir).await.unwrap()
    }

    fn settings(value: Value) -> SettingsManager {
        let settings: Settings = serde_json::from_value(value).unwrap();
        SettingsManager::in_memory(&settings)
    }

    async fn resolve(
        models: &Models,
        settings: &SettingsManager,
        requested: Option<(&str, &str)>,
        thinking: Option<ModelThinkingLevel>,
    ) -> Result<Option<ResolvedModel>, ModelsError> {
        let requested = requested.map(|(provider, pattern)| ModelRequest {
            provider: Some(provider.to_owned()),
            pattern: pattern.to_owned(),
        });
        resolve_session_model(
            models,
            settings,
            requested.as_ref(),
            thinking,
            &BACKGROUND_CONTEXT,
        )
        .await
    }

    fn resolved(provider: &str, model_id: &str, thinking: ModelThinkingLevel) -> ResolvedModel {
        ResolvedModel {
            model: ModelRef {
                provider: provider.to_owned(),
                model_id: model_id.to_owned(),
            },
            thinking,
        }
    }

    #[tokio::test]
    async fn custom_models_json_providers_and_overrides_appear_in_models() {
        let dir = tempfile::tempdir().unwrap();
        let anthropic = get_builtin_models("anthropic").remove(0);
        let models_json = BATTERY_MODELS_JSON.replace(
            "\"providers\": {",
            &format!(
                "\"providers\": {{ \"anthropic\": {{ \"modelOverrides\": {{ \"{}\": {{ \"name\": \"Renamed\", \"maxTokens\": 1234 }} }} }},",
                anthropic.id
            ),
        );
        let models = battery_models(dir.path(), &models_json).await;

        let reason = models.get_model("battery", "mock-reason").unwrap();
        assert_eq!(
            serde_json::to_value(&reason).unwrap(),
            json!({
                "id": "mock-reason", "name": "mock-reason", "api": "openai-completions",
                "provider": "battery", "baseUrl": "http://127.0.0.1:9/v1",
                "input": ["text"],
                "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
                "headers": { "X-Model": "m" },
                "reasoning": true, "contextWindow": 64000, "maxTokens": 4096
            })
        );
        let plain = models.get_model("battery", "mock-plain").unwrap();
        assert_eq!(plain.input, [Modality::Text, Modality::Image]);
        assert_eq!((plain.context_window, plain.max_tokens), (128_000, 16_384));

        let overridden = models.get_model("anthropic", &anthropic.id).unwrap();
        assert_eq!(overridden.name, "Renamed");
        assert_eq!(overridden.max_tokens, 1234);
        assert_eq!(overridden.cost, anthropic.cost);

        // The configured apiKey authenticates the custom provider (and only
        // it: nothing else has credentials); its headers ride the auth.
        let available = models
            .get_available(None, AuthOperationOptions::default())
            .await
            .unwrap();
        let available: Vec<(&str, &str)> = available
            .iter()
            .map(|model| (model.provider.as_str(), model.id.as_str()))
            .collect();
        assert_eq!(
            available,
            [("battery", "mock-reason"), ("battery", "mock-plain")]
        );
        let provider = models.get_provider("battery").unwrap();
        let auth = provider
            .auth
            .api_key
            .as_ref()
            .unwrap()
            .resolve(ApiKeyResolveInput {
                ctx: Arc::new(EmptyAuthContext),
                credential: None,
                signal: operation_signal(None),
            })
            .await
            .unwrap()
            .unwrap();
        assert_eq!(
            auth.auth,
            ModelAuth {
                api_key: Some("battery-key".to_owned()),
                headers: Some(ProviderHeaders::from([(
                    "X-Battery".to_owned(),
                    Some("1".to_owned())
                )])),
                base_url: None,
            }
        );
    }

    #[tokio::test]
    async fn an_invalid_models_json_fails_with_the_file_named() {
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(
            dir.path().join("models.json"),
            r#"{ "providers": { "custom": { "models": [{ "id": "x" }] } } }"#,
        )
        .unwrap();
        let Err(error) = offline_models(dir.path()).await else {
            panic!("an invalid models.json must fail");
        };
        assert_eq!(
            error.to_string(),
            format!(
                "Provider custom: \"baseUrl\" is required when defining custom models.\n\nFile: {}",
                dir.path().join("models.json").display()
            )
        );
    }

    #[tokio::test]
    async fn settings_default_model_and_thinking_resolve_clamped() {
        let dir = tempfile::tempdir().unwrap();
        let models = battery_models(dir.path(), BATTERY_MODELS_JSON).await;
        let reason = settings(json!({
            "defaultProvider": "battery", "defaultModel": "mock-reason",
            "defaultThinkingLevel": "high"
        }));
        assert_eq!(
            resolve(&models, &reason, None, None).await.unwrap(),
            Some(resolved("battery", "mock-reason", ModelThinkingLevel::High))
        );
        // A non-reasoning default clamps the level to off.
        let plain = settings(json!({
            "defaultProvider": "battery", "defaultModel": "mock-plain",
            "defaultThinkingLevel": "high"
        }));
        assert_eq!(
            resolve(&models, &plain, None, None).await.unwrap(),
            Some(resolved("battery", "mock-plain", ModelThinkingLevel::Off))
        );
        // Without a default level the session starts at medium.
        let unset =
            settings(json!({ "defaultProvider": "battery", "defaultModel": "mock-reason" }));
        assert_eq!(
            resolve(&models, &unset, None, None).await.unwrap(),
            Some(resolved(
                "battery",
                "mock-reason",
                ModelThinkingLevel::Medium
            ))
        );
        // The enabledModels scope picks its first model and its `:level`.
        let scoped = settings(json!({ "enabledModels": ["battery/mock-reason:low"] }));
        assert_eq!(
            resolve(&models, &scoped, None, None).await.unwrap(),
            Some(resolved("battery", "mock-reason", ModelThinkingLevel::Low))
        );
    }

    #[tokio::test]
    async fn a_requested_model_and_level_win_over_settings() {
        let dir = tempfile::tempdir().unwrap();
        let models = battery_models(dir.path(), BATTERY_MODELS_JSON).await;
        let defaults = settings(json!({
            "defaultProvider": "battery", "defaultModel": "mock-plain",
            "defaultThinkingLevel": "minimal"
        }));
        assert_eq!(
            resolve(
                &models,
                &defaults,
                Some(("battery", "mock-reason")),
                Some(ModelThinkingLevel::Low)
            )
            .await
            .unwrap(),
            Some(resolved("battery", "mock-reason", ModelThinkingLevel::Low))
        );
        // The requested level clamps to the model: max needs an explicit map entry.
        assert_eq!(
            resolve(
                &models,
                &defaults,
                Some(("battery", "mock-reason")),
                Some(ModelThinkingLevel::Max)
            )
            .await
            .unwrap(),
            Some(resolved("battery", "mock-reason", ModelThinkingLevel::High))
        );
        assert_eq!(
            resolve(&models, &defaults, Some(("battery", "nope")), None)
                .await
                .unwrap_err()
                .to_string(),
            "Model \"battery/nope\" not found. Use \"eukhe model list\" to see available models."
        );
    }

    #[tokio::test]
    async fn allowed_models_refuses_models_outside_the_allowlist() {
        let dir = tempfile::tempdir().unwrap();
        let models = battery_models(dir.path(), BATTERY_MODELS_JSON).await;
        let allowlisted = settings(json!({
            "defaultProvider": "battery", "defaultModel": "mock-plain",
            "allowedModels": ["battery/mock-reason"]
        }));
        match resolve(&models, &allowlisted, None, None).await {
            Err(ModelsError::NotAllowed(refusal)) => {
                assert_eq!(refusal.selector, "battery/mock-plain");
            }
            other => panic!("expected an allowlist refusal, got {other:?}"),
        }
        assert_eq!(
            resolve(
                &models,
                &allowlisted,
                Some(("battery", "mock-reason")),
                None
            )
            .await
            .unwrap(),
            Some(resolved(
                "battery",
                "mock-reason",
                ModelThinkingLevel::Medium
            ))
        );
    }

    #[tokio::test]
    async fn nothing_resolves_without_credentials() {
        let dir = tempfile::tempdir().unwrap();
        let models = offline_models(dir.path()).await.unwrap();
        assert!(!models.get_models(None).is_empty());
        assert_eq!(
            resolve(&models, &settings(json!({})), None, None)
                .await
                .unwrap(),
            None
        );
    }
}
