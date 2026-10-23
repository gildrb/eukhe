//! The pi-ai model collection of a durable eukhe session and the model of a
//! new root conversation.
//!
//! [`create_models`] registers every built-in pi-ai provider (the eukhe
//! `prime-inference` provider included), composes the user's
//! `<agent_dir>/models.json` over them (`compose`), and wires the
//! credential store (`stores`): a pi-ai `CredentialStore` over eukhe's
//! `<agent_dir>/auth.json`, through eukhe's own `FileAuthStorageBackend`
//! (same file, same lock directory, same atomic 0600 writes, same
//! process-local serialization), so every eukhe reader and writer shares
//! one document.
//!
//! Catalogs are fully local: every provider serves its compiled catalog
//! and the collection never refreshes a provider's model list over the
//! network.
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
//! OAuth credentials in the pi-ai shape (a superset of eukhe's own),
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
//! environment key resolves. A bad `providers.<id>` entry drops only that
//! provider; [`SessionModels::diagnostics`] names it, the same way the
//! registry's diagnostics do (one loader serves both views).
//!
//! # The saved default model
//!
//! [`resolve_session_model`] never moves past the saved default
//! (`defaultProvider`/`defaultModel`) in silence. A saved default that is
//! not in the catalog, or not in the `enabledModels` scope, gives the next
//! startup default with the [`Substitution`]. A saved default whose
//! provider has no credentials is the typed error
//! [`ModelsError::DefaultUnusable`]: the session never moves to another
//! provider. A session opens on [`resolve_open_model`] and shows the
//! notice row [`DEFAULT_MODEL_NOTICE_CUSTOM_TYPE`]. The Bend model is
//! `bend/default_model.bend`.

mod compose;
pub(crate) mod failover;
pub(crate) mod image_route;
pub(crate) mod park;
pub(crate) mod provider;
mod stores;
pub(crate) mod timing;

use std::path::Path;
use std::sync::Arc;

use eukhe_ai::auth::{AuthContext, AuthOperationOptions};
use eukhe_ai::models::{
    clamp_thinking_level, create_models as create_pi_models, CreateModelsOptions, Models,
};
use eukhe_ai::providers::all::builtin_providers;
use eukhe_ai::utils::abort::operation_signal;
use eukhe_chord::context::Context;
use eukhe_durable::harness::types::ModelRef;
use eukhe_types::pi_ai::{Model, ModelThinkingLevel};
use serde_json::Value;

use super::deps::ModelRequest;
use crate::models::{
    find_initial_model, model_allowed, resolve_cli_model, resolve_default,
    resolve_model_scope_from_models, saved_default_facts, DefaultMiss, DefaultResolution,
    InitialModelOptions, ModelAllowlistRefusal,
};
use crate::settings::SettingsManager;

/// The custom type of the row that tells why a session did not open on the
/// saved default model (display-only: the user sees it, the model does
/// not).
pub const DEFAULT_MODEL_NOTICE_CUSTOM_TYPE: &str = "eukhe.default_model";

/// Errors resolving a model.
#[derive(Debug, thiserror::Error)]
pub enum ModelsError {
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
    /// The saved default model cannot run and no model runs in its place:
    /// its provider has no credentials (no other provider takes its
    /// place), or no other model has credentials.
    #[error("{}", .0.refusal())]
    DefaultUnusable(Substitution),
    /// The caller's context was cancelled.
    #[error("Model resolution was cancelled")]
    Cancelled,
}

/// The saved default model a session does not run on, and why.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Substitution {
    /// The saved default (`defaultProvider`/`defaultModel`).
    pub wanted: ModelRef,
    pub reason: DefaultMiss,
}

impl Substitution {
    /// The sentence that names the saved default and the reason.
    fn missed(&self) -> String {
        format!(
            "The saved default model {}/{} did not run: {}.",
            self.wanted.provider, self.wanted.model_id, self.reason
        )
    }

    /// The text of [`ModelsError::DefaultUnusable`]: the saved default,
    /// the reason, and what to do.
    #[must_use]
    pub fn refusal(&self) -> String {
        let fix = match self.reason {
            DefaultMiss::NoCredentials => {
                "eukhe does not move to another provider. Sign in with /login, set the provider's API key, or change defaultProvider/defaultModel."
            }
            DefaultMiss::NotInCatalog => {
                "No other model has credentials. Run \"eukhe model list\", fix models.json, or change defaultProvider/defaultModel."
            }
            DefaultMiss::NotInScope => {
                "No other model is in the scope. Change enabledModels or defaultProvider/defaultModel."
            }
        };
        format!("{} {fix}", self.missed())
    }
}

/// The model and thinking level of a new conversation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedModel {
    pub model: ModelRef,
    pub thinking: ModelThinkingLevel,
    /// The saved default this model runs in place of; `None` when the
    /// model is the saved default, nothing is saved, or the caller
    /// requested the model.
    pub substituted: Option<Substitution>,
}

/// The model collection of a session and the models.json diagnostics.
pub struct SessionModels {
    pub models: Models,
    /// One diagnostic for each bad `providers.<id>` entry (that provider
    /// is dropped), or one for a file that cannot be read or parsed (no
    /// custom models). Empty when the file is good or absent.
    pub diagnostics: Vec<String>,
}

/// `eukhe_ai::models::Models` with every built-in pi-ai provider,
/// credentials from eukhe's auth storage, custom providers/models from
/// eukhe `models.json`, and Prime Inference through the pi-ai
/// `prime-inference` provider's compiled catalog. See the module docs.
#[must_use]
pub fn create_models(agent_dir: &Path) -> SessionModels {
    build_models(agent_dir, None)
}

/// [`create_models`] with an injectable auth context (`None`: the process
/// environment and file system).
fn build_models(agent_dir: &Path, auth_context: Option<Arc<dyn AuthContext>>) -> SessionModels {
    let models = create_pi_models(CreateModelsOptions {
        credentials: Some(Arc::new(stores::AuthJsonCredentialStore::new(
            agent_dir.join(crate::auth::AUTH_FILE_NAME),
        ))),
        models_store: None,
        auth_context,
    });
    let (providers, diagnostics) =
        compose::compose_providers(builtin_providers(), &agent_dir.join("models.json"));
    for provider in providers {
        models.set_provider(provider);
    }
    // The installed tiny models as `local/<id>` classifiers (S9 `judge`).
    crate::tiny::judge::add_local_provider(&models, agent_dir);
    SessionModels {
        models,
        diagnostics,
    }
}

/// `<agent_dir>/models.json` composed over the providers already in
/// `models` (the scripted faux verification seam's collection), plus the
/// custom providers it defines: a `models.json` faux-api model streams
/// through the registered scripted provider, as it did through the old
/// registry. A missing file changes nothing. Returns the models.json
/// diagnostics ([`SessionModels::diagnostics`]).
#[must_use]
pub fn compose_models_json(models: &Models, agent_dir: &Path) -> Vec<String> {
    let base = models
        .get_providers()
        .iter()
        .map(|provider| eukhe_ai::models::Provider::clone(provider))
        .collect();
    let (providers, diagnostics) = compose::compose_providers(base, &agent_dir.join("models.json"));
    for provider in providers {
        models.set_provider(provider);
    }
    diagnostics
}

/// Model + thinking of a new root conversation, as eukhe's daemon resolves
/// a fresh session (registry model resolution and effective thinking):
///
/// 1. `requested` resolves against the full catalog like `--provider` +
///    `--model` (`resolve_cli_model`), whether or not it has credentials;
/// 2. otherwise the startup chain over the models with credentials
///    (`find_initial_model`): the settings `enabledModels` scope (the saved
///    default when in scope, else the first scoped model), the settings
///    `defaultProvider`/`defaultModel`, the featured default, the first
///    available model. A saved default that is not in the catalog or not
///    in the scope gives the next startup default with the
///    [`Substitution`]; a saved default whose provider has no
///    credentials is [`ModelsError::DefaultUnusable`];
/// 3. the result must pass the settings `allowedModels` allowlist (no
///    fallback on refusal; an unreadable global settings document fails
///    closed);
/// 4. thinking: `requested_thinking`, else the model pattern's `:level`,
///    else the scoped entry's `:level`, else `defaultThinkingLevel`, else
///    `medium` — clamped to the model's supported levels.
///
/// `Ok(None)` when nothing was requested, nothing is saved, and no model
/// has credentials.
///
/// # Errors
///
/// [`ModelsError::Requested`] / [`ModelsError::ModelNotFound`] for a
/// requested model that does not resolve, [`ModelsError::DefaultUnusable`]
/// for a saved default that cannot run with no model in its place, the
/// allowlist errors, [`ModelsError::Catalog`] when the credential checks
/// fail, and [`ModelsError::Cancelled`] when `cx` is cancelled.
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

    let (model, pattern_thinking, substituted) = if let Some(requested) = requested {
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
        let thinking = result.thinking_level;
        (catalog_model(&all, &resolved)?, thinking, None)
    } else {
        let patterns = settings.get_enabled_models().unwrap_or_default();
        let scoped = if patterns.is_empty() {
            Vec::new()
        } else {
            resolve_model_scope_from_models(&patterns, &available_legacy)
        };
        let default_provider = settings.get_default_provider();
        let default_model_id = settings.get_default_model();
        let options = InitialModelOptions {
            cli_provider: None,
            cli_model: None,
            scoped_models: &scoped,
            is_continuing: false,
            default_provider: default_provider.as_deref(),
            default_model_id: default_model_id.as_deref(),
            all_models: &all_legacy,
            available_models: &available_legacy,
        };
        // The chain's pick past the saved default.
        let next = find_initial_model(&InitialModelOptions {
            default_model_id: None,
            ..options
        });
        let substitution = |reason| {
            default_provider
                .as_deref()
                .zip(default_model_id.as_deref())
                .map(|(provider, model_id)| Substitution {
                    wanted: ModelRef {
                        provider: provider.to_owned(),
                        model_id: model_id.to_owned(),
                    },
                    reason,
                })
        };
        let (picked, substituted) =
            match resolve_default(saved_default_facts(&options), next.is_some()) {
                DefaultResolution::Saved => (find_initial_model(&options), None),
                DefaultResolution::Next(miss) => (next, miss.and_then(substitution)),
                DefaultResolution::Nothing => return Ok(None),
                DefaultResolution::Refused(miss) => {
                    return match substitution(miss) {
                        Some(substitution) => Err(ModelsError::DefaultUnusable(substitution)),
                        None => Ok(None),
                    }
                }
            };
        let Some(picked) = picked else {
            return Ok(None);
        };
        let thinking = scoped
            .iter()
            .find(|scoped| scoped.model.provider == picked.provider && scoped.model.id == picked.id)
            .and_then(|scoped| scoped.thinking_level);
        (catalog_model(&all, &picked)?, thinking, substituted)
    };

    enforce_allowlist(settings, &format!("{}/{}", model.provider, model.id))?;
    let thinking = requested_thinking
        .or(pattern_thinking)
        .unwrap_or_else(|| super::default_thinking_level(settings));
    Ok(Some(ResolvedModel {
        thinking: clamp_thinking_level(&model, thinking),
        model: ModelRef {
            provider: model.provider,
            model_id: model.id,
        },
        substituted,
    }))
}

/// The model a session opens with ([`resolve_open_model`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct OpenModel {
    /// The model and thinking level; `None` when no model resolves.
    pub(crate) resolved: Option<ResolvedModel>,
    /// The saved default that cannot run when no model runs in its place
    /// ([`ModelsError::DefaultUnusable`]).
    pub(crate) refused: Option<Substitution>,
}

impl OpenModel {
    /// The text of the session's notice row: the saved default, why it
    /// did not run, and the model in its place (or none). `None` when
    /// the session runs on the saved default, nothing is saved, or the
    /// caller requested the model.
    pub(crate) fn notice(&self) -> Option<String> {
        match (&self.resolved, &self.refused) {
            (Some(resolved), _) => resolved.substituted.as_ref().map(|substitution| {
                format!(
                    "{} The session runs on {}/{}.",
                    substitution.missed(),
                    resolved.model.provider,
                    resolved.model.model_id
                )
            }),
            (None, Some(substitution)) => Some(format!(
                "{} The session has no model.",
                substitution.refusal()
            )),
            (None, None) => None,
        }
    }
}

/// [`resolve_session_model`] for a session that opens: a saved default
/// that cannot run ([`ModelsError::DefaultUnusable`]) opens the session
/// with no model and the reason, so the user can sign in or change the
/// default from the session.
///
/// # Errors
///
/// Every other error of [`resolve_session_model`].
pub(crate) async fn resolve_open_model(
    models: &Models,
    settings: &SettingsManager,
    requested: Option<&ModelRequest>,
    requested_thinking: Option<ModelThinkingLevel>,
    cx: &Context,
) -> Result<OpenModel, ModelsError> {
    match resolve_session_model(models, settings, requested, requested_thinking, cx).await {
        Ok(resolved) => Ok(OpenModel {
            resolved,
            refused: None,
        }),
        Err(ModelsError::DefaultUnusable(substitution)) => Ok(OpenModel {
            resolved: None,
            refused: Some(substitution),
        }),
        Err(error) => Err(error),
    }
}

/// The resolver's view of the pi-ai models (eukhe's resolver matches on
/// provider, id, and name).
fn legacy_models(models: &[Model]) -> Result<Vec<eukhe_types::ai::Model>, ModelsError> {
    models
        .iter()
        .map(|model| {
            eukhe_models::pi_ai_model::registry_model(model).map_err(|error| {
                ModelsError::Catalog(format!(
                    "model {}/{} cannot be matched: {error}",
                    model.provider, model.id
                ))
            })
        })
        .collect()
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
    use eukhe_ai::auth::{ApiKeyResolveInput, ModelAuth};
    use eukhe_ai::models::chat_models;
    use eukhe_ai::providers::all::get_builtin_models;
    use eukhe_chord::context::BACKGROUND_CONTEXT;
    use eukhe_types::pi_ai::{Modality, ProviderHeaders};
    use futures::future::BoxFuture;
    use serde_json::json;

    use super::*;
    use crate::models::ModelRegistry;
    use crate::settings::types::Settings;

    /// The two views of one models.json — the registry (`ModelRegistry`,
    /// the picker and model lists) and this collection (the sessions) —
    /// come from one parse and one composition: on the same document they
    /// list the same models with the same fields, including the cases the
    /// two parsers used to disagree on (an override's `thinkingLevelMap` on
    /// a model without one, an override without `compat` on a model with
    /// one, a custom model's `headers`).
    #[tokio::test]
    async fn the_registry_and_the_collection_agree_on_models_json() {
        let dir = tempfile::tempdir().unwrap();
        let (compat_provider, compat_model) = builtin_providers()
            .into_iter()
            .find_map(|provider| {
                let models = (provider.get_models)().ok()?;
                let model = chat_models(&models)
                    .find(|model| model.compat.is_some())?
                    .clone();
                Some((provider.id, model))
            })
            .expect("a built-in model with compat");
        let anthropic = get_builtin_models("anthropic")
            .into_iter()
            .find(|model| model.thinking_level_map.is_none())
            .expect("an anthropic model without a thinking-level map");
        let models_json = BATTERY_MODELS_JSON.replace(
            "\"providers\": {",
            &format!(
                r#""providers": {{
                    "anthropic": {{
                        "modelOverrides": {{ "{anthropic}": {{ "name": "Renamed", "maxTokens": 1234,
                            "thinkingLevelMap": {{ "xhigh": "xhigh" }} }} }},
                        "models": [ {{ "id": "anthropic-extra", "headers": {{ "X-Extra": "1" }} }} ]
                    }},
                    "{compat_provider}": {{
                        "baseUrl": "http://127.0.0.1:9/v1",
                        "modelOverrides": {{ "{compat}": {{ "contextWindow": 4321 }} }}
                    }},"#,
                anthropic = anthropic.id,
                compat = compat_model.id,
            ),
        );
        let models = battery_models(dir.path(), &models_json);
        let auth = crate::auth::AuthStorage::in_memory_without_env(
            &crate::auth::AuthStorageData::default(),
            Arc::new(crate::auth::NoOAuth),
        );
        let registry = ModelRegistry::create(auth, dir.path().join("models.json"));
        assert_eq!(registry.diagnostics(), [] as [String; 0]);

        for provider in ["anthropic", compat_provider.as_str(), "battery"] {
            let mut listed: Vec<eukhe_types::ai::Model> = registry
                .get_all()
                .filter(|model| model.provider == provider)
                .cloned()
                .collect();
            for model in &mut listed {
                // The flag is the registry's own (pi-ai has no slot) and
                // the collection folds an addressed map into `reasoning`.
                model.max_tokens_explicit = false;
                model.reasoning |= model
                    .thinking_level_map
                    .as_ref()
                    .is_some_and(|map| map.values().any(Option::is_some));
            }
            let served = legacy_models(&models.get_models(Some(provider))).unwrap();
            let key = |model: &eukhe_types::ai::Model| model.id.clone();
            listed.sort_by_key(key);
            let mut served = served;
            served.sort_by_key(key);
            assert_eq!(listed, served, "provider {provider}");
        }

        let renamed = registry
            .get_all()
            .find(|model| model.id == anthropic.id)
            .unwrap();
        assert_eq!(
            (renamed.name.as_str(), renamed.max_tokens),
            ("Renamed", 1234)
        );
        assert!(renamed.max_tokens_explicit);
        assert!(renamed.thinking_level_map.is_some());
        let compat = registry
            .get_all()
            .find(|model| model.id == compat_model.id && model.provider == compat_provider)
            .unwrap();
        assert!(
            compat.compat.is_some(),
            "an override without compat keeps it"
        );
        assert_eq!(compat.context_window, 4321);
        let extra = models.get_model("anthropic", "anthropic-extra").unwrap();
        assert_eq!(extra.api, anthropic.api);
        assert_eq!(extra.base_url, anthropic.base_url);

        // The configured apiKey authenticates the custom provider in both.
        assert!(registry
            .get_available()
            .iter()
            .any(|model| model.provider == "battery"));
        let available = models
            .get_available(Some("battery"), AuthOperationOptions::default())
            .await
            .unwrap();
        assert_eq!(available.len(), 2);
    }

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

    pub(super) fn offline_models(agent_dir: &Path) -> SessionModels {
        build_models(agent_dir, Some(Arc::new(EmptyAuthContext)))
    }

    fn battery_models(agent_dir: &Path, models_json: &str) -> Models {
        std::fs::write(agent_dir.join("models.json"), models_json).unwrap();
        let loaded = offline_models(agent_dir);
        assert_eq!(loaded.diagnostics, Vec::<String>::new());
        loaded.models
    }

    pub(super) fn settings(value: Value) -> SettingsManager {
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
            substituted: None,
        }
    }

    fn substitution(provider: &str, model_id: &str, reason: DefaultMiss) -> Substitution {
        Substitution {
            wanted: ModelRef {
                provider: provider.to_owned(),
                model_id: model_id.to_owned(),
            },
            reason,
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
        let models = battery_models(dir.path(), &models_json);

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

    /// eukhe's thinking capability rule (#2858): a model whose map
    /// addresses a level can think even with `reasoning: false`, for
    /// models.json models and built-in catalog models alike; an all-null
    /// map claims nothing.
    #[test]
    fn a_map_addressed_level_makes_a_model_thinking_capable() {
        let dir = tempfile::tempdir().unwrap();
        let models = battery_models(
            dir.path(),
            r#"{ "providers": { "battery": {
                "baseUrl": "http://127.0.0.1:9/v1",
                "api": "openai-completions",
                "apiKey": "TEST_KEY",
                "models": [
                    { "id": "map-model", "reasoning": false,
                      "thinkingLevelMap": { "off": null, "xhigh": "xhigh" } },
                    { "id": "null-map", "thinkingLevelMap": { "off": null } },
                ]
            } } }"#,
        );
        let levels = |provider: &str, id: &str| {
            eukhe_ai::models::get_supported_thinking_levels(
                &models.get_model(provider, id).unwrap(),
            )
        };
        assert_eq!(
            levels("battery", "map-model"),
            [
                ModelThinkingLevel::Minimal,
                ModelThinkingLevel::Low,
                ModelThinkingLevel::Medium,
                ModelThinkingLevel::High,
                ModelThinkingLevel::Xhigh,
            ]
        );
        assert_eq!(levels("battery", "null-map"), [ModelThinkingLevel::Off]);
        assert!(
            models
                .get_model("openai", "gpt-5.3-chat-latest")
                .unwrap()
                .reasoning
        );
    }

    /// The faux verification seam: `models.json` composes over the scripted
    /// provider, so a models.json faux-api model is listed next to the
    /// scripted model.
    #[tokio::test]
    async fn models_json_composes_over_a_faux_script_collection() {
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(
            dir.path().join("models.json"),
            r#"{ "providers": { "faux": { "api": "faux", "baseUrl": "http://localhost:0",
                "apiKey": "sk-faux",
                "models": [ { "id": "plain-model", "api": "faux", "baseUrl": "http://localhost:0" } ]
            } } }"#,
        )
        .unwrap();
        let script = eukhe_ai::providers::faux_script::parse_faux_script_value(
            &json!({ "responses": ["scripted"] }),
        )
        .unwrap();
        let (models, provider) =
            eukhe_ai::providers::faux_script::create_faux_script_models(script);
        assert_eq!(
            compose_models_json(&models, dir.path()),
            Vec::<String>::new()
        );
        let mut ids: Vec<String> = models
            .get_models(Some("faux"))
            .into_iter()
            .map(|model| model.id)
            .collect();
        let mut expected = vec![provider.get_model().id, "plain-model".to_owned()];
        ids.sort();
        expected.sort();
        assert_eq!(ids, expected);
    }

    /// Upstream #755 (configured max tokens clamped to a 32000 default
    /// ceiling): the durable path has no such ceiling. A models.json
    /// `maxTokens` reaches the provider request unchanged, only clamped to
    /// the context window's room.
    #[test]
    fn a_models_json_max_tokens_reaches_the_request_unchanged() {
        let dir = tempfile::tempdir().unwrap();
        let models = battery_models(
            dir.path(),
            r#"{ "providers": { "glm-h200": {
                "baseUrl": "http://127.0.0.1:9/v1",
                "api": "openai-completions",
                "apiKey": "TEST_KEY",
                "models": [ { "id": "glm-5.2", "reasoning": true,
                              "contextWindow": 393216, "maxTokens": 131072 } ]
            } } }"#,
        );
        let model = models.get_model("glm-h200", "glm-5.2").unwrap();
        assert_eq!(model.max_tokens, 131_072);
        let context = eukhe_types::pi_ai::TranscriptContext::from_normalized_messages(Vec::new());
        let base = eukhe_ai::api::simple_options::build_base_options(&model, &context, None, None);
        assert_eq!(base.max_tokens, Some(131_072));
    }

    /// Regression (audit M1): a models.json with one bad provider entry
    /// failed the session collection as a whole, while the registry kept
    /// the built-ins only and stored an error most callers ignored. Now
    /// both views keep the good provider, drop the bad one, and report the
    /// same diagnostic naming `providers.<id>`.
    #[tokio::test]
    async fn a_bad_provider_entry_drops_only_that_provider_in_both_views() {
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(
            dir.path().join("models.json"),
            BATTERY_MODELS_JSON.replace(
                "\"providers\": {",
                r#""providers": { "custom": { "models": [{ "id": "x" }] },"#,
            ),
        )
        .unwrap();
        let session = offline_models(dir.path());
        let auth = crate::auth::AuthStorage::in_memory_without_env(
            &crate::auth::AuthStorageData::default(),
            Arc::new(crate::auth::NoOAuth),
        );
        let registry = ModelRegistry::create(auth, dir.path().join("models.json"));
        let diagnostic =
            "models.json providers.custom: \"baseUrl\" is required when defining custom models.";
        assert_eq!(
            (registry.diagnostics().to_vec(), session.diagnostics.clone()),
            (vec![diagnostic.to_owned()], vec![diagnostic.to_owned()])
        );
        let custom = |provider: &str| -> (Vec<String>, Vec<String>) {
            let mut listed: Vec<String> = registry
                .get_all()
                .filter(|model| model.provider == provider)
                .map(|model| model.id.clone())
                .collect();
            let mut served: Vec<String> = session
                .models
                .get_models(Some(provider))
                .into_iter()
                .map(|model| model.id)
                .collect();
            listed.sort();
            served.sort();
            (listed, served)
        };
        let battery = vec!["mock-plain".to_owned(), "mock-reason".to_owned()];
        assert_eq!(custom("battery"), (battery.clone(), battery));
        assert_eq!(custom("custom"), (Vec::new(), Vec::new()));
    }

    /// Regression (audit H4): a saved default missing from the catalog
    /// was replaced by the next startup default with only a log line. Now
    /// the resolution carries the substitution and its reason.
    #[tokio::test]
    async fn a_saved_default_missing_from_the_catalog_is_a_substitution() {
        let dir = tempfile::tempdir().unwrap();
        let models = battery_models(dir.path(), BATTERY_MODELS_JSON);
        let gone = settings(json!({
            "defaultProvider": "battery", "defaultModel": "gone",
            "enabledModels": ["battery/mock-plain"]
        }));
        assert_eq!(
            resolve(&models, &gone, None, None).await.unwrap(),
            Some(ResolvedModel {
                substituted: Some(substitution("battery", "gone", DefaultMiss::NotInCatalog)),
                ..resolved("battery", "mock-plain", ModelThinkingLevel::Off)
            })
        );
        // A saved default outside the enabledModels scope.
        let outside = settings(json!({
            "defaultProvider": "battery", "defaultModel": "mock-reason",
            "enabledModels": ["battery/mock-plain"]
        }));
        assert_eq!(
            resolve(&models, &outside, None, None).await.unwrap(),
            Some(ResolvedModel {
                substituted: Some(substitution(
                    "battery",
                    "mock-reason",
                    DefaultMiss::NotInScope
                )),
                ..resolved("battery", "mock-plain", ModelThinkingLevel::Off)
            })
        );
    }

    /// Regression (audit H4): a saved default whose provider has no
    /// credentials moved the session to another provider in silence. Now
    /// it is the typed error, and no other provider runs.
    #[tokio::test]
    async fn a_saved_default_without_credentials_never_moves_provider() {
        let dir = tempfile::tempdir().unwrap();
        let models = battery_models(dir.path(), BATTERY_MODELS_JSON);
        let anthropic = get_builtin_models("anthropic").remove(0);
        let unkeyed = settings(json!({
            "defaultProvider": "anthropic", "defaultModel": anthropic.id
        }));
        let wanted = substitution("anthropic", &anthropic.id, DefaultMiss::NoCredentials);
        match resolve(&models, &unkeyed, None, None).await {
            Err(ModelsError::DefaultUnusable(refused)) => assert_eq!(refused, wanted),
            other => panic!("expected the typed error, got {other:?}"),
        }
        let opened = resolve_open_model(&models, &unkeyed, None, None, &BACKGROUND_CONTEXT)
            .await
            .unwrap();
        assert_eq!(
            (opened.notice(), opened),
            (
                Some(format!(
                    "The saved default model anthropic/{} did not run: its provider has no credentials. eukhe does not move to another provider. Sign in with /login, set the provider's API key, or change defaultProvider/defaultModel. The session has no model.",
                    anthropic.id
                )),
                OpenModel {
                    resolved: None,
                    refused: Some(wanted),
                }
            )
        );
    }

    #[tokio::test]
    async fn settings_default_model_and_thinking_resolve_clamped() {
        let dir = tempfile::tempdir().unwrap();
        let models = battery_models(dir.path(), BATTERY_MODELS_JSON);
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
        let models = battery_models(dir.path(), BATTERY_MODELS_JSON);
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
        let models = battery_models(dir.path(), BATTERY_MODELS_JSON);
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
        let models = offline_models(dir.path()).models;
        assert!(!models.get_models(None).is_empty());
        assert_eq!(
            resolve(&models, &settings(json!({})), None, None)
                .await
                .unwrap(),
            None
        );
    }
}
