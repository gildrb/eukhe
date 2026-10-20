//! `ModelRegistry`: the built-in catalog (the union of the bundled snapshot
//! and the compiled catalog) with the user's models.json composed over it, and request auth
//! per provider/model. Port of model-registry.ts. Fully local: building the
//! catalog never touches the network. models.json parsing, composition, and
//! its configured auth are `super::custom`'s, the same code the session's
//! model collection (`durable::models`) runs; this is the registry's view.

use std::borrow::Cow;
use std::collections::{BTreeMap, HashMap};
use std::path::Path;
use std::sync::LazyLock;

use eukhe_models::ModelCatalog;
use eukhe_types::ai::{CompatKind, Model, ModelCompat, ModelThinkingLevel, OpenAiResponsesCompat};

use crate::auth::manager::AuthStorage;
use crate::auth::types::AuthCredential;

use super::custom::{in_file, ModelsConfig, ProviderConfig};
use super::prime_inference::{is_private_prime_inference_model, private_prime_inference_models};

/// The process-wide built-in catalog: the union of the packaged bundled
/// snapshot and the compiled catalog. The install's assets never change
/// while the process runs, so one resolution serves every registry.
static BUILT_IN_CATALOG: LazyLock<ModelCatalog> = LazyLock::new(ModelCatalog::new);

/// The result of `getApiKeyAndHeaders`.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct ResolvedRequestAuth {
    pub ok: bool,
    pub api_key: Option<String>,
    /// Ordered (`BTreeMap`): providers iterate this map when composing
    /// request headers, and unordered iteration would order them randomly.
    pub headers: Option<BTreeMap<String, String>>,
    pub error: Option<String>,
}

/// Why a `set_model` selection failed to resolve (the daemon's
/// `set_model` classification): the provider is not signed in (the
/// client offers the sign-in flow and retries) or the model is genuinely
/// not in the catalog (the TS refusal).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SetModelSelectionError {
    /// The model exists in the catalog, but its provider has no
    /// credential and none is stale: sign in, then retry the switch.
    ProviderUnauthenticated { provider: String },
    /// No such model in the catalog (the TS `set_model` message).
    NotFound { provider: String, model_id: String },
}

impl SetModelSelectionError {
    /// The refused provider of the sign-in variant (the daemon's typed
    /// `errorInfo` payload); `None` on the not-found refusal.
    #[must_use]
    pub fn unauthenticated_provider(&self) -> Option<&str> {
        match self {
            SetModelSelectionError::ProviderUnauthenticated { provider } => Some(provider),
            SetModelSelectionError::NotFound { .. } => None,
        }
    }
}

impl std::fmt::Display for SetModelSelectionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SetModelSelectionError::ProviderUnauthenticated { provider } => write!(
                f,
                "Provider \"{provider}\" is not signed in. Sign in to the provider (the TUI's /login command), then set the model again."
            ),
            SetModelSelectionError::NotFound { provider, model_id } => {
                write!(f, "Model not found: {provider}/{model_id}")
            }
        }
    }
}

impl std::error::Error for SetModelSelectionError {}

/// Composed model catalog with auth-aware availability.
pub struct ModelRegistry {
    pub auth: AuthStorage,
    /// Built-in models stay borrowed from the process-wide catalog unless
    /// models.json or a stored subscription rewrites them.
    models: Vec<Cow<'static, Model>>,
    /// The models.json document (empty when absent or failing to load).
    config: ModelsConfig,
    load_error: Option<String>,
}

/// TS `getXaiSubscriptionModel`: the xAI provider's models switch onto
/// the openai-responses API under a stored subscription, with the
/// `supportsLongCacheRetention: false` compat. A model without a
/// thinking map gets the quirks rulebook's ladder of its family
/// (`thinking_ladder`), else a map that sets every level to null (the
/// reasoning output stays; unverified effort controls never send).
fn xai_subscription_model(model: &Model) -> Model {
    let mut adapted = model.clone();
    adapted.api = "openai-responses".to_string();
    adapted.base_url = "https://api.x.ai/v1".to_string();
    // TS `getXaiSubscriptionModel` fills only an absent map: a model
    // that already declares its levels keeps them.
    if adapted.thinking_level_map.is_none() {
        let ladder = eukhe_ai::models::registry_rule_ladder(&adapted).unwrap_or_else(|| {
            [
                ModelThinkingLevel::Off,
                ModelThinkingLevel::Minimal,
                ModelThinkingLevel::Low,
                ModelThinkingLevel::Medium,
                ModelThinkingLevel::High,
                ModelThinkingLevel::Xhigh,
                ModelThinkingLevel::Max,
            ]
            .into_iter()
            .map(|level| (level, None))
            .collect()
        });
        adapted.thinking_level_map = Some(ladder);
    }
    adapted.compat = Some(ModelCompat::from_kind(CompatKind::OpenAiResponses(
        OpenAiResponsesCompat {
            send_session_id_header: None,
            supports_long_cache_retention: Some(false),
        },
    )));
    adapted
}

impl ModelRegistry {
    pub fn create(auth: AuthStorage, models_json_path: impl AsRef<Path>) -> Self {
        let (config, models, load_error) = match compose(models_json_path.as_ref()) {
            Ok((config, models)) => (config, models, None),
            // Keep built-ins only; the error names the file.
            Err(error) => (ModelsConfig::default(), built_in_models(), Some(error)),
        };
        Self::with_models(auth, config, models, load_error)
    }

    #[cfg(test)]
    pub(crate) fn in_memory(auth: AuthStorage) -> Self {
        Self::with_models(auth, ModelsConfig::default(), built_in_models(), None)
    }

    fn with_models(
        auth: AuthStorage,
        config: ModelsConfig,
        models: Vec<Cow<'static, Model>>,
        load_error: Option<String>,
    ) -> Self {
        let mut registry = Self {
            auth,
            models,
            config,
            load_error,
        };
        registry.apply_subscription_model_adaptations();
        registry
    }

    /// Error from loading models.json, if any.
    pub fn get_error(&self) -> Option<&str> {
        self.load_error.as_deref()
    }

    /// Built-in + custom models (auth not filtered).
    pub fn get_all(&self) -> impl ExactSizeIterator<Item = &Model> + Clone {
        self.models.iter().map(AsRef::as_ref)
    }

    /// Models whose provider has configured auth, with private Prime
    /// Inference models gated out unless models.json declares them (TS
    /// `getAvailable`). The per-model
    /// auth probe is answered once per provider (the port of TS #2479's
    /// `getAvailable` memo): the catalog walks hundreds of models over a
    /// few dozen providers and each probe rebuilds the provider's
    /// auth-source candidates, while a same-registry probe is stable by
    /// construction (`&self`, no mutation between models).
    pub fn get_available(&self) -> Vec<&Model> {
        let mut auth_by_provider: HashMap<&str, bool> = HashMap::new();
        self.get_all()
            .filter(|model| {
                (!is_private_prime_inference_model(model)
                    || self.is_authorized_private_model(model))
                    && *auth_by_provider
                        .entry(model.provider.as_str())
                        .or_insert_with(|| self.has_configured_auth(model))
            })
            .collect()
    }

    /// Models `rlm.find_models` may search: auth-configured, and not on a
    /// stale or expired provider credential. The per-model status probe
    /// is answered once per provider (the port of TS #2479's
    /// `_authenticatedRlmModels` memo — same stability argument as
    /// [`Self::get_available`]).
    pub fn get_rlm_searchable_models(&self) -> Vec<&Model> {
        let mut status_by_provider: HashMap<&str, bool> = HashMap::new();
        self.get_available()
            .into_iter()
            .filter(|model| {
                *status_by_provider
                    .entry(model.provider.as_str())
                    .or_insert_with(|| {
                        let status = self.auth.get_auth_status(&model.provider);
                        status.source != Some(crate::auth::types::AuthSource::Stale)
                            && status.label.as_deref() != Some("expired")
                    })
            })
            .collect()
    }

    pub fn has_configured_auth(&self, model: &Model) -> bool {
        self.auth.has_auth(&model.provider)
            || self
                .config
                .providers
                .get(&model.provider)
                .is_some_and(ProviderConfig::has_request_auth)
    }

    /// The provider's auth status without credential values (TS
    /// `getProviderAuthStatus`): callers that classify unauthenticated
    /// vs stale providers read it instead of probing for keys.
    pub fn get_provider_auth_status(&self, provider: &str) -> crate::auth::types::AuthStatus {
        self.auth.get_auth_status(provider)
    }

    /// TS `loadModels`'s `modifyModels` loop plus
    /// `getModelForCurrentAuth`'s xAI subscription switch, applied at
    /// load: a stored Copilot credential rewrites its models' base URL
    /// through the credential (the token's proxy endpoint, else the
    /// enterprise domain, else the catalog default), and a stored xAI
    /// subscription switches the provider's models onto the
    /// openai-responses API with the TS thinking maps. Callers build a
    /// fresh registry after every credential change, so the adaptations
    /// track the store exactly like TS's per-read switch.
    fn apply_subscription_model_adaptations(&mut self) {
        // TS `githubCopilotOAuthProvider.modifyModels`.
        let copilot_credential = self
            .auth
            .get_all()
            .credential(crate::auth::GITHUB_COPILOT_PROVIDER_ID);
        if let Some(AuthCredential::Oauth {
            access,
            enterprise_url,
            ..
        }) = copilot_credential
        {
            let base_url = eukhe_ai::auth::oauth::get_github_copilot_base_url(
                Some(&access),
                enterprise_url.as_deref(),
            );
            for model in &mut self.models {
                if model.provider == crate::auth::GITHUB_COPILOT_PROVIDER_ID {
                    model.to_mut().base_url.clone_from(&base_url);
                }
            }
        }
        // TS `isUsingXaiSubscription`: the stored credential is OAuth
        // and the store is the winning source (a stale credential does
        // not serve the subscription API).
        let xai_stored = matches!(
            self.auth.get_all().credential(crate::auth::XAI_PROVIDER_ID),
            Some(AuthCredential::Oauth { .. })
        ) && self
            .auth
            .get_auth_status(crate::auth::XAI_PROVIDER_ID)
            .source
            == Some(crate::auth::types::AuthSource::Stored);
        if xai_stored {
            for model in &mut self.models {
                if model.provider == crate::auth::XAI_PROVIDER_ID {
                    *model = Cow::Owned(xai_subscription_model(model));
                }
            }
        }
    }

    /// Private Prime Inference models are usable only when models.json
    /// declares them.
    fn is_authorized_private_model(&self, model: &Model) -> bool {
        self.config
            .providers
            .get(&model.provider)
            .is_some_and(|provider| provider.definition(&model.id).is_some())
    }

    /// Resolve request auth for `model` (TS `getApiKeyAndHeaders`): the
    /// stored credential (an expired OAuth token refreshes), else the
    /// models.json `apiKey`. Headers merge in precedence order: auth
    /// storage, the models.json provider headers, its model headers, the
    /// `authHeader` bearer, then the model's own headers. Blocking: reads
    /// auth storage and may refresh a token over the network.
    pub fn get_api_key_and_headers(&mut self, model: &Model) -> ResolvedRequestAuth {
        let failure = |error: String| ResolvedRequestAuth {
            ok: false,
            error: Some(error),
            ..ResolvedRequestAuth::default()
        };
        let stored = self
            .auth
            .get_api_key_with_source_token(&model.provider, false);
        let config = self.config.providers.get(&model.provider);
        let api_key = stored
            .api_key
            .or_else(|| config.and_then(ProviderConfig::configured_api_key));
        // An expired OAuth credential whose refresh failed resolves no key:
        // the request fails with the refresh's reason and the TS login hint
        // (`LOGIN_RECOVERY_MESSAGE`), never the provider's bare "No API key".
        if let (None, Some(refresh_error)) = (&api_key, stored.refresh_error) {
            return failure(format!(
                "{refresh_error}\n\nRun /login to update credentials."
            ));
        }
        let mut headers: BTreeMap<String, String> = self
            .auth
            .get_provider_headers(&model.provider)
            .into_iter()
            .flatten()
            .collect();
        if let Some(config) = config {
            let configured = config.headers.iter().chain(config.model_headers(&model.id));
            headers.extend(configured.flatten().map(|(k, v)| (k.clone(), v.clone())));
            match config.bearer_header(&model.provider, api_key.as_deref()) {
                Ok(bearer) => headers.extend(bearer),
                Err(error) => return failure(error),
            }
        }
        if let Some(model_headers) = &model.headers {
            headers.extend(model_headers.clone());
        }
        ResolvedRequestAuth {
            ok: true,
            api_key,
            headers: (!headers.is_empty()).then_some(headers),
            error: None,
        }
    }
}

/// The built-in catalog (bundled snapshot and compiled catalog), borrowed,
/// then the bundled private Prime Inference table (listed, but gated out
/// of `get_available` unless models.json declares the id).
fn built_in_models() -> Vec<Cow<'static, Model>> {
    BUILT_IN_CATALOG
        .models()
        .iter()
        .map(Cow::Borrowed)
        .chain(private_prime_inference_models().into_iter().map(Cow::Owned))
        .collect()
}

/// `models_json` composed over [`built_in_models`] (TS `loadModels`): the
/// provider and model overrides rewrite the catalog's built-in models, then
/// the custom models land, winning on provider+id conflicts.
fn compose(models_json: &Path) -> Result<(ModelsConfig, Vec<Cow<'static, Model>>), String> {
    let compiled = eukhe_models::transports::compiled_models();
    let config = ModelsConfig::load(models_json, &|provider| {
        compiled.iter().any(|model| model.provider == provider)
    })?;
    let mut models = built_in_models();
    let built_in_count = BUILT_IN_CATALOG.models().len();
    for slot in &mut models[..built_in_count] {
        let Some(provider) =
            (config.providers.get(&slot.provider)).filter(|provider| provider.rewrites(&slot.id))
        else {
            continue;
        };
        let rewritten = provider
            .rewrite_built_in(slot.as_ref())
            .and_then(|model| registry_view(&model, provider))
            .map_err(|error| in_file(error, models_json))?;
        *slot = Cow::Owned(rewritten);
    }
    for (provider_id, provider) in &config.providers {
        let defaults = (compiled.iter())
            .find(|model| model.provider == *provider_id)
            .map(|model| (model.api.as_str(), model.base_url.as_str()));
        let custom = provider
            .custom_models(provider_id, defaults)
            .map_err(|error| in_file(error, models_json))?;
        for model in custom {
            let model = registry_view(&model, provider).map_err(|e| in_file(e, models_json))?;
            let existing = (models.iter())
                .position(|entry| entry.provider == model.provider && entry.id == model.id);
            match existing {
                Some(index) => models[index] = Cow::Owned(model),
                None => models.push(Cow::Owned(model)),
            }
        }
    }
    Ok((config, models))
}

/// The registry form of a composed pi-ai model; a `maxTokens` models.json
/// configures is explicit (it bypasses the default output ceiling).
fn registry_view(
    model: &eukhe_types::pi_ai::Model,
    provider: &ProviderConfig,
) -> Result<Model, String> {
    let mut view =
        eukhe_models::pi_ai_model::registry_model(model).map_err(|error| error.to_string())?;
    view.max_tokens_explicit = provider.configures_max_tokens(&model.id);
    Ok(view)
}

// The unit battery lives in the child module (registry::tests); its
// use-super glob resolves through this facade's bindings and re-exports.
#[cfg(test)]
mod tests;
