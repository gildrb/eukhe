//! `ModelRegistry`: composes built-in (bundled snapshot | compiled fallback)
//! and custom (models.json) catalogs; resolves request auth per
//! provider/model. Port of model-registry.ts. Fully local: building the
//! catalog never touches the network.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::LazyLock;

use eukhe_models::ModelCatalog;
use eukhe_types::ai::{
    CompatKind, Model, ModelCompat, ModelThinkingLevel, OpenAiResponsesCompat, ThinkingLevelMap,
};

use crate::auth::manager::AuthStorage;
use crate::auth::types::AuthCredential;

use super::custom::{apply_model_override, load_custom_models, merge_compat, CustomModelsResult};
use super::prime_inference::{is_private_prime_inference_model, private_prime_inference_models};

/// The process-wide built-in catalog: the packaged bundled snapshot, else
/// the compiled fallback. The install's assets never change while the
/// process runs, so one resolution serves every registry.
static BUILT_IN_CATALOG: LazyLock<ModelCatalog> = LazyLock::new(ModelCatalog::new);

/// Request-auth bits a provider can configure in models.json.
#[derive(Debug, Clone, Default)]
pub struct ProviderRequestConfig {
    pub api_key: Option<String>,
    /// Ordered (`BTreeMap`): these headers merge into request-header maps
    /// that providers iterate deterministically.
    pub headers: Option<BTreeMap<String, String>>,
    pub auth_header: Option<bool>,
}

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
    models_json_path: Option<PathBuf>,
    models: Vec<Model>,
    load_error: Option<String>,
    provider_request_configs: HashMap<String, ProviderRequestConfig>,
    model_request_headers: HashMap<String, BTreeMap<String, String>>,
    /// Private Prime Inference ids the user's models.json declares: the only
    /// private models `get_available` serves.
    explicit_private_ids: HashSet<String>,
}

/// TS `getXaiSubscriptionModel`: the xAI provider's models switch onto
/// the openai-responses API under a stored subscription — the TS
/// thinking map per model id (the explicit maps for the models the TS
/// flow knows, an all-null map otherwise) and the
/// `supportsLongCacheRetention: false` compat.
fn xai_subscription_model(model: &Model) -> Model {
    let mut adapted = model.clone();
    adapted.api = "openai-responses".to_string();
    adapted.base_url = "https://api.x.ai/v1".to_string();
    // TS `getXaiSubscriptionModel` fills only an absent map: a model
    // that already declares its levels keeps them.
    if adapted.thinking_level_map.is_none() {
        adapted.thinking_level_map = Some(xai_subscription_thinking_map(&model.id));
    }
    adapted.compat = Some(ModelCompat::from_kind(CompatKind::OpenAiResponses(
        OpenAiResponsesCompat {
            send_session_id_header: None,
            supports_long_cache_retention: Some(false),
        },
    )));
    adapted
}

/// The TS flow's thinking maps (`getXaiSubscriptionModel`'s switch): an
/// explicit map for the grok models the TS flow names, and the
/// all-levels-null default for every other xAI model (the reasoning
/// output stays; unverified effort controls never send).
fn xai_subscription_thinking_map(model_id: &str) -> ThinkingLevelMap {
    // The map's value is the TS table's entry: `None` for the null
    // mapping (unsupported), the wire string for a named level; an
    // absent level keeps its default support.
    let null = || None;
    let value = |text: &str| Some(text.to_string());
    let mut map = ThinkingLevelMap::new();
    match model_id {
        "grok-4.3" => {
            map.insert(ModelThinkingLevel::Off, value("none"));
            map.insert(ModelThinkingLevel::Minimal, null());
        }
        "grok-4.5" => {
            map.insert(ModelThinkingLevel::Off, null());
            map.insert(ModelThinkingLevel::Minimal, null());
        }
        "grok-4.6" | "grok-4.7" => {
            map.insert(ModelThinkingLevel::Off, null());
            map.insert(ModelThinkingLevel::Minimal, null());
            map.insert(ModelThinkingLevel::Xhigh, value("xhigh"));
        }
        _ => {
            for level in [
                ModelThinkingLevel::Off,
                ModelThinkingLevel::Minimal,
                ModelThinkingLevel::Low,
                ModelThinkingLevel::Medium,
                ModelThinkingLevel::High,
                ModelThinkingLevel::Xhigh,
                ModelThinkingLevel::Max,
            ] {
                map.insert(level, null());
            }
        }
    }
    map
}

impl ModelRegistry {
    pub fn create(auth: AuthStorage, models_json_path: impl Into<PathBuf>) -> Self {
        Self::new(auth, Some(models_json_path.into()))
    }

    pub fn in_memory(auth: AuthStorage) -> Self {
        Self::new(auth, None)
    }

    fn new(auth: AuthStorage, models_json_path: Option<PathBuf>) -> Self {
        let mut registry = Self {
            auth,
            models_json_path,
            models: Vec::new(),
            load_error: None,
            provider_request_configs: HashMap::new(),
            model_request_headers: HashMap::new(),
            explicit_private_ids: HashSet::new(),
        };
        registry.load_models();
        registry
    }

    /// Error from loading models.json, if any.
    pub fn get_error(&self) -> Option<&str> {
        self.load_error.as_deref()
    }

    /// Built-in + custom models (auth not filtered).
    pub fn get_all(&self) -> &[Model] {
        &self.models
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
        self.models
            .iter()
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
            || self.has_configured_provider_request_auth(&model.provider)
    }

    /// The provider's auth status without credential values (TS
    /// `getProviderAuthStatus`): callers that classify unauthenticated
    /// vs stale providers (the daemon `set_model` resolution) read it
    /// instead of probing for keys.
    pub fn get_provider_auth_status(&self, provider: &str) -> crate::auth::types::AuthStatus {
        self.auth.get_auth_status(provider)
    }

    /// `set_model`'s model resolution (the TS daemon's available-list
    /// lookup with its stale fallback and the sign-in classification):
    /// an available model resolves directly; a catalog model whose
    /// provider has no credential at all (and none marked stale) is the
    /// typed sign-in refusal — the client offers the provider's login
    /// and retries the switch, instead of the old dead-end "Model not
    /// found" — while everything else (an unauthorized private Prime
    /// Inference model, an unknown id) keeps the TS refusal.
    ///
    /// Stale-auth providers keep the switch exactly like the TS daemon
    /// (`session.modelRegistry.find`'s full-catalog fallback: the lookup
    /// never mutates stale state, `session.setModel` owns the clear).
    ///
    /// # Errors
    ///
    /// Returns [`SetModelSelectionError::ProviderUnauthenticated`] when the
    /// model exists but its provider has no credential (and none is
    /// stale), or [`SetModelSelectionError::NotFound`] when no catalog
    /// model matches.
    pub fn resolve_set_model_selection(
        &self,
        provider: &str,
        model_id: &str,
    ) -> Result<&Model, SetModelSelectionError> {
        let matches = |model: &Model| model.provider == provider && model.id == model_id;
        if let Some(model) = self
            .get_available()
            .into_iter()
            .find(|model| matches(model))
        {
            return Ok(model);
        }
        // The catalog lists every provider's models, so a model can exist
        // while its provider is not signed in — the picker's discovery
        // path. The stale fallback resolves from the full catalog (TS
        // `find`); a provider without any credential is the sign-in
        // refusal; a signed-in provider's exclusion is the unauthorized
        // private Prime Inference model (the only `get_available` gate
        // besides auth), which keeps the TS "Model not found" refusal —
        // never a switch to a model the account is not entitled to.
        let Some(model) = self.get_all().iter().find(|model| matches(model)) else {
            return Err(SetModelSelectionError::NotFound {
                provider: provider.to_string(),
                model_id: model_id.to_string(),
            });
        };
        if self.get_provider_auth_status(provider).source
            == Some(crate::auth::types::AuthSource::Stale)
        {
            return Ok(model);
        }
        if !self.has_configured_auth(model) {
            return Err(SetModelSelectionError::ProviderUnauthenticated {
                provider: provider.to_string(),
            });
        }
        Err(SetModelSelectionError::NotFound {
            provider: provider.to_string(),
            model_id: model_id.to_string(),
        })
    }

    fn has_configured_provider_request_auth(&self, provider: &str) -> bool {
        let Some(config) = self.provider_request_configs.get(provider) else {
            return false;
        };
        if config.headers.is_some() || config.auth_header.is_some() {
            return true;
        }
        config.api_key.as_deref().is_some_and(|key| {
            crate::auth::resolve_config_value::resolve_config_value(key).is_some()
        })
    }

    /// Reload built-in + custom models and provider request configs from disk.
    pub fn refresh(&mut self) {
        self.provider_request_configs.clear();
        self.model_request_headers.clear();
        self.explicit_private_ids.clear();
        self.load_error = None;
        self.auth.reload();
        self.load_models();
    }

    fn load_models(&mut self) {
        let path = self.models_json_path.clone();
        let result = match &path {
            Some(path) => self.load_custom_models_file(path),
            None => CustomModelsResult::default(),
        };
        if let Some(error) = &result.error {
            self.load_error = Some(error.clone());
        }
        self.explicit_private_ids = result
            .models
            .iter()
            .filter(|model| is_private_prime_inference_model(model))
            .map(|model| model.id.clone())
            .collect();

        // The bundled private-route table: listed, but gated out of
        // `get_available` unless models.json declares the id.
        let mut built_in = Self::load_built_in_models(&result);
        built_in.extend(private_prime_inference_models());
        self.models = Self::merge_custom_models(built_in, result.models);
        self.apply_subscription_model_adaptations();
    }

    /// TS `loadModels`'s `modifyModels` loop plus
    /// `getModelForCurrentAuth`'s xAI subscription switch, applied at
    /// load: a stored Copilot credential rewrites its models' base URL
    /// through the credential (the token's proxy endpoint, else the
    /// enterprise domain, else the catalog default), and a stored xAI
    /// subscription switches the provider's models onto the
    /// openai-responses API with the TS thinking maps. The registry
    /// reloads after every credential change, so the adaptations track
    /// the store exactly like TS's per-read switch.
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
                    model.base_url.clone_from(&base_url);
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
                    *model = xai_subscription_model(model);
                }
            }
        }
    }

    fn load_custom_models_file(&mut self, path: &Path) -> CustomModelsResult {
        if !path.exists() {
            return CustomModelsResult::default();
        }
        let Ok(content) = std::fs::read_to_string(path) else {
            return CustomModelsResult {
                error: Some(format!(
                    "Failed to load models.json\n\nFile: {}",
                    path.display()
                )),
                ..Default::default()
            };
        };
        let compiled = eukhe_models::transports::compiled_models();
        let mut result = load_custom_models(
            &content,
            &|provider| compiled.iter().any(|model| model.provider == provider),
            &|provider| {
                compiled
                    .iter()
                    .find(|model| model.provider == provider)
                    .map(|model| (model.api.clone(), model.base_url.clone()))
            },
        );
        // Provider/model request config from the parsed document.
        if result.error.is_none() {
            if let Ok(config) =
                super::custom::parse_models_config(&super::custom::strip_json_comments(&content))
            {
                for (provider, provider_config) in config.providers {
                    if provider_config.api_key.is_some()
                        || provider_config.headers.is_some()
                        || provider_config.auth_header.is_some()
                    {
                        self.provider_request_configs.insert(
                            provider.clone(),
                            ProviderRequestConfig {
                                api_key: provider_config.api_key,
                                headers: provider_config.headers,
                                auth_header: provider_config.auth_header,
                            },
                        );
                    }
                    if let Some(model_overrides) = provider_config.model_overrides {
                        for (model_id, model_override) in model_overrides {
                            self.store_model_headers(
                                &provider,
                                &model_id,
                                model_override.headers.clone(),
                            );
                        }
                    }
                    if let Some(model_defs) = provider_config.models {
                        for model_def in model_defs {
                            self.store_model_headers(
                                &provider,
                                &model_def.id,
                                model_def.headers.clone(),
                            );
                        }
                    }
                }
            }
        }
        if let Some(error) = &result.error {
            // Keep built-ins only; message mirrors the TS load failure format.
            if !error.contains("models.json") {
                result.error = Some(format!("{error}\n\nFile: {}", path.display()));
            }
        }
        result
    }

    fn store_model_headers(
        &mut self,
        provider: &str,
        model_id: &str,
        headers: Option<BTreeMap<String, String>>,
    ) {
        let key = format!("{provider}:{model_id}");
        match headers {
            Some(headers) if !headers.is_empty() => {
                self.model_request_headers.insert(key, headers);
            }
            _ => {
                self.model_request_headers.remove(&key);
            }
        }
    }

    /// Built-ins through the no-cold-start chain (bundled asset | compiled
    /// fallback) with the models.json provider and model overrides applied
    /// — TS `loadBuiltInModels`.
    fn load_built_in_models(custom: &CustomModelsResult) -> Vec<Model> {
        BUILT_IN_CATALOG
            .models()
            .iter()
            .cloned()
            .map(|mut model| {
                if let Some(provider_override) = custom.provider_overrides.get(&model.provider) {
                    if provider_override.base_url.is_some() {
                        model.base_url = provider_override
                            .base_url
                            .clone()
                            .unwrap_or_else(|| model.base_url.clone());
                    }
                    if provider_override.compat.is_some() {
                        model.compat =
                            merge_compat(model.compat.as_ref(), provider_override.compat.clone());
                    }
                }
                if let Some(model_override) = custom
                    .model_overrides
                    .get(&model.provider)
                    .and_then(|overrides| overrides.get(&model.id))
                {
                    model = apply_model_override(&model, model_override);
                }
                model
            })
            .collect()
    }

    /// Custom models win on provider+id conflicts.
    fn merge_custom_models(mut built_in: Vec<Model>, custom: Vec<Model>) -> Vec<Model> {
        for custom_model in custom {
            match built_in.iter().position(|model| {
                model.provider == custom_model.provider && model.id == custom_model.id
            }) {
                Some(index) => built_in[index] = custom_model,
                None => built_in.push(custom_model),
            }
        }
        built_in
    }

    /// Private Prime Inference models are usable only when models.json
    /// declares them.
    fn is_authorized_private_model(&self, model: &Model) -> bool {
        self.explicit_private_ids.contains(&model.id)
    }

    /// Resolve request auth: API key + merged headers for a model.
    pub fn get_api_key_and_headers(
        &mut self,
        model: &Model,
        request_headers: Option<&BTreeMap<String, String>>,
    ) -> ResolvedRequestAuth {
        let stored = self
            .auth
            .get_api_key_with_source_token(&model.provider, false);
        let mut api_key = stored.api_key;
        let provider_config = self.provider_request_configs.get(&model.provider).cloned();
        if api_key.is_none() {
            if let Some(config) = &provider_config {
                if let Some(configured) = &config.api_key {
                    if let Some(resolved) =
                        crate::auth::resolve_config_value::resolve_config_value(configured)
                    {
                        api_key = Some(resolved);
                    }
                }
            }
        }
        // An expired OAuth credential whose refresh failed resolves no key:
        // the request fails with the refresh's reason and the TS login hint
        // (`LOGIN_RECOVERY_MESSAGE`), never the provider's bare "No API key".
        if let (None, Some(refresh_error)) = (&api_key, stored.refresh_error) {
            return ResolvedRequestAuth {
                ok: false,
                error: Some(format!(
                    "{refresh_error}\n\nRun /login to update credentials."
                )),
                ..Default::default()
            };
        }
        let provider_headers = provider_config
            .as_ref()
            .and_then(|config| config.headers.clone());
        let auth_storage_headers = self.auth.get_provider_headers(&model.provider);
        let model_request_key = format!("{}:{}", model.provider, model.id);
        let model_request_headers = self.model_request_headers.get(&model_request_key).cloned();

        let mut headers: BTreeMap<String, String> = BTreeMap::new();
        if let Some(model_headers) = &model.headers {
            headers.extend(model_headers.clone());
        }
        if let Some(auth_storage_headers) = auth_storage_headers {
            headers.extend(auth_storage_headers);
        }
        if let Some(provider_headers) = provider_headers {
            headers.extend(provider_headers);
        }
        if let Some(model_request_headers) = model_request_headers {
            headers.extend(model_request_headers);
        }
        if provider_config
            .as_ref()
            .and_then(|config| config.auth_header)
            .unwrap_or(false)
        {
            let Some(api_key) = &api_key else {
                return ResolvedRequestAuth {
                    ok: false,
                    error: Some(format!("No API key found for \"{}\"", model.provider)),
                    ..Default::default()
                };
            };
            headers.insert("Authorization".to_string(), format!("Bearer {api_key}"));
        }
        if let Some(request_headers) = request_headers {
            headers.extend(request_headers.clone());
        }
        ResolvedRequestAuth {
            ok: true,
            api_key,
            headers: (!headers.is_empty()).then_some(headers),
            error: None,
        }
    }
}

/// Request auth for `model` from `agent_dir`'s auth storage and
/// `models.json` (TS `getApiKeyAndHeaders`, the per-request resolution
/// a session stream runs): the stored credential (an expired OAuth token
/// refreshes), then the models.json provider `apiKey`, with the merged
/// request headers. A `runtime_api_key` rides as the runtime override (TS
/// `setRuntimeApiKey`): it wins without reading or refreshing the stored
/// credential, and the merged headers still ship. Blocking: reads auth
/// storage and may refresh a token over the network.
#[must_use]
pub fn resolve_request_auth(
    agent_dir: &Path,
    runtime_api_key: Option<&str>,
    model: &Model,
) -> ResolvedRequestAuth {
    let mut auth = AuthStorage::create(agent_dir);
    if let Some(api_key) = runtime_api_key {
        auth.set_runtime_api_key(&model.provider, api_key.to_string());
    }
    ModelRegistry::create(auth, agent_dir.join("models.json"))
        .get_api_key_and_headers(model, model.headers.as_ref())
}

// The unit battery lives in the child module (registry::tests); its
// use-super glob resolves through this facade's bindings and re-exports.
#[cfg(test)]
mod tests;
