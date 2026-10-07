//! eukhe `models.json` composed over the built-in pi-ai providers: the TS
//! `composeModelProvider` shape with eukhe's `models.json` schema and
//! semantics (`crate::models::custom`, `ModelRegistry`).

use std::collections::{BTreeMap, HashSet};
use std::path::Path;
use std::sync::Arc;

use eukhe_chord::context::AbortSignal;
use eukhe_pi_ai::api::builtin::load_stream_api;
use eukhe_pi_ai::api::lazy::lazy_stream;
use eukhe_pi_ai::auth::{
    ApiKeyAuth, ApiKeyCredential, ApiKeyResolveInput, AuthResult, LoginOptions, ModelAuth,
    OAuthAuth, OAuthCredential, ProviderAuth, ProviderAuthInteraction,
};
use eukhe_pi_ai::models::{GetAllModelsFn, GetModelsFn, Provider};
use eukhe_pi_ai::utils::diagnostics::Thrown;
use eukhe_types::pi_ai::{AnyModel, Model, ProviderHeaders};
use futures::future::BoxFuture;
use serde_json::{json, Map, Value};

use super::stores::{blocking, thrown};
use super::ModelsError;
use crate::auth::resolve_config_value::resolve_config_value;
use crate::models::custom::{
    merge_compat, parse_models_config, validate_config, ModelCostConfig, ModelDefinition,
    ModelOverride, ProviderConfig,
};

fn models_json_error(error: String, path: &Path) -> ModelsError {
    if error.contains("models.json") {
        ModelsError::ModelsJson(error)
    } else {
        ModelsError::ModelsJson(format!("{error}\n\nFile: {}", path.display()))
    }
}

/// The built-in providers with `models_json` composed over them, plus the
/// custom providers it defines. A missing file leaves the built-ins as is.
pub(super) fn compose_providers(
    builtins: Vec<Provider>,
    models_json: &Path,
) -> Result<Vec<Provider>, ModelsError> {
    let content = match std::fs::read_to_string(models_json) {
        Ok(content) => content,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(builtins),
        Err(error) => {
            return Err(ModelsError::ModelsJson(format!(
                "Failed to load models.json: {error}\n\nFile: {}",
                models_json.display()
            )))
        }
    };
    let config =
        parse_models_config(&content).map_err(|error| models_json_error(error, models_json))?;
    let with_models: HashSet<String> = builtins
        .iter()
        .filter(|provider| (provider.get_models)().is_ok_and(|models| !models.is_empty()))
        .map(|provider| provider.id.clone())
        .collect();
    validate_config(&config, &|provider| with_models.contains(provider))
        .map_err(|error| models_json_error(error, models_json))?;

    let mut providers = Vec::with_capacity(builtins.len() + config.providers.len());
    let mut composed_ids = HashSet::new();
    for base in builtins {
        match config.providers.get(&base.id) {
            Some(provider_config) => {
                composed_ids.insert(base.id.clone());
                let id = base.id.clone();
                providers.push(
                    compose_provider(&id, Some(base), provider_config)
                        .map_err(|error| models_json_error(error, models_json))?,
                );
            }
            None => providers.push(base),
        }
    }
    for (id, provider_config) in &config.providers {
        let defines_models = provider_config
            .models
            .as_ref()
            .is_some_and(|models| !models.is_empty());
        // Overrides for a provider that does not exist change nothing.
        if composed_ids.contains(id) || !defines_models {
            continue;
        }
        providers.push(
            compose_provider(id, None, provider_config)
                .map_err(|error| models_json_error(error, models_json))?,
        );
    }
    Ok(providers)
}

/// The provider/model rewrites `models.json` applies to built-in models.
struct BuiltinRewrite {
    base_url: Option<String>,
    compat: Option<Value>,
    overrides: BTreeMap<String, ModelOverride>,
}

impl BuiltinRewrite {
    fn apply(&self, model: &Model) -> Result<Model, String> {
        let mut value = serde_json::to_value(model).map_err(|error| error.to_string())?;
        let Some(object) = value.as_object_mut() else {
            return Err(format!("model {} did not serialize to an object", model.id));
        };
        if let Some(base_url) = &self.base_url {
            object.insert("baseUrl".to_owned(), Value::String(base_url.clone()));
        }
        if let Some(compat) = &self.compat {
            merge_compat_value(object, compat);
        }
        if let Some(over) = self.overrides.get(&model.id) {
            apply_model_override(object, over);
        }
        serde_json::from_value(value)
            .map_err(|error| format!("Provider {}, model {}: {error}", model.provider, model.id))
    }
}

/// `compat` merged with eukhe's `merge_compat` (override fields win; the
/// routing sub-objects merge).
fn merge_compat_value(object: &mut Map<String, Value>, over: &Value) {
    let Value::Object(over) = over else {
        return;
    };
    let base = object
        .get("compat")
        .and_then(Value::as_object)
        .map(|raw| eukhe_types::ai::ModelCompat { raw: raw.clone() });
    let merged = merge_compat(
        base.as_ref(),
        Some(eukhe_types::ai::ModelCompat { raw: over.clone() }),
    );
    if let Some(merged) = merged {
        object.insert("compat".to_owned(), Value::Object(merged.raw));
    }
}

/// eukhe's `model_inputs`: anything but "image" is text.
fn model_inputs(values: Option<&Vec<String>>) -> Value {
    match values {
        None => json!(["text"]),
        Some(items) => Value::Array(
            items
                .iter()
                .map(|item| {
                    Value::String(if item == "image" { "image" } else { "text" }.to_owned())
                })
                .collect(),
        ),
    }
}

fn cost_value(config: &ModelCostConfig) -> Value {
    json!({
        "input": config.input.unwrap_or(0.0),
        "output": config.output.unwrap_or(0.0),
        "cacheRead": config.cache_read.unwrap_or(0.0),
        "cacheWrite": config.cache_write.unwrap_or(0.0),
    })
}

/// eukhe's `apply_model_override`, over the pi-ai model's JSON.
fn apply_model_override(object: &mut Map<String, Value>, over: &ModelOverride) {
    if let Some(name) = &over.name {
        object.insert("name".to_owned(), Value::String(name.clone()));
    }
    if let Some(reasoning) = over.reasoning {
        object.insert("reasoning".to_owned(), Value::Bool(reasoning));
    }
    if let Some(map) = &over.thinking_level_map {
        let merged = object
            .entry("thinkingLevelMap")
            .or_insert_with(|| Value::Object(Map::new()));
        if !merged.is_object() {
            *merged = Value::Object(Map::new());
        }
        if let Value::Object(merged) = merged {
            for (level, value) in map {
                merged.insert(
                    level.clone(),
                    value.clone().map_or(Value::Null, Value::String),
                );
            }
        }
    }
    if let Some(input) = &over.input {
        object.insert("input".to_owned(), model_inputs(Some(input)));
    }
    if let Some(window) = over.context_window {
        object.insert("contextWindow".to_owned(), json!(window));
    }
    if let Some(max_tokens) = over.max_tokens {
        object.insert("maxTokens".to_owned(), json!(max_tokens));
    }
    if let Some(cost) = &over.cost {
        if let Some(Value::Object(base)) = object.get_mut("cost") {
            for (field, value) in [
                ("input", cost.input),
                ("output", cost.output),
                ("cacheRead", cost.cache_read),
                ("cacheWrite", cost.cache_write),
            ] {
                if let Some(value) = value {
                    base.insert(field.to_owned(), json!(value));
                }
            }
        }
    }
    if let Some(compat) = &over.compat {
        merge_compat_value(object, compat);
    }
    if let Some(headers) = &over.headers {
        let merged = object
            .entry("headers")
            .or_insert_with(|| Value::Object(Map::new()));
        if let Value::Object(merged) = merged {
            for (name, value) in headers {
                merged.insert(name.clone(), Value::String(value.clone()));
            }
        }
    }
}

/// A `models.json` model definition as a pi-ai model (eukhe's
/// `load_custom_models` defaults). `None` when neither the definition, the
/// provider, nor the provider's built-in models name an api and base URL.
fn custom_model(
    provider_id: &str,
    definition: &ModelDefinition,
    config: &ProviderConfig,
    defaults: Option<&Model>,
) -> Result<Option<Model>, String> {
    let Some(api) = definition
        .api
        .clone()
        .or_else(|| config.api.clone())
        .or_else(|| defaults.map(|model| model.api.clone()))
    else {
        return Ok(None);
    };
    let Some(base_url) = definition
        .base_url
        .clone()
        .or_else(|| config.base_url.clone())
        .or_else(|| defaults.map(|model| model.base_url.clone()))
    else {
        return Ok(None);
    };
    let mut object = Map::new();
    object.insert("id".to_owned(), json!(definition.id));
    object.insert(
        "name".to_owned(),
        json!(definition
            .name
            .clone()
            .unwrap_or_else(|| definition.id.clone())),
    );
    object.insert("api".to_owned(), json!(api));
    object.insert("provider".to_owned(), json!(provider_id));
    object.insert("baseUrl".to_owned(), json!(base_url));
    object.insert(
        "reasoning".to_owned(),
        json!(definition.reasoning.unwrap_or(false)),
    );
    if let Some(map) = &definition.thinking_level_map {
        object.insert("thinkingLevelMap".to_owned(), json!(map));
    }
    object.insert("input".to_owned(), model_inputs(definition.input.as_ref()));
    object.insert(
        "cost".to_owned(),
        cost_value(
            definition
                .cost
                .as_ref()
                .unwrap_or(&ModelCostConfig::default()),
        ),
    );
    object.insert(
        "contextWindow".to_owned(),
        json!(definition.context_window.unwrap_or(128_000)),
    );
    object.insert(
        "maxTokens".to_owned(),
        json!(definition.max_tokens.unwrap_or(16_384)),
    );
    if let Some(headers) = definition
        .headers
        .as_ref()
        .filter(|headers| !headers.is_empty())
    {
        object.insert("headers".to_owned(), json!(headers));
    }
    if let Some(compat) = &config.compat {
        merge_compat_value(&mut object, compat);
    }
    serde_json::from_value(Value::Object(object))
        .map(Some)
        .map_err(|error| format!("Provider {provider_id}, model {}: {error}", definition.id))
}

fn upsert(models: &mut Vec<Model>, model: Model) {
    match models.iter().position(|entry| entry.id == model.id) {
        Some(index) => models[index] = model,
        None => models.push(model),
    }
}

/// The chat models of a composed provider: the built-in models rewritten,
/// then the custom models upserted by id. Recomputed per call so a dynamic
/// base (Prime Inference) stays live.
fn composed_chat_models(
    base: Option<Arc<Provider>>,
    rewrite: Arc<BuiltinRewrite>,
    custom: Arc<Vec<Model>>,
) -> GetModelsFn {
    Arc::new(move || {
        let mut models = match &base {
            Some(base) => (base.get_models)()?
                .into_iter()
                .map(|model| rewrite.apply(&model).map_err(thrown))
                .collect::<Result<Vec<_>, _>>()?,
            None => Vec::new(),
        };
        for model in custom.iter() {
            upsert(&mut models, model.clone());
        }
        Ok(models)
    })
}

/// One provider with its `models.json` layer.
fn compose_provider(
    id: &str,
    base: Option<Provider>,
    config: &ProviderConfig,
) -> Result<Provider, String> {
    let base = base.map(Arc::new);
    let rewrite = Arc::new(BuiltinRewrite {
        base_url: config.base_url.clone(),
        compat: config.compat.clone(),
        overrides: config.model_overrides.clone().unwrap_or_default(),
    });
    let base_models = match &base {
        Some(base) => (base.get_models)().map_err(|error| error.to_string())?,
        None => Vec::new(),
    };
    let mut custom = Vec::new();
    for definition in config.models.as_deref().unwrap_or_default() {
        if let Some(model) = custom_model(id, definition, config, base_models.first())? {
            upsert(&mut custom, model);
        }
    }
    // Fail at load, not per request, on overrides that break a model.
    for model in &base_models {
        rewrite.apply(model)?;
    }

    let chat_models = composed_chat_models(base.clone(), rewrite, Arc::new(custom));
    let get_all_models = base
        .as_ref()
        .and_then(|base| base.get_all_models.clone())
        .map(|base_all| {
            let chat_models = Arc::clone(&chat_models);
            let all: GetAllModelsFn = Arc::new(move || {
                let mut models: Vec<AnyModel> =
                    chat_models()?.into_iter().map(AnyModel::Chat).collect();
                models.extend(
                    base_all()?
                        .into_iter()
                        .filter(|model| !matches!(model, AnyModel::Chat(_))),
                );
                Ok(models)
            });
            all
        });

    let headers = config.headers.clone().filter(|headers| !headers.is_empty());
    let auth_header = config.auth_header.unwrap_or(false);
    let api_key: Arc<dyn ApiKeyAuth> = Arc::new(ConfiguredApiKeyAuth {
        provider_id: id.to_owned(),
        inherited: base.as_ref().and_then(|base| base.auth.api_key.clone()),
        api_key: config.api_key.clone(),
        headers: headers.clone(),
        auth_header,
    });
    let oauth =
        base.as_ref()
            .and_then(|base| base.auth.oauth.clone())
            .map(|oauth| -> Arc<dyn OAuthAuth> {
                if headers.is_none() && !auth_header {
                    return oauth;
                }
                Arc::new(ConfiguredOAuth {
                    provider_id: id.to_owned(),
                    inner: oauth,
                    headers: headers.clone(),
                    auth_header,
                })
            });

    let stream_base = base.clone();
    let simple_base = base.clone();
    Ok(Provider {
        id: id.to_owned(),
        name: config
            .name
            .clone()
            .or_else(|| base.as_ref().map(|base| base.name.clone()))
            .unwrap_or_else(|| id.to_owned()),
        base_url: config
            .base_url
            .clone()
            .or_else(|| base.as_ref().and_then(|base| base.base_url.clone())),
        headers: base.as_ref().and_then(|base| base.headers.clone()),
        auth: ProviderAuth {
            api_key: Some(api_key),
            oauth,
        },
        get_models: chat_models,
        get_all_models,
        refresh_models: base.as_ref().and_then(|base| base.refresh_models.clone()),
        filter_models: base.as_ref().and_then(|base| base.filter_models.clone()),
        filter_all_models: base
            .as_ref()
            .and_then(|base| base.filter_all_models.clone()),
        stream: Arc::new(move |model, context, options| {
            if let Some(base) = stream_base.as_ref().filter(|base| base_serves(base, model)) {
                return (base.stream)(model, context, options);
            }
            let api_model = model.clone();
            let context = context.clone();
            lazy_stream(model, async move {
                let api = load_stream_api(&api_model.api)?;
                Ok((api.stream)(&api_model, &context, options))
            })
        }),
        stream_simple: Arc::new(move |model, context, options| {
            if let Some(base) = simple_base.as_ref().filter(|base| base_serves(base, model)) {
                return (base.stream_simple)(model, context, options);
            }
            let api_model = model.clone();
            let context = context.clone();
            lazy_stream(model, async move {
                let api = load_stream_api(&api_model.api)?;
                Ok((api.stream_simple)(&api_model, &context, options))
            })
        }),
        fetch_deferred: base.as_ref().and_then(|base| base.fetch_deferred.clone()),
        cancel_deferred: base.as_ref().and_then(|base| base.cancel_deferred.clone()),
        generate_images: base.as_ref().and_then(|base| base.generate_images.clone()),
        classify: base.as_ref().and_then(|base| base.classify.clone()),
    })
}

/// Whether the built-in provider implements `model`'s api (TS
/// `supportsBaseApi`).
fn base_serves(base: &Provider, model: &Model) -> bool {
    (base.get_models)().is_ok_and(|models| models.iter().any(|entry| entry.api == model.api))
}

/// Merges the provider's configured headers (and the `authHeader` bearer)
/// into resolved request auth.
fn with_configured_headers(
    provider_id: &str,
    mut auth: ModelAuth,
    headers: Option<&BTreeMap<String, String>>,
    auth_header: bool,
) -> Result<ModelAuth, Thrown> {
    if let Some(headers) = headers {
        let merged = auth.headers.get_or_insert_with(ProviderHeaders::new);
        for (name, value) in headers {
            merged.insert(name.clone(), Some(value.clone()));
        }
    }
    if auth_header {
        let Some(api_key) = auth.api_key.clone() else {
            return Err(thrown(format!("No API key found for \"{provider_id}\"")));
        };
        auth.headers
            .get_or_insert_with(ProviderHeaders::new)
            .insert(
                "Authorization".to_owned(),
                Some(format!("Bearer {api_key}")),
            );
    }
    Ok(auth)
}

/// Api-key auth of a provider with a `models.json` layer, in eukhe's order:
/// the stored credential and the provider's environment key (the built-in
/// auth), then the configured `apiKey`. Configured headers alone make the
/// provider usable (eukhe `has_configured_auth`); `authHeader` needs a key.
struct ConfiguredApiKeyAuth {
    provider_id: String,
    inherited: Option<Arc<dyn ApiKeyAuth>>,
    api_key: Option<String>,
    headers: Option<BTreeMap<String, String>>,
    auth_header: bool,
}

impl ApiKeyAuth for ConfiguredApiKeyAuth {
    // The trait returns a borrowed name; the fallback is a literal.
    #[allow(clippy::unnecessary_literal_bound)]
    fn name(&self) -> &str {
        match &self.inherited {
            Some(inherited) => inherited.name(),
            None => "API key",
        }
    }

    fn login(
        &self,
        interaction: ProviderAuthInteraction,
    ) -> Option<BoxFuture<'_, Result<ApiKeyCredential, Thrown>>> {
        self.inherited.as_ref()?.login(interaction)
    }

    fn resolve(
        &self,
        input: ApiKeyResolveInput,
    ) -> BoxFuture<'_, Result<Option<AuthResult>, Thrown>> {
        Box::pin(async move {
            let stored = input.credential.clone();
            let mut result = match &self.inherited {
                Some(inherited) => inherited.resolve(input).await?,
                None => stored.and_then(|credential| {
                    let key = credential.key?;
                    Some(AuthResult {
                        auth: ModelAuth {
                            api_key: Some(key),
                            ..ModelAuth::default()
                        },
                        env: credential.env,
                        source: Some("stored credential".to_owned()),
                    })
                }),
            };
            if result.is_none() {
                if let Some(configured) = self.api_key.clone() {
                    let key = blocking(move || Ok(resolve_config_value(&configured))).await?;
                    result = key.map(|key| AuthResult {
                        auth: ModelAuth {
                            api_key: Some(key),
                            ..ModelAuth::default()
                        },
                        env: None,
                        source: Some("configured API key".to_owned()),
                    });
                }
            }
            if result.is_none() && self.headers.is_some() && !self.auth_header {
                result = Some(AuthResult {
                    source: Some("configured headers".to_owned()),
                    ..AuthResult::default()
                });
            }
            let Some(mut result) = result else {
                return Ok(None);
            };
            result.auth = with_configured_headers(
                &self.provider_id,
                result.auth,
                self.headers.as_ref(),
                self.auth_header,
            )?;
            Ok(Some(result))
        })
    }
}

/// OAuth of a built-in provider whose `models.json` entry adds request
/// headers or `authHeader`.
struct ConfiguredOAuth {
    provider_id: String,
    inner: Arc<dyn OAuthAuth>,
    headers: Option<BTreeMap<String, String>>,
    auth_header: bool,
}

impl OAuthAuth for ConfiguredOAuth {
    fn name(&self) -> &str {
        self.inner.name()
    }

    fn is_subscription(&self) -> Option<bool> {
        self.inner.is_subscription()
    }

    fn login_label(&self) -> Option<&str> {
        self.inner.login_label()
    }

    fn login(
        &self,
        interaction: ProviderAuthInteraction,
        options: Option<LoginOptions>,
    ) -> BoxFuture<'_, Result<OAuthCredential, Thrown>> {
        self.inner.login(interaction, options)
    }

    fn refresh(
        &self,
        credential: OAuthCredential,
        signal: AbortSignal,
    ) -> BoxFuture<'_, Result<OAuthCredential, Thrown>> {
        self.inner.refresh(credential, signal)
    }

    fn to_auth<'a>(
        &'a self,
        credential: &'a OAuthCredential,
    ) -> BoxFuture<'a, Result<ModelAuth, Thrown>> {
        Box::pin(async move {
            let auth = self.inner.to_auth(credential).await?;
            with_configured_headers(
                &self.provider_id,
                auth,
                self.headers.as_ref(),
                self.auth_header,
            )
        })
    }
}
