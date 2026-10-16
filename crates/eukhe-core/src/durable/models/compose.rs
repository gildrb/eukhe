//! eukhe `models.json` composed over the built-in pi-ai providers: the TS
//! `composeModelProvider` shape over `crate::models::custom` — the parse,
//! the model composition, and the configured auth the registry runs too.

use std::path::Path;
use std::sync::Arc;

use eukhe_ai::api::builtin::load_stream_api;
use eukhe_ai::api::lazy::lazy_stream;
use eukhe_ai::auth::{
    ApiKeyAuth, ApiKeyCredential, ApiKeyResolveInput, AuthResult, LoginOptions, ModelAuth,
    OAuthAuth, OAuthCredential, ProviderAuth, ProviderAuthInteraction,
};
use eukhe_ai::models::{chat_models, GetModelsFn, Provider};
use eukhe_ai::utils::diagnostics::Thrown;
use eukhe_chord::context::AbortSignal;
use eukhe_types::pi_ai::{AnyModel, Model, ProviderHeaders};
use futures::future::BoxFuture;

use super::stores::{blocking, thrown};
use super::ModelsError;
use crate::models::custom::{in_file, ModelsConfig, ProviderConfig};

/// The built-in providers with `models_json` composed over them, plus the
/// custom providers it defines. A missing file leaves the built-ins as is.
/// Every provider's models then follow eukhe's thinking capability rule
/// ([`with_map_addressed_reasoning`]).
pub(super) fn compose_providers(
    builtins: Vec<Provider>,
    models_json: &Path,
) -> Result<Vec<Provider>, ModelsError> {
    compose_layers(builtins, models_json).map(|providers| {
        providers
            .into_iter()
            .map(with_map_addressed_reasoning)
            .collect()
    })
}

/// eukhe's thinking capability rule (#2858, `eukhe_types::ai::supports_thinking`):
/// a model whose thinking-level map addresses a level (maps it to a wire
/// value) can think even when its coarse `reasoning` flag is false (the
/// catalog ships `gpt-5.3-chat-latest` as `reasoning: false` with an
/// addressable `xhigh`). pi-ai reads only the flag, so the provider's models
/// carry the flag set: the supported levels, the clamp, and the request
/// reasoning controls then follow the map.
fn with_map_addressed_reasoning(mut provider: Provider) -> Provider {
    fn needs_flag(model: &Model) -> bool {
        !model.reasoning
            && model
                .thinking_level_map
                .as_ref()
                .is_some_and(|map| map.values().any(Option::is_some))
    }
    let get_models = Arc::clone(&provider.get_models);
    provider.get_models = Arc::new(move || {
        get_models().map(|models| {
            // Share the list untouched unless some chat model needs the flag.
            if !models.iter().any(|model| match model {
                AnyModel::Chat(model) => needs_flag(model),
                AnyModel::Image(_) | AnyModel::Classifier(_) => false,
            }) {
                return models;
            }
            models
                .iter()
                .map(|model| match model {
                    AnyModel::Chat(chat) if needs_flag(chat) => {
                        let mut chat = chat.clone();
                        chat.reasoning = true;
                        AnyModel::Chat(chat)
                    }
                    AnyModel::Chat(_) | AnyModel::Image(_) | AnyModel::Classifier(_) => {
                        model.clone()
                    }
                })
                .collect()
        })
    });
    provider
}

/// [`compose_providers`] before the capability rule.
fn compose_layers(
    builtins: Vec<Provider>,
    models_json: &Path,
) -> Result<Vec<Provider>, ModelsError> {
    let has_models = |provider: &Provider| (provider.get_models)().is_ok_and(|m| !m.is_empty());
    let config = ModelsConfig::load(models_json, &|id| {
        builtins
            .iter()
            .any(|provider| provider.id == id && has_models(provider))
    })
    .map_err(ModelsError::ModelsJson)?;
    let error = |error: String| ModelsError::ModelsJson(in_file(error, models_json));
    let mut configs = config.providers;
    let mut providers = Vec::with_capacity(builtins.len() + configs.len());
    for base in builtins {
        match configs.remove(&base.id) {
            Some(provider_config) => {
                let id = base.id.clone();
                providers.push(compose_provider(&id, Some(base), provider_config).map_err(error)?);
            }
            None => providers.push(base),
        }
    }
    // Overrides for a provider that does not exist change nothing.
    for (id, provider_config) in configs {
        if provider_config
            .models
            .as_ref()
            .is_some_and(|m| !m.is_empty())
        {
            providers.push(compose_provider(&id, None, provider_config).map_err(error)?);
        }
    }
    Ok(providers)
}

/// A built-in chat model under the provider's `models.json` rewrites.
fn rewrite(config: &ProviderConfig, model: &Model) -> Result<Model, String> {
    if config.rewrites(&model.id) {
        config.rewrite_built_in(model)
    } else {
        Ok(model.clone())
    }
}

/// The models of a composed provider: the built-in chat models rewritten,
/// then the custom models upserted by id, then the built-in non-chat models.
/// Recomputed per call so a dynamic base (Prime Inference) stays live.
fn composed_models(
    base: Option<Arc<Provider>>,
    config: Arc<ProviderConfig>,
    custom: Arc<Vec<Model>>,
) -> GetModelsFn {
    Arc::new(move || {
        let base_models = match &base {
            Some(base) => Some((base.get_models)()?),
            None => None,
        };
        let base_models = base_models.as_deref().unwrap_or_default();
        let mut chat = chat_models(base_models)
            .map(|model| rewrite(&config, model).map_err(thrown))
            .collect::<Result<Vec<_>, _>>()?;
        for model in custom.iter() {
            match chat.iter().position(|entry| entry.id == model.id) {
                Some(index) => chat[index] = model.clone(),
                None => chat.push(model.clone()),
            }
        }
        let others = base_models
            .iter()
            .filter(|model| !matches!(model, AnyModel::Chat(_)))
            .cloned();
        Ok(chat.into_iter().map(AnyModel::Chat).chain(others).collect())
    })
}

/// One provider with its `models.json` layer.
fn compose_provider(
    id: &str,
    base: Option<Provider>,
    config: ProviderConfig,
) -> Result<Provider, String> {
    let base = base.map(Arc::new);
    let config = Arc::new(config);
    let base_models = match &base {
        Some(base) => (base.get_models)().map_err(|error| error.to_string())?,
        None => Arc::from([]),
    };
    let defaults = chat_models(&base_models)
        .next()
        .map(|model| (model.api.as_str(), model.base_url.as_str()));
    let custom = Arc::new(config.custom_models(id, defaults)?);
    // Fail at load, not per request, on overrides that break a model.
    for model in chat_models(&base_models) {
        rewrite(&config, model)?;
    }

    let get_models = composed_models(base.clone(), Arc::clone(&config), custom);
    let api_key: Arc<dyn ApiKeyAuth> = Arc::new(ConfiguredApiKeyAuth {
        provider_id: id.to_owned(),
        inherited: base.as_ref().and_then(|base| base.auth.api_key.clone()),
        config: Arc::clone(&config),
    });
    let adds_headers = config.headers.as_ref().is_some_and(|h| !h.is_empty())
        || config.auth_header.unwrap_or(false);
    let oauth =
        base.as_ref()
            .and_then(|base| base.auth.oauth.clone())
            .map(|oauth| -> Arc<dyn OAuthAuth> {
                if !adds_headers {
                    return oauth;
                }
                Arc::new(ConfiguredOAuth {
                    provider_id: id.to_owned(),
                    inner: oauth,
                    config: Arc::clone(&config),
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
        get_models,
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
    (base.get_models)().is_ok_and(|models| chat_models(&models).any(|entry| entry.api == model.api))
}

/// Merges the provider's configured headers (and the `authHeader` bearer)
/// into resolved request auth.
fn with_configured_headers(
    provider_id: &str,
    mut auth: ModelAuth,
    config: &ProviderConfig,
) -> Result<ModelAuth, Thrown> {
    let bearer = config
        .bearer_header(provider_id, auth.api_key.as_deref())
        .map_err(thrown)?;
    let configured = config
        .headers
        .iter()
        .flatten()
        .map(|(k, v)| (k.clone(), v.clone()));
    for (name, value) in configured.chain(bearer) {
        auth.headers
            .get_or_insert_with(ProviderHeaders::new)
            .insert(name, Some(value));
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
    config: Arc<ProviderConfig>,
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
            if result.is_none() && self.config.api_key.is_some() {
                let config = Arc::clone(&self.config);
                let key = blocking(move || Ok(config.configured_api_key())).await?;
                result = key.map(|key| AuthResult {
                    auth: ModelAuth {
                        api_key: Some(key),
                        ..ModelAuth::default()
                    },
                    env: None,
                    source: Some("configured API key".to_owned()),
                });
            }
            if result.is_none() && self.config.authenticates_with_headers() {
                result = Some(AuthResult {
                    source: Some("configured headers".to_owned()),
                    ..AuthResult::default()
                });
            }
            let Some(mut result) = result else {
                return Ok(None);
            };
            result.auth = with_configured_headers(&self.provider_id, result.auth, &self.config)?;
            Ok(Some(result))
        })
    }
}

/// OAuth of a built-in provider whose `models.json` entry adds request
/// headers or `authHeader`.
struct ConfiguredOAuth {
    provider_id: String,
    inner: Arc<dyn OAuthAuth>,
    config: Arc<ProviderConfig>,
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
            with_configured_headers(&self.provider_id, auth, &self.config)
        })
    }
}
