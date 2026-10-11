//! [`create_provider`]: builds a provider from parts.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_types::pi_ai::IndexMap;
use eukhe_types::pi_ai::{AnyModel, Model, ProviderHeaders};
use futures::future::BoxFuture;

use super::provider::{
    FilterAllModelsFn, FilterModelsFn, ModelsPersistence, ModelsPublication, Provider,
    RefreshModelsContext,
};
use crate::api::lazy::lazy_stream;
use crate::api::{ProviderClassifier, ProviderImages, ProviderStreams};
use crate::auth::ProviderAuth;
use crate::models_store::ModelsStoreEntry;
use crate::utils::diagnostics::Thrown;
use crate::utils::model_operations::{classifier_error_result, image_error_result};
use crate::utils::models_error::{ModelsError, ModelsErrorCode};

/// Fetches a dynamic model overlay of every type: TS
/// `CreateProviderOptions.fetchModels`.
pub type FetchModelsFn = Arc<
    dyn Fn(RefreshModelsContext) -> BoxFuture<'static, Result<Vec<AnyModel>, Thrown>> + Send + Sync,
>;

/// Chat implementation of a provider: one for all chat models, or a map
/// keyed by `model.api` for mixed-API providers.
#[derive(Debug, Clone)]
pub enum ProviderApi {
    Single(ProviderStreams),
    ByApi(IndexMap<String, ProviderStreams>),
}

/// Input of [`create_provider`]: TS `CreateProviderOptions`.
#[derive(Clone, Default)]
pub struct CreateProviderOptions {
    pub id: String,
    /// Display name. Default: `id`.
    pub name: Option<String>,
    pub base_url: Option<String>,
    pub headers: Option<ProviderHeaders>,
    /// Every provider has auth semantics, even ambient/keyless ones.
    pub auth: ProviderAuth,
    /// Static baseline models of every type (empty for purely dynamic
    /// providers).
    pub models: Vec<AnyModel>,
    /// Fetch a dynamic model overlay of every type. `create_provider`
    /// restores and publishes it transactionally.
    pub fetch_models: Option<FetchModelsFn>,
    /// Credential-specific chat model availability.
    pub filter_models: Option<FilterModelsFn>,
    /// Credential-specific availability across every model type.
    pub filter_all_models: Option<FilterAllModelsFn>,
    /// Chat implementation. Optional when `images` or `classifiers` is given.
    pub api: Option<ProviderApi>,
    /// Image-generation implementations keyed by `model.api`.
    pub images: Option<IndexMap<String, ProviderImages>>,
    /// Classifier implementations keyed by `model.api`.
    pub classifiers: Option<IndexMap<String, ProviderClassifier>>,
}

/// A provider without any concrete implementation.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("Provider {id}: at least one of \"api\", \"images\", or \"classifiers\" is required.")]
pub struct CreateProviderError {
    pub id: String,
}

fn models_error(code: ModelsErrorCode, message: String) -> Thrown {
    Arc::new(ModelsError::new(code, message))
}

/// Builds a provider from parts. A single `api` streams all chat models; an
/// `api` map dispatches on `model.api`, and a model whose api has no entry
/// produces a stream error. One-shot operation maps dispatch on `model.api`
/// the same way.
///
/// # Errors
///
/// [`CreateProviderError`] when `api`, `images`, and `classifiers` provide
/// no implementation at all (empty maps count as none).
pub fn create_provider(input: CreateProviderOptions) -> Result<Provider, CreateProviderError> {
    let has_streams = match &input.api {
        Some(ProviderApi::Single(_)) => true,
        Some(ProviderApi::ByApi(by_api)) => !by_api.is_empty(),
        None => false,
    };
    let has_images = input
        .images
        .as_ref()
        .is_some_and(|images| !images.is_empty());
    let has_classifiers = input
        .classifiers
        .as_ref()
        .is_some_and(|classifiers| !classifiers.is_empty());
    if !has_streams && !has_images && !has_classifiers {
        return Err(CreateProviderError { id: input.id });
    }
    Ok(build_provider(input))
}

/// Shared catalog state: static baseline plus the dynamic overlay.
struct Catalog {
    baseline: Vec<AnyModel>,
    dynamic: Mutex<Vec<AnyModel>>,
}

impl Catalog {
    fn current(&self) -> Vec<AnyModel> {
        let mut merged = self.baseline.clone();
        let dynamic = self.dynamic.lock().unwrap_or_else(PoisonError::into_inner);
        for model in dynamic.iter() {
            let index = merged.iter().position(|entry| {
                entry.model_type() == model.model_type() && entry.id() == model.id()
            });
            match index {
                Some(index) => merged[index] = model.clone(),
                None => merged.push(model.clone()),
            }
        }
        merged
    }

    fn set_dynamic(&self, models: Vec<AnyModel>) {
        *self.dynamic.lock().unwrap_or_else(PoisonError::into_inner) = models;
    }
}

/// The chat streams for `model`, if the provider has an implementation.
fn api_for(api: Option<&ProviderApi>, model: &Model) -> Option<ProviderStreams> {
    match api? {
        ProviderApi::Single(streams) => Some(streams.clone()),
        ProviderApi::ByApi(by_api) => by_api.get(&model.api).cloned(),
    }
}

fn missing_api_stream(
    provider_id: &str,
    model: &Model,
) -> crate::utils::event_stream::AssistantMessageEventStream {
    let error = models_error(
        ModelsErrorCode::Stream,
        format!(
            "Provider {provider_id} has no API implementation for \"{}\"",
            model.api
        ),
    );
    lazy_stream(model, async move { Err(error) })
}

fn refresh_with_fetch(
    provider_id: String,
    catalog: Arc<Catalog>,
    fetch_models: FetchModelsFn,
) -> super::provider::RefreshModelsFn {
    Arc::new(move |context: RefreshModelsContext| {
        let provider_id = provider_id.clone();
        let catalog = Arc::clone(&catalog);
        let fetch_models = Arc::clone(&fetch_models);
        Box::pin(async move {
            if let Some(stored) = &context.stored {
                let restored: Vec<AnyModel> = stored
                    .models
                    .iter()
                    .filter(|model| model.provider() == provider_id)
                    .cloned()
                    .collect();
                let restore_catalog = Arc::clone(&catalog);
                let published = context
                    .publish(ModelsPublication {
                        persist: ModelsPersistence::Keep,
                        update: Some(Box::new(move || restore_catalog.set_dynamic(restored))),
                    })
                    .await?;
                if !published {
                    return Ok(());
                }
            }
            if !context.allow_network || context.signal.aborted() {
                return Ok(());
            }
            let fetched = fetch_models(context.clone()).await?;
            if context.signal.aborted() {
                return Ok(());
            }
            // Typed models always have a known type (TS `hasKnownModelType`).
            let refreshed = fetched;
            let persisted = refreshed.clone();
            context
                .publish(ModelsPublication {
                    persist: ModelsPersistence::Write(ModelsStoreEntry {
                        models: persisted,
                        checked_at: Some(super::date_now()),
                        ..ModelsStoreEntry::default()
                    }),
                    update: Some(Box::new(move || catalog.set_dynamic(refreshed))),
                })
                .await?;
            Ok(())
        })
    })
}

/// [`create_provider`] without the implementation check, for built-in
/// factories whose parts are static.
#[allow(clippy::too_many_lines)] // One provider object literal, as in TS.
pub(crate) fn build_provider(input: CreateProviderOptions) -> Provider {
    let CreateProviderOptions {
        id,
        name,
        base_url,
        headers,
        auth,
        models,
        fetch_models,
        filter_models,
        filter_all_models,
        api,
        images,
        classifiers,
    } = input;
    let api = api.map(Arc::new);
    let streams: Vec<ProviderStreams> = match api.as_deref() {
        Some(ProviderApi::Single(single)) => vec![single.clone()],
        Some(ProviderApi::ByApi(by_api)) => by_api.values().cloned().collect(),
        None => Vec::new(),
    };

    let catalog = Arc::new(Catalog {
        baseline: models,
        dynamic: Mutex::new(Vec::new()),
    });

    let chat_catalog = Arc::clone(&catalog);
    let all_catalog = Arc::clone(&catalog);
    let stream_api = api.clone();
    let stream_id = id.clone();
    let simple_api = api.clone();
    let simple_id = id.clone();

    let mut provider = Provider {
        id: id.clone(),
        name: name.unwrap_or_else(|| id.clone()),
        base_url,
        headers,
        auth,
        get_models: Arc::new(move || {
            Ok(chat_catalog
                .current()
                .into_iter()
                .filter_map(|model| match model {
                    AnyModel::Chat(model) => Some(model),
                    AnyModel::Image(_) | AnyModel::Classifier(_) => None,
                })
                .collect())
        }),
        get_all_models: Some(Arc::new(move || Ok(all_catalog.current()))),
        refresh_models: fetch_models
            .map(|fetch| refresh_with_fetch(id.clone(), Arc::clone(&catalog), fetch)),
        filter_models,
        filter_all_models,
        stream: Arc::new(move |model, context, options| {
            match api_for(stream_api.as_deref(), model) {
                Some(streams) => (streams.stream)(model, context, options),
                None => missing_api_stream(&stream_id, model),
            }
        }),
        stream_simple: Arc::new(move |model, context, options| {
            match api_for(simple_api.as_deref(), model) {
                Some(streams) => (streams.stream_simple)(model, context, options),
                None => missing_api_stream(&simple_id, model),
            }
        }),
        fetch_deferred: None,
        cancel_deferred: None,
        generate_images: None,
        classify: None,
    };

    if streams.iter().any(|entry| entry.fetch_deferred.is_some()) {
        let api = api.clone();
        let provider_id = id.clone();
        provider.fetch_deferred = Some(Arc::new(move |model, handle, options| {
            let implementation =
                api_for(api.as_deref(), model).and_then(|streams| streams.fetch_deferred);
            let (provider_id, request_model, handle) =
                (provider_id.clone(), model.clone(), handle.clone());
            lazy_stream(model, async move {
                let fetch = implementation.ok_or_else(|| {
                    models_error(
                        ModelsErrorCode::Provider,
                        format!(
                            "Provider {provider_id} does not support deferred responses for \"{}\"",
                            request_model.api
                        ),
                    )
                })?;
                Ok(fetch(&request_model, &handle, options))
            })
        }));
    }
    if streams.iter().any(|entry| entry.cancel_deferred.is_some()) {
        let api = api;
        let provider_id = id.clone();
        provider.cancel_deferred = Some(Arc::new(move |model, handle, options| {
            let implementation =
                api_for(api.as_deref(), model).and_then(|streams| streams.cancel_deferred);
            let Some(cancel) = implementation else {
                let error = models_error(
                    ModelsErrorCode::Provider,
                    format!(
                        "Provider {provider_id} cannot cancel deferred responses for \"{}\"",
                        model.api
                    ),
                );
                return Box::pin(async move { Err(error) });
            };
            cancel(model, handle, options)
        }));
    }
    if let Some(images) = images.filter(|images| !images.is_empty()) {
        let provider_id = id.clone();
        provider.generate_images = Some(Arc::new(move |model, context, options| {
            if let Some(implementation) = images.get(&model.api) {
                (implementation.generate_images)(model, context, options)
            } else {
                let error = models_error(
                    ModelsErrorCode::Provider,
                    format!(
                        "Provider {provider_id} has no image generation implementation for \"{}\"",
                        model.api
                    ),
                );
                let result = image_error_result(model, &error, false);
                Box::pin(async move { result })
            }
        }));
    }
    if let Some(classifiers) = classifiers.filter(|classifiers| !classifiers.is_empty()) {
        let provider_id = id;
        provider.classify = Some(Arc::new(move |model, context, options| {
            if let Some(implementation) = classifiers.get(&model.api) {
                (implementation.classify)(model, context, options)
            } else {
                let error = models_error(
                    ModelsErrorCode::Provider,
                    format!(
                        "Provider {provider_id} has no classifier implementation for \"{}\"",
                        model.api
                    ),
                );
                let result = classifier_error_result(model, &error, false);
                Box::pin(async move { result })
            }
        }));
    }

    provider
}
