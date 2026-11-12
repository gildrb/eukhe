//! The built-in model catalog in a session: every model `eukhe model list`
//! lists resolves and streams in a session: one model registry serves
//! both the model list and `--model` resolution.
//!
//! The list is the registry's built-in catalog (`crate::models::registry`:
//! the bundled snapshot's union with the compiled catalog). The `eukhe_ai`
//! providers carry the compiled catalog only, so each model of the
//! snapshot its provider lacks joins that provider here, and a provider
//! only the snapshot has (`azure-openai-responses`) joins as a provider of
//! its own: stored-credential auth (no environment key names it), and
//! models.json composes over it like over any built-in provider. A model
//! the provider has keeps its compiled entry (the bundled snapshot carries
//! none: it is made of the models.dev models the compiled catalog lacks).
//! A joined model whose api the provider does not implement streams
//! through that api's built-in implementation.

use std::collections::HashSet;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_ai::auth::{env_api_key_auth, ProviderAuth};
use eukhe_ai::models::{chat_models, GetModelsFn, Provider};
use eukhe_types::pi_ai::{AnyModel, Model};

use super::compose::layered_streams;

/// `providers` with the built-in `catalog` models they lack, plus a
/// provider for each catalog provider none of them is.
pub(super) fn with_catalog_models(
    providers: Vec<Provider>,
    catalog: &[eukhe_types::ai::Model],
) -> Vec<Provider> {
    let mut joining: Vec<(String, Vec<Model>)> = Vec::new();
    for entry in catalog {
        let model = match session_model(entry) {
            Ok(model) => model,
            Err(error) => {
                tracing::warn!(
                    "catalog model {}/{} has no session form: {error}",
                    entry.provider,
                    entry.id
                );
                continue;
            }
        };
        match joining.iter_mut().find(|(id, _)| *id == model.provider) {
            Some((_, models)) => models.push(model),
            None => joining.push((model.provider.clone(), vec![model])),
        }
    }
    let mut layered: Vec<Provider> = providers
        .into_iter()
        .map(
            |provider| match joining.iter().position(|(id, _)| *id == provider.id) {
                Some(index) => with_models(provider, joining.swap_remove(index).1),
                None => provider,
            },
        )
        .collect();
    layered.extend(
        joining
            .into_iter()
            .map(|(id, models)| catalog_provider(id, models)),
    );
    layered
}

/// The `eukhe_ai` form of a registry catalog model (the same JSON shape).
fn session_model(model: &eukhe_types::ai::Model) -> Result<Model, serde_json::Error> {
    serde_json::to_value(model).and_then(serde_json::from_value)
}

/// The base provider's list and the joined list it was extended to.
type Joined = Option<(Arc<[AnyModel]>, Arc<[AnyModel]>)>;

/// `base` with each of `models` whose id its chat models lack. The joined
/// list is cached against the base list it extends.
fn with_models(base: Provider, models: Vec<Model>) -> Provider {
    let base = Arc::new(base);
    let joined: Mutex<Joined> = Mutex::new(None);
    let own = Arc::clone(&base);
    let get_models: GetModelsFn = Arc::new(move || {
        let current = (own.get_models)()?;
        let mut cache = joined.lock().unwrap_or_else(PoisonError::into_inner);
        if let Some((seen, list)) = cache.as_ref() {
            if Arc::ptr_eq(seen, &current) {
                return Ok(Arc::clone(list));
            }
        }
        let list: Arc<[AnyModel]> = {
            let ids: HashSet<&str> = chat_models(&current)
                .map(|model| model.id.as_str())
                .collect();
            current
                .iter()
                .cloned()
                .chain(
                    models
                        .iter()
                        .filter(|model| !ids.contains(model.id.as_str()))
                        .cloned()
                        .map(AnyModel::Chat),
                )
                .collect()
        };
        *cache = Some((current, Arc::clone(&list)));
        Ok(list)
    });
    let (stream, stream_simple) = layered_streams(Some(Arc::clone(&base)));
    Provider {
        get_models,
        stream,
        stream_simple,
        ..Provider::clone(&base)
    }
}

/// A provider only the catalog has: its models, a stored API key, and each
/// model streaming through its api's built-in implementation.
fn catalog_provider(id: String, models: Vec<Model>) -> Provider {
    let models: Arc<[AnyModel]> = models.into_iter().map(AnyModel::Chat).collect();
    let get_models: GetModelsFn = Arc::new(move || Ok(Arc::clone(&models)));
    let (stream, stream_simple) = layered_streams(None);
    Provider {
        name: id.clone(),
        auth: ProviderAuth {
            api_key: Some(env_api_key_auth(&format!("{id} API key"), &[])),
            oauth: None,
        },
        id,
        base_url: None,
        headers: None,
        get_models,
        refresh_models: None,
        filter_models: None,
        filter_all_models: None,
        stream,
        stream_simple,
        fetch_deferred: None,
        cancel_deferred: None,
        generate_images: None,
        classify: None,
    }
}
