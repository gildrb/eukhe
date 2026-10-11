//! The `radius` gateway provider. Port of `providers/radius.ts`.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_types::pi_ai::{AnyModel, Model};

use super::radius_config::{
    get_radius_models, get_radius_models_from_config, load_radius_gateway_config,
    normalize_radius_gateway_url, DEFAULT_RADIUS_GATEWAY,
};
use super::radius_models::RADIUS_MODELS;
use crate::api::builtin::pi_messages_api;
use crate::auth::oauth::load_radius_oauth;
use crate::auth::{env_api_key_auth, lazy_oauth, Credential, LazyOAuthInput, ProviderAuth};
use crate::models::{
    date_now, ModelsPersistence, ModelsPublication, Provider, RefreshModelsContext,
};
use crate::models_store::ModelsStoreEntry;
use crate::utils::diagnostics::Thrown;

/// Options of [`radius_provider`]: TS `RadiusProviderOptions`.
#[derive(Debug, Clone, Default)]
pub struct RadiusProviderOptions {
    pub id: Option<String>,
    pub name: Option<String>,
    pub gateway: Option<String>,
}

struct RadiusCatalog {
    baseline: Vec<Model>,
    /// Gateway catalog for this account. Radius org owners can disable
    /// models, so once known it replaces the shipped baseline instead of
    /// overlaying it. The baseline only covers the time before any catalog
    /// exists.
    dynamic: Mutex<Option<Vec<Model>>>,
}

impl RadiusCatalog {
    fn models(&self) -> Vec<Model> {
        self.dynamic
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone()
            .unwrap_or_else(|| self.baseline.clone())
    }

    fn set_dynamic(&self, models: Vec<Model>) {
        *self.dynamic.lock().unwrap_or_else(PoisonError::into_inner) = Some(models);
    }
}

fn chat_entries(models: Vec<Model>) -> Vec<AnyModel> {
    models.into_iter().map(AnyModel::Chat).collect()
}

async fn refresh_radius_models(
    id: String,
    gateway: String,
    catalog: Arc<RadiusCatalog>,
    context: RefreshModelsContext,
) -> Result<(), Thrown> {
    let stored = context.stored.clone();
    if let Some(stored) = &stored {
        let restored: Vec<Model> = stored
            .models
            .iter()
            .filter(|model| model.provider() == id)
            .filter_map(|model| match model {
                AnyModel::Chat(model) => Some(model.clone()),
                AnyModel::Image(_) | AnyModel::Classifier(_) => None,
            })
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

    // Import catalogs cached by the pre-ModelsStore Radius implementation.
    if stored.is_none() {
        if let Some(Credential::OAuth(credential)) = &context.credential {
            let legacy = get_radius_models(&id, Some(credential));
            if !legacy.is_empty() {
                let legacy_catalog = Arc::clone(&catalog);
                let persisted = chat_entries(legacy.clone());
                let published = context
                    .publish(ModelsPublication {
                        persist: ModelsPersistence::Write(ModelsStoreEntry {
                            models: persisted,
                            checked_at: Some(date_now()),
                            ..ModelsStoreEntry::default()
                        }),
                        update: Some(Box::new(move || legacy_catalog.set_dynamic(legacy))),
                    })
                    .await?;
                if !published {
                    return Ok(());
                }
            }
        }
    }

    if !context.allow_network || context.signal.aborted() {
        return Ok(());
    }
    let api_key = match &context.credential {
        Some(Credential::OAuth(credential)) => Some(credential.access.clone()),
        Some(Credential::ApiKey(credential)) => credential.key.clone(),
        None => None,
    };
    let config =
        load_radius_gateway_config(&gateway, api_key.as_deref(), Some(&context.signal)).await?;
    if context.signal.aborted() {
        return Ok(());
    }
    let refreshed = get_radius_models_from_config(&id, &config);
    let persisted = chat_entries(refreshed.clone());
    context
        .publish(ModelsPublication {
            persist: ModelsPersistence::Write(ModelsStoreEntry {
                models: persisted,
                checked_at: Some(date_now()),
                ..ModelsStoreEntry::default()
            }),
            update: Some(Box::new(move || catalog.set_dynamic(refreshed))),
        })
        .await?;
    Ok(())
}

/// Radius gateway provider with a persisted, dynamically refreshed catalog.
#[must_use]
pub fn radius_provider(options: RadiusProviderOptions) -> Provider {
    let id = options.id.unwrap_or_else(|| "radius".to_owned());
    let name = options.name.unwrap_or_else(|| "Radius".to_owned());
    let gateway =
        normalize_radius_gateway_url(options.gateway.as_deref().unwrap_or(DEFAULT_RADIUS_GATEWAY));
    let baseline: Vec<Model> = if gateway == normalize_radius_gateway_url(DEFAULT_RADIUS_GATEWAY) {
        RADIUS_MODELS
            .values()
            .map(|model| Model {
                provider: id.clone(),
                ..model.clone()
            })
            .collect()
    } else {
        Vec::new()
    };
    let catalog = Arc::new(RadiusCatalog {
        baseline,
        dynamic: Mutex::new(None),
    });
    let streams = pi_messages_api();
    let models_catalog = Arc::clone(&catalog);
    let refresh_id = id.clone();
    let refresh_gateway = gateway.clone();
    let oauth_name = name.clone();
    let oauth_gateway = gateway;

    Provider {
        id,
        name: name.clone(),
        base_url: None,
        headers: None,
        auth: ProviderAuth {
            api_key: Some(env_api_key_auth("Radius API key", &["RADIUS_API_KEY"])),
            oauth: Some(lazy_oauth(LazyOAuthInput {
                name,
                is_subscription: None,
                login_label: None,
                load: Arc::new(move || {
                    load_radius_oauth(oauth_name.clone(), oauth_gateway.clone())
                }),
            })),
        },
        get_models: Arc::new(move || Ok(models_catalog.models())),
        get_all_models: None,
        refresh_models: Some(Arc::new(move |context| {
            Box::pin(refresh_radius_models(
                refresh_id.clone(),
                refresh_gateway.clone(),
                Arc::clone(&catalog),
                context,
            ))
        })),
        filter_models: None,
        filter_all_models: None,
        stream: streams.stream,
        stream_simple: streams.stream_simple,
        fetch_deferred: None,
        cancel_deferred: None,
        generate_images: None,
        classify: None,
    }
}
