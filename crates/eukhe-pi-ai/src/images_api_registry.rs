//! Global image-generation API registry of the old global API. Port of
//! `images-api-registry.ts`.

use std::sync::{Arc, LazyLock, Mutex, MutexGuard, PoisonError};

use eukhe_types::pi_ai::{AssistantImages, ImageApi, ImageModel, ImagesContext, IndexMap};
use futures::future::BoxFuture;

use crate::types::ProviderImagesOptions;
use crate::utils::diagnostics::{ErrorObject, Thrown};

/// An image-generation function: TS `ImagesApiFunction` / `ImagesFunction`.
pub type ImagesApiFunction = Arc<
    dyn Fn(
            &ImageModel,
            &ImagesContext,
            ProviderImagesOptions,
        ) -> BoxFuture<'static, Result<AssistantImages, Thrown>>
        + Send
        + Sync,
>;

/// A registered image API: TS `ImagesApiProvider`.
#[derive(Clone)]
pub struct ImagesApiProvider {
    pub api: ImageApi,
    pub generate_images: ImagesApiFunction,
}

struct RegisteredImagesApiProvider {
    provider: ImagesApiProvider,
    // TS records the registering source; no image API reads it back.
    #[allow(dead_code)]
    source_id: Option<String>,
}

static IMAGES_API_PROVIDER_REGISTRY: LazyLock<
    Mutex<IndexMap<String, RegisteredImagesApiProvider>>,
> = LazyLock::new(|| Mutex::new(IndexMap::new()));

fn registry() -> MutexGuard<'static, IndexMap<String, RegisteredImagesApiProvider>> {
    IMAGES_API_PROVIDER_REGISTRY
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
}

fn wrap_generate_images(api: ImageApi, generate_images: ImagesApiFunction) -> ImagesApiFunction {
    Arc::new(move |model, context, options| {
        if model.api != api {
            let error =
                ErrorObject::new(format!("Mismatched api: {} expected {api}", model.api)).thrown();
            return Box::pin(async move { Err(error) });
        }
        generate_images(model, context, options)
    })
}

/// Registers (or replaces) the implementation for `provider.api`.
pub fn register_images_api_provider(provider: ImagesApiProvider, source_id: Option<String>) {
    let api = provider.api.clone();
    let wrapped = ImagesApiProvider {
        api: api.clone(),
        generate_images: wrap_generate_images(api.clone(), provider.generate_images),
    };
    registry().insert(
        api,
        RegisteredImagesApiProvider {
            provider: wrapped,
            source_id,
        },
    );
}

/// The registered implementation for `api`.
#[must_use]
pub fn get_images_api_provider(api: &str) -> Option<ImagesApiProvider> {
    registry().get(api).map(|entry| entry.provider.clone())
}
