//! Global image generation of the old global API. Port of `images.ts`.

use std::sync::Arc;

use eukhe_types::pi_ai::{AssistantImages, ImageModel, ImagesContext};

use crate::images_api_registry::get_images_api_provider;
use crate::providers::images::register_builtins::ensure_builtin_images_api_providers;
use crate::types::ProviderImagesOptions;
use crate::utils::diagnostics::{ErrorObject, Thrown};

/// Global image generation dispatched on `model.api` through the images API
/// registry. Auth must be passed explicitly via `options.images.request.api_key`;
/// prefer `Models::generate_images`, which resolves provider auth.
///
/// # Errors
///
/// "No API provider registered for api: …" for an unregistered api, or the
/// registered implementation's failure.
pub async fn generate_images(
    model: &ImageModel,
    context: &ImagesContext,
    options: ProviderImagesOptions,
) -> Result<AssistantImages, Thrown> {
    ensure_builtin_images_api_providers();
    let provider = get_images_api_provider(&model.api).ok_or_else(|| -> Thrown {
        Arc::new(ErrorObject::new(format!(
            "No API provider registered for api: {}",
            model.api
        )))
    })?;
    (provider.generate_images)(model, context, options).await
}
