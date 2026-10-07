//! Registers the built-in image APIs into the global images registry. Port
//! of `providers/images/register-builtins.ts`.

use std::sync::{Arc, Once};

use eukhe_types::pi_ai::{AssistantImages, ImageModel, ImagesContext, ImagesStopReason};
use futures::future::BoxFuture;

use crate::api::builtin::load_image_api;
use crate::images_api_registry::{register_images_api_provider, ImagesApiProvider};
use crate::types::ProviderImagesOptions;
use crate::utils::diagnostics::Thrown;
use crate::utils::now_ms;

fn create_lazy_load_error_images(model: &ImageModel, error: &Thrown) -> AssistantImages {
    AssistantImages {
        api: model.api.clone(),
        provider: model.provider.clone(),
        model: model.id.clone(),
        output: Vec::new(),
        response_id: None,
        usage: None,
        stop_reason: ImagesStopReason::Error,
        error_message: Some(error.to_string()),
        timestamp: now_ms(),
    }
}

/// TS `generateImagesOpenRouter`: loads the `openrouter-images` module on
/// use; a load failure becomes an error result.
#[must_use]
pub fn generate_images_openrouter(
    model: &ImageModel,
    context: &ImagesContext,
    options: ProviderImagesOptions,
) -> BoxFuture<'static, Result<AssistantImages, Thrown>> {
    match load_image_api("openrouter-images") {
        Ok(module) => {
            let images = (module.generate_images)(model, context, options.images);
            Box::pin(async move { Ok(images.await) })
        }
        Err(error) => {
            let result = create_lazy_load_error_images(model, &error);
            Box::pin(async move { Ok(result) })
        }
    }
}

/// Registers the built-in image API implementations.
pub fn register_builtin_images_api_providers() {
    register_images_api_provider(
        ImagesApiProvider {
            api: "openrouter-images".to_owned(),
            generate_images: Arc::new(generate_images_openrouter),
        },
        None,
    );
}

static REGISTERED: Once = Once::new();

/// The TS module side effect: registers the built-ins once per process.
pub(crate) fn ensure_builtin_images_api_providers() {
    REGISTERED.call_once(register_builtin_images_api_providers);
}
