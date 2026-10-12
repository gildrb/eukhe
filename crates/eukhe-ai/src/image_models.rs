//! Compat reads of the generated catalog restricted to image models. Port of
//! `image-models.ts`. New code uses `Models::get_model_of_type` or
//! `providers::all::get_builtin_image_model`.

use std::sync::LazyLock;

use eukhe_types::pi_ai::{ImageModel, IndexMap};

use crate::models_generated::IMAGE_MODELS;

/// Providers with at least one image model, each with its models by id.
static IMAGE_MODELS_BY_PROVIDER: LazyLock<IndexMap<&'static str, IndexMap<String, ImageModel>>> =
    LazyLock::new(|| {
        IMAGE_MODELS
            .iter()
            .filter(|(_, models)| !models.is_empty())
            .map(|(provider, models)| {
                let by_id = models
                    .values()
                    .map(|model| (model.id.clone(), model.clone()))
                    .collect();
                (*provider, by_id)
            })
            .collect()
    });

/// Static catalog read of one image model.
#[must_use]
pub fn get_image_model(provider: &str, model_id: &str) -> Option<ImageModel> {
    IMAGE_MODELS_BY_PROVIDER
        .get(provider)?
        .get(model_id)
        .cloned()
}
