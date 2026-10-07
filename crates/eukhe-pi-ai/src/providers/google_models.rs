//! Generated catalog of the `google` provider. Port of
//! `providers/google.models.ts`.

use std::sync::LazyLock;

use crate::model_catalog::{
    flatten_chat_model_catalog, flatten_classifier_model_catalog, flatten_image_model_catalog,
    parse_model_groups, ChatModelCatalog, ClassifierModelCatalog, ImageModelCatalog, ModelGroups,
};

static VALUES: LazyLock<ModelGroups> =
    LazyLock::new(|| parse_model_groups(include_str!("data/google.json")));

pub static GOOGLE_MODELS: LazyLock<ChatModelCatalog> =
    LazyLock::new(|| flatten_chat_model_catalog("google", &VALUES));

pub static GOOGLE_IMAGE_MODELS: LazyLock<ImageModelCatalog> =
    LazyLock::new(|| flatten_image_model_catalog("google", &VALUES));

pub static GOOGLE_CLASSIFIER_MODELS: LazyLock<ClassifierModelCatalog> =
    LazyLock::new(|| flatten_classifier_model_catalog("google", &VALUES));
