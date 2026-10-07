//! Generated catalog of the `zai` provider. Port of
//! `providers/zai.models.ts`.

use std::sync::LazyLock;

use crate::model_catalog::{
    flatten_chat_model_catalog, flatten_classifier_model_catalog, flatten_image_model_catalog,
    parse_model_groups, ChatModelCatalog, ClassifierModelCatalog, ImageModelCatalog, ModelGroups,
};

static VALUES: LazyLock<ModelGroups> =
    LazyLock::new(|| parse_model_groups(include_str!("data/zai.json")));

pub static ZAI_MODELS: LazyLock<ChatModelCatalog> =
    LazyLock::new(|| flatten_chat_model_catalog("zai", &VALUES));

pub static ZAI_IMAGE_MODELS: LazyLock<ImageModelCatalog> =
    LazyLock::new(|| flatten_image_model_catalog("zai", &VALUES));

pub static ZAI_CLASSIFIER_MODELS: LazyLock<ClassifierModelCatalog> =
    LazyLock::new(|| flatten_classifier_model_catalog("zai", &VALUES));
