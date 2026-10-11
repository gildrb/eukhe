//! Generated catalog of the `amazon-bedrock` provider. Port of
//! `providers/amazon-bedrock.models.ts`.

use std::sync::LazyLock;

use crate::model_catalog::{
    flatten_chat_model_catalog, flatten_classifier_model_catalog, flatten_image_model_catalog,
    parse_model_groups, ChatModelCatalog, ClassifierModelCatalog, ImageModelCatalog, ModelGroups,
};

static VALUES: LazyLock<ModelGroups> =
    LazyLock::new(|| parse_model_groups(include_str!("data/amazon-bedrock.json")));

pub static AMAZON_BEDROCK_MODELS: LazyLock<ChatModelCatalog> =
    LazyLock::new(|| flatten_chat_model_catalog("amazon-bedrock", &VALUES));

pub static AMAZON_BEDROCK_IMAGE_MODELS: LazyLock<ImageModelCatalog> =
    LazyLock::new(|| flatten_image_model_catalog("amazon-bedrock", &VALUES));

pub static AMAZON_BEDROCK_CLASSIFIER_MODELS: LazyLock<ClassifierModelCatalog> =
    LazyLock::new(|| flatten_classifier_model_catalog("amazon-bedrock", &VALUES));
