//! Generated catalog of the `xiaomi-token-plan-ams` provider. Port of
//! `providers/xiaomi-token-plan-ams.models.ts`.

use std::sync::LazyLock;

use crate::model_catalog::{
    flatten_chat_model_catalog, flatten_classifier_model_catalog, flatten_image_model_catalog,
    parse_model_groups, ChatModelCatalog, ClassifierModelCatalog, ImageModelCatalog, ModelGroups,
};

static VALUES: LazyLock<ModelGroups> =
    LazyLock::new(|| parse_model_groups(include_str!("data/xiaomi-token-plan-ams.json")));

pub static XIAOMI_TOKEN_PLAN_AMS_MODELS: LazyLock<ChatModelCatalog> =
    LazyLock::new(|| flatten_chat_model_catalog("xiaomi-token-plan-ams", &VALUES));

pub static XIAOMI_TOKEN_PLAN_AMS_IMAGE_MODELS: LazyLock<ImageModelCatalog> =
    LazyLock::new(|| flatten_image_model_catalog("xiaomi-token-plan-ams", &VALUES));

pub static XIAOMI_TOKEN_PLAN_AMS_CLASSIFIER_MODELS: LazyLock<ClassifierModelCatalog> =
    LazyLock::new(|| flatten_classifier_model_catalog("xiaomi-token-plan-ams", &VALUES));
