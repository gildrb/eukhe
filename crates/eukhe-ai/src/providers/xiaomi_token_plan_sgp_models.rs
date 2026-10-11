//! Generated catalog of the `xiaomi-token-plan-sgp` provider. Port of
//! `providers/xiaomi-token-plan-sgp.models.ts`.

use std::sync::LazyLock;

use crate::model_catalog::{
    flatten_chat_model_catalog, flatten_classifier_model_catalog, flatten_image_model_catalog,
    parse_model_groups, ChatModelCatalog, ClassifierModelCatalog, ImageModelCatalog, ModelGroups,
};

static VALUES: LazyLock<ModelGroups> =
    LazyLock::new(|| parse_model_groups(include_str!("data/xiaomi-token-plan-sgp.json")));

pub static XIAOMI_TOKEN_PLAN_SGP_MODELS: LazyLock<ChatModelCatalog> =
    LazyLock::new(|| flatten_chat_model_catalog("xiaomi-token-plan-sgp", &VALUES));

pub static XIAOMI_TOKEN_PLAN_SGP_IMAGE_MODELS: LazyLock<ImageModelCatalog> =
    LazyLock::new(|| flatten_image_model_catalog("xiaomi-token-plan-sgp", &VALUES));

pub static XIAOMI_TOKEN_PLAN_SGP_CLASSIFIER_MODELS: LazyLock<ClassifierModelCatalog> =
    LazyLock::new(|| flatten_classifier_model_catalog("xiaomi-token-plan-sgp", &VALUES));
