//! Generated catalog of the `qwen-token-plan` provider. Port of
//! `providers/qwen-token-plan.models.ts`.

use std::sync::LazyLock;

use crate::model_catalog::{
    flatten_chat_model_catalog, flatten_classifier_model_catalog, flatten_image_model_catalog,
    parse_model_groups, ChatModelCatalog, ClassifierModelCatalog, ImageModelCatalog, ModelGroups,
};

static VALUES: LazyLock<ModelGroups> =
    LazyLock::new(|| parse_model_groups(include_str!("data/qwen-token-plan.json")));

pub static QWEN_TOKEN_PLAN_MODELS: LazyLock<ChatModelCatalog> =
    LazyLock::new(|| flatten_chat_model_catalog("qwen-token-plan", &VALUES));

pub static QWEN_TOKEN_PLAN_IMAGE_MODELS: LazyLock<ImageModelCatalog> =
    LazyLock::new(|| flatten_image_model_catalog("qwen-token-plan", &VALUES));

pub static QWEN_TOKEN_PLAN_CLASSIFIER_MODELS: LazyLock<ClassifierModelCatalog> =
    LazyLock::new(|| flatten_classifier_model_catalog("qwen-token-plan", &VALUES));
