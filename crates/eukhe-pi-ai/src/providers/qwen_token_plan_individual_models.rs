//! Generated catalog of the `qwen-token-plan-individual` provider. Port of
//! `providers/qwen-token-plan-individual.models.ts`.

use std::sync::LazyLock;

use crate::model_catalog::{
    flatten_chat_model_catalog, flatten_classifier_model_catalog, flatten_image_model_catalog,
    parse_model_groups, ChatModelCatalog, ClassifierModelCatalog, ImageModelCatalog, ModelGroups,
};

static VALUES: LazyLock<ModelGroups> =
    LazyLock::new(|| parse_model_groups(include_str!("data/qwen-token-plan-individual.json")));

pub static QWEN_TOKEN_PLAN_INDIVIDUAL_MODELS: LazyLock<ChatModelCatalog> =
    LazyLock::new(|| flatten_chat_model_catalog("qwen-token-plan-individual", &VALUES));

pub static QWEN_TOKEN_PLAN_INDIVIDUAL_IMAGE_MODELS: LazyLock<ImageModelCatalog> =
    LazyLock::new(|| flatten_image_model_catalog("qwen-token-plan-individual", &VALUES));

pub static QWEN_TOKEN_PLAN_INDIVIDUAL_CLASSIFIER_MODELS: LazyLock<ClassifierModelCatalog> =
    LazyLock::new(|| flatten_classifier_model_catalog("qwen-token-plan-individual", &VALUES));
