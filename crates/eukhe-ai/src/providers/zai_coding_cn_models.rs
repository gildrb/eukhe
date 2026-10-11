//! Generated catalog of the `zai-coding-cn` provider. Port of
//! `providers/zai-coding-cn.models.ts`.

use std::sync::LazyLock;

use crate::model_catalog::{
    flatten_chat_model_catalog, flatten_classifier_model_catalog, flatten_image_model_catalog,
    parse_model_groups, ChatModelCatalog, ClassifierModelCatalog, ImageModelCatalog, ModelGroups,
};

static VALUES: LazyLock<ModelGroups> =
    LazyLock::new(|| parse_model_groups(include_str!("data/zai-coding-cn.json")));

pub static ZAI_CODING_CN_MODELS: LazyLock<ChatModelCatalog> =
    LazyLock::new(|| flatten_chat_model_catalog("zai-coding-cn", &VALUES));

pub static ZAI_CODING_CN_IMAGE_MODELS: LazyLock<ImageModelCatalog> =
    LazyLock::new(|| flatten_image_model_catalog("zai-coding-cn", &VALUES));

pub static ZAI_CODING_CN_CLASSIFIER_MODELS: LazyLock<ClassifierModelCatalog> =
    LazyLock::new(|| flatten_classifier_model_catalog("zai-coding-cn", &VALUES));
