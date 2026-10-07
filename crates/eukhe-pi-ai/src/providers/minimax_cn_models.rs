//! Generated catalog of the `minimax-cn` provider. Port of
//! `providers/minimax-cn.models.ts`.

use std::sync::LazyLock;

use crate::model_catalog::{
    flatten_chat_model_catalog, flatten_classifier_model_catalog, flatten_image_model_catalog,
    parse_model_groups, ChatModelCatalog, ClassifierModelCatalog, ImageModelCatalog, ModelGroups,
};

static VALUES: LazyLock<ModelGroups> =
    LazyLock::new(|| parse_model_groups(include_str!("data/minimax-cn.json")));

pub static MINIMAX_CN_MODELS: LazyLock<ChatModelCatalog> =
    LazyLock::new(|| flatten_chat_model_catalog("minimax-cn", &VALUES));

pub static MINIMAX_CN_IMAGE_MODELS: LazyLock<ImageModelCatalog> =
    LazyLock::new(|| flatten_image_model_catalog("minimax-cn", &VALUES));

pub static MINIMAX_CN_CLASSIFIER_MODELS: LazyLock<ClassifierModelCatalog> =
    LazyLock::new(|| flatten_classifier_model_catalog("minimax-cn", &VALUES));
