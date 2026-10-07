//! Generated catalog of the `moonshotai-cn` provider. Port of
//! `providers/moonshotai-cn.models.ts`.

use std::sync::LazyLock;

use crate::model_catalog::{
    flatten_chat_model_catalog, flatten_classifier_model_catalog, flatten_image_model_catalog,
    parse_model_groups, ChatModelCatalog, ClassifierModelCatalog, ImageModelCatalog, ModelGroups,
};

static VALUES: LazyLock<ModelGroups> =
    LazyLock::new(|| parse_model_groups(include_str!("data/moonshotai-cn.json")));

pub static MOONSHOTAI_CN_MODELS: LazyLock<ChatModelCatalog> =
    LazyLock::new(|| flatten_chat_model_catalog("moonshotai-cn", &VALUES));

pub static MOONSHOTAI_CN_IMAGE_MODELS: LazyLock<ImageModelCatalog> =
    LazyLock::new(|| flatten_image_model_catalog("moonshotai-cn", &VALUES));

pub static MOONSHOTAI_CN_CLASSIFIER_MODELS: LazyLock<ClassifierModelCatalog> =
    LazyLock::new(|| flatten_classifier_model_catalog("moonshotai-cn", &VALUES));
