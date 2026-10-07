//! Generated catalog of the `cloudflare-workers-ai` provider. Port of
//! `providers/cloudflare-workers-ai.models.ts`.

use std::sync::LazyLock;

use crate::model_catalog::{
    flatten_chat_model_catalog, flatten_classifier_model_catalog, flatten_image_model_catalog,
    parse_model_groups, ChatModelCatalog, ClassifierModelCatalog, ImageModelCatalog, ModelGroups,
};

static VALUES: LazyLock<ModelGroups> =
    LazyLock::new(|| parse_model_groups(include_str!("data/cloudflare-workers-ai.json")));

pub static CLOUDFLARE_WORKERS_AI_MODELS: LazyLock<ChatModelCatalog> =
    LazyLock::new(|| flatten_chat_model_catalog("cloudflare-workers-ai", &VALUES));

pub static CLOUDFLARE_WORKERS_AI_IMAGE_MODELS: LazyLock<ImageModelCatalog> =
    LazyLock::new(|| flatten_image_model_catalog("cloudflare-workers-ai", &VALUES));

pub static CLOUDFLARE_WORKERS_AI_CLASSIFIER_MODELS: LazyLock<ClassifierModelCatalog> =
    LazyLock::new(|| flatten_classifier_model_catalog("cloudflare-workers-ai", &VALUES));
