//! Generated catalog of the `vercel-ai-gateway` provider. Port of
//! `providers/vercel-ai-gateway.models.ts`.

use std::sync::LazyLock;

use crate::model_catalog::{
    flatten_chat_model_catalog, flatten_classifier_model_catalog, flatten_image_model_catalog,
    parse_model_groups, ChatModelCatalog, ClassifierModelCatalog, ImageModelCatalog, ModelGroups,
};

static VALUES: LazyLock<ModelGroups> =
    LazyLock::new(|| parse_model_groups(include_str!("data/vercel-ai-gateway.json")));

pub static VERCEL_AI_GATEWAY_MODELS: LazyLock<ChatModelCatalog> =
    LazyLock::new(|| flatten_chat_model_catalog("vercel-ai-gateway", &VALUES));

pub static VERCEL_AI_GATEWAY_IMAGE_MODELS: LazyLock<ImageModelCatalog> =
    LazyLock::new(|| flatten_image_model_catalog("vercel-ai-gateway", &VALUES));

pub static VERCEL_AI_GATEWAY_CLASSIFIER_MODELS: LazyLock<ClassifierModelCatalog> =
    LazyLock::new(|| flatten_classifier_model_catalog("vercel-ai-gateway", &VALUES));
