//! Generated catalog of the `opencode-go` provider. Port of
//! `providers/opencode-go.models.ts`.

use std::sync::LazyLock;

use crate::model_catalog::{
    flatten_chat_model_catalog, flatten_classifier_model_catalog, flatten_image_model_catalog,
    parse_model_groups, ChatModelCatalog, ClassifierModelCatalog, ImageModelCatalog, ModelGroups,
};

static VALUES: LazyLock<ModelGroups> =
    LazyLock::new(|| parse_model_groups(include_str!("data/opencode-go.json")));

pub static OPENCODE_GO_MODELS: LazyLock<ChatModelCatalog> =
    LazyLock::new(|| flatten_chat_model_catalog("opencode-go", &VALUES));

pub static OPENCODE_GO_IMAGE_MODELS: LazyLock<ImageModelCatalog> =
    LazyLock::new(|| flatten_image_model_catalog("opencode-go", &VALUES));

pub static OPENCODE_GO_CLASSIFIER_MODELS: LazyLock<ClassifierModelCatalog> =
    LazyLock::new(|| flatten_classifier_model_catalog("opencode-go", &VALUES));
