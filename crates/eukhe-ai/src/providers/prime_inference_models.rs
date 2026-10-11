//! Compiled offline catalog of the `prime-inference` provider (eukhe
//! addition): the public Prime Inference routes the client ships for
//! onboarding before the first credentialed fetch. Private ids (internal/,
//! dev/, ids containing `:`) never ship compiled.

use std::sync::LazyLock;

use crate::model_catalog::{
    flatten_chat_model_catalog, parse_model_groups, ChatModelCatalog, ModelGroups,
};

static VALUES: LazyLock<ModelGroups> =
    LazyLock::new(|| parse_model_groups(include_str!("data/prime-inference.json")));

pub static PRIME_INFERENCE_MODELS: LazyLock<ChatModelCatalog> =
    LazyLock::new(|| flatten_chat_model_catalog("prime-inference", &VALUES));
