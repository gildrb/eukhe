//! Catalog of the `claude-code` provider: the `anthropic` catalog, served
//! through the `claude` CLI.

use std::sync::LazyLock;

use eukhe_types::pi_ai::Model;

use super::anthropic_models::ANTHROPIC_MODELS;
use crate::model_catalog::ChatModelCatalog;

pub static CLAUDE_CODE_MODELS: LazyLock<ChatModelCatalog> = LazyLock::new(|| {
    ANTHROPIC_MODELS
        .iter()
        .map(|(id, model)| {
            (
                id.clone(),
                Model {
                    api: "claude-code".to_owned(),
                    provider: "claude-code".to_owned(),
                    base_url: String::new(),
                    headers: None,
                    compat: None,
                    ..model.clone()
                },
            )
        })
        .collect()
});
