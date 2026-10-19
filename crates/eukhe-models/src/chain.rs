//! The built-in models: where they come from.
//!
//! Two local sources, after the TS registry's local catalog layers
//! (`bundled-model-catalog.ts`):
//!
//! 1. the packaged bundled snapshot (`models.bundled.json` beside the
//!    executable, strict-parsed and pinned);
//! 2. the compiled catalog (the pi-ai tables plus the Prime Inference
//!    entries compiled into the binary).
//!
//! The built-in catalog is their union ([`effective_catalog`]): every
//! model of either source, the bundled entry winning the fields it states.
//! Without a usable bundled snapshot it is the compiled catalog. A user
//! always has models, and the catalog never touches the network. The
//! bundled asset is part of the install, so its resolution is computed
//! once per catalog instance and served from memory afterwards.
//!
//! The user's local `models.json` takes PRECEDENCE over this catalog; the
//! registry that owns models.json merges custom models over this list.

use std::path::PathBuf;
use std::sync::OnceLock;

use crate::bundled::{load_bundled_models, BundledAssets};
use crate::effective::effective_catalog;
use crate::pinning::PinnedTemplates;
use crate::transports;
use crate::Model;

/// The built-in model catalog: the union of the bundled snapshot and the
/// compiled catalog.
pub struct ModelCatalog {
    bundled: BundledAssets,
    /// The union, resolved on first use (`None`: the install has no usable
    /// bundled asset and the compiled catalog serves alone).
    resolved: OnceLock<Option<Vec<Model>>>,
}

impl Default for ModelCatalog {
    fn default() -> Self {
        Self::new()
    }
}

impl ModelCatalog {
    /// The production catalog: bundled assets at the package root.
    #[must_use]
    pub fn new() -> Self {
        Self::from_assets(BundledAssets::at_package_root())
    }

    /// [`ModelCatalog::new`] with an explicit bundled-asset directory
    /// (tests, staged installs).
    #[must_use]
    pub fn with_bundled_dir(bundled_dir: PathBuf) -> Self {
        Self::from_assets(BundledAssets::from_dir(bundled_dir))
    }

    fn from_assets(bundled: BundledAssets) -> Self {
        Self {
            bundled,
            resolved: OnceLock::new(),
        }
    }

    /// The built-in models: the bundled snapshot's union with the compiled
    /// catalog. Never fails; never touches the network.
    pub fn models(&self) -> &[Model] {
        self.resolved
            .get_or_init(|| {
                self.bundled
                    .read_models()
                    .and_then(|asset| {
                        load_bundled_models(&asset, &PinnedTemplates::from_compiled())
                    })
                    .map(|bundled| effective_catalog(bundled, transports::compiled_models()))
            })
            .as_deref()
            .unwrap_or_else(|| transports::compiled_models())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn models_json(ids: &[&str]) -> String {
        let compiled = transports::compiled_models();
        let anthropic = compiled
            .iter()
            .find(|m| m.provider == "anthropic")
            .expect("compiled anthropic");
        let models: Vec<serde_json::Value> = ids
            .iter()
            .map(|id| {
                json!({
                    "id": id,
                    "name": id,
                    "api": anthropic.api,
                    "provider": anthropic.provider,
                    "baseUrl": anthropic.base_url,
                    "reasoning": false,
                    "input": ["text"],
                    "cost": {"input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0},
                    "contextWindow": 128_000,
                    "maxTokens": 4_096,
                })
            })
            .collect();
        serde_json::to_string(&json!({"schemaVersion": 1, "models": models})).unwrap()
    }

    #[test]
    fn compiled_catalog_without_a_bundled_asset() {
        let dir = tempfile::tempdir().unwrap();
        let catalog = ModelCatalog::with_bundled_dir(dir.path().into());
        assert_eq!(catalog.models(), transports::compiled_models());
    }

    #[test]
    fn a_bundled_asset_adds_to_the_compiled_catalog() {
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(
            dir.path().join("models.bundled.json"),
            models_json(&["bundled-a"]),
        )
        .unwrap();
        let catalog = ModelCatalog::with_bundled_dir(dir.path().into());
        let models = catalog.models();
        assert_eq!(models[0].id, "bundled-a");
        assert_eq!(&models[1..], transports::compiled_models());
    }

    /// The pinned catalog snapshot has no Claude Haiku 5.5; the compiled
    /// catalog has it. With that snapshot bundled, the model is still in
    /// the built-in catalog, as the compiled catalog defines it.
    #[test]
    fn a_bundle_without_a_compiled_model_keeps_it() {
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(
            dir.path().join("models.bundled.json"),
            include_str!("../tests/fixtures/catalog.v1.json"),
        )
        .unwrap();
        let haiku = |models: &[Model]| -> Option<Model> {
            models
                .iter()
                .find(|model| model.provider == "anthropic" && model.id == "claude-haiku-5-5")
                .cloned()
        };
        let catalog = ModelCatalog::with_bundled_dir(dir.path().into());
        assert_eq!(
            haiku(catalog.models()),
            haiku(transports::compiled_models())
        );
        assert!(haiku(catalog.models()).is_some());
    }

    #[test]
    fn damaged_bundled_asset_serves_the_compiled_catalog() {
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(dir.path().join("models.bundled.json"), "{broken").unwrap();
        let catalog = ModelCatalog::with_bundled_dir(dir.path().into());
        assert_eq!(catalog.models(), transports::compiled_models());
    }
}
