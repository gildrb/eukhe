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
//! Without a bundled snapshot it is the compiled catalog. With a damaged
//! bundled snapshot it is also the compiled catalog, and the catalog keeps
//! the reason ([`ModelCatalog::bundled_fallback`]). A user always has
//! models, and the catalog never touches the network. The bundled asset is
//! part of the install, so its resolution is computed once per catalog
//! instance and served from memory afterwards.
//!
//! The user's local `models.json` takes PRECEDENCE over this catalog; the
//! registry that owns models.json merges custom models over this list.

use std::path::PathBuf;
use std::sync::OnceLock;

use crate::bundled::{
    load_bundled_models, BundledAssets, BundledCatalogFallback, BundledModelsDefect,
};
use crate::effective::effective_catalog;
use crate::pinning::PinnedTemplates;
use crate::transports;
use crate::Model;

/// The built-in model catalog: the union of the bundled snapshot and the
/// compiled catalog.
pub struct ModelCatalog {
    bundled: BundledAssets,
    /// The resolution, computed on first use.
    resolved: OnceLock<Resolution>,
}

/// Which models the catalog serves.
enum Resolution {
    /// The install has no bundled snapshot. The compiled catalog serves.
    Compiled,
    /// The union of the bundled snapshot and the compiled catalog.
    Union(Vec<Model>),
    /// The bundled snapshot is damaged. The compiled catalog serves.
    Fallback(BundledCatalogFallback),
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
        match self.resolution() {
            Resolution::Union(models) => models,
            Resolution::Compiled | Resolution::Fallback(_) => transports::compiled_models(),
        }
    }

    /// Why the compiled catalog serves in place of the install's bundled
    /// snapshot. `None` when the snapshot is in use or the install has none.
    #[must_use]
    pub fn bundled_fallback(&self) -> Option<&BundledCatalogFallback> {
        match self.resolution() {
            Resolution::Fallback(fallback) => Some(fallback),
            Resolution::Compiled | Resolution::Union(_) => None,
        }
    }

    fn resolution(&self) -> &Resolution {
        self.resolved.get_or_init(|| {
            let loaded = match self.bundled.read_models() {
                Ok(None) => return Resolution::Compiled,
                Ok(Some(asset)) => load_bundled_models(&asset, &PinnedTemplates::from_compiled()),
                Err(error) => Err(BundledModelsDefect::Unreadable(error.to_string())),
            };
            match loaded {
                Ok(bundled) => {
                    Resolution::Union(effective_catalog(bundled, transports::compiled_models()))
                }
                Err(defect) => {
                    let fallback = BundledCatalogFallback {
                        path: self.bundled.models_path(),
                        defect,
                    };
                    tracing::warn!("{fallback}");
                    Resolution::Fallback(fallback)
                }
            }
        })
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
    fn damaged_bundled_asset_serves_the_compiled_catalog_and_keeps_the_reason() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("models.bundled.json");
        std::fs::write(&path, "{broken").unwrap();
        let json_error = serde_json::from_str::<serde_json::Value>("{broken").unwrap_err();
        let catalog = ModelCatalog::with_bundled_dir(dir.path().into());
        assert_eq!(catalog.models(), transports::compiled_models());
        assert_eq!(
            catalog.bundled_fallback(),
            Some(&BundledCatalogFallback {
                path,
                defect: BundledModelsDefect::InvalidJson(json_error.to_string()),
            })
        );
    }

    #[test]
    fn a_missing_bundled_asset_has_no_fallback_reason() {
        let dir = tempfile::tempdir().unwrap();
        let catalog = ModelCatalog::with_bundled_dir(dir.path().into());
        assert_eq!(catalog.models(), transports::compiled_models());
        assert_eq!(catalog.bundled_fallback(), None);
    }

    #[test]
    fn a_usable_bundled_asset_has_no_fallback_reason() {
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(
            dir.path().join("models.bundled.json"),
            models_json(&["bundled-a"]),
        )
        .unwrap();
        let catalog = ModelCatalog::with_bundled_dir(dir.path().into());
        assert_eq!(catalog.bundled_fallback(), None);
    }
}
