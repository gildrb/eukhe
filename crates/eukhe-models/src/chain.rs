//! The no-cold-start chain: where the built-in models come from.
//!
//! Port of the TS registry's local catalog layers (`bundled-model-catalog.ts`):
//!
//! 1. packaged bundled snapshot (`models.bundled.json` beside the
//!    executable, strict-parsed and pinned);
//! 2. compiled fallback (the 42 transport tuples + 110 offline Prime
//!    Inference entries compiled into the binary).
//!
//! A user always has models: the chain never touches the network. The
//! bundled asset is part of the install, so its resolution is computed once
//! per catalog instance and served from memory afterwards.
//!
//! The user's local `models.json` takes PRECEDENCE over this catalog; the
//! registry that owns models.json merges custom models over this list.

use std::path::PathBuf;
use std::sync::OnceLock;

use crate::bundled::{load_bundled_models, BundledAssets};
use crate::pinning::PinnedTemplates;
use crate::transports;
use crate::Model;

/// The built-in model catalog: the bundled snapshot, else the compiled
/// fallback.
pub struct ModelCatalog {
    bundled: BundledAssets,
    /// The pinned bundled snapshot, resolved on first use (`None`: the
    /// install has no usable asset and the compiled fallback serves).
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

    /// The built-in models through the no-cold-start chain. Never fails;
    /// never touches the network.
    pub fn models(&self) -> &[Model] {
        self.resolved
            .get_or_init(|| {
                self.bundled.read_models().and_then(|asset| {
                    load_bundled_models(&asset, &PinnedTemplates::from_compiled())
                })
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
    fn compiled_fallback_without_a_bundled_asset() {
        let dir = tempfile::tempdir().unwrap();
        let catalog = ModelCatalog::with_bundled_dir(dir.path().into());
        assert_eq!(
            catalog.models().len(),
            transports::compiled_models().len(),
            "compiled fallback"
        );
    }

    #[test]
    fn bundled_asset_beats_compiled_fallback() {
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(
            dir.path().join("models.bundled.json"),
            models_json(&["bundled-a"]),
        )
        .unwrap();
        let catalog = ModelCatalog::with_bundled_dir(dir.path().into());
        let models = catalog.models();
        assert_eq!(
            models.len(),
            111,
            "1 pinned bundled entry + 110 offline prime-inference entries"
        );
        assert!(models.iter().any(|m| m.id == "bundled-a"));
    }

    #[test]
    fn damaged_bundled_asset_falls_back_to_compiled() {
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(dir.path().join("models.bundled.json"), "{broken").unwrap();
        let catalog = ModelCatalog::with_bundled_dir(dir.path().into());
        assert_eq!(catalog.models().len(), transports::compiled_models().len());
    }
}
