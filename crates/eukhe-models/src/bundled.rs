//! Bundled snapshot loading: one of the two sources of the built-in
//! catalog (the compiled catalog is the other; [`crate::ModelCatalog`]
//! serves their union).
//!
//! Ported from `bundled-model-catalog.ts`: the packaged assets
//! (`models.bundled.json` + `mcp-services.bundled.json`) are generated at
//! build time and shipped beside the executable. The models asset is parsed
//! with the strict schema and pinned to compiled transports. When the asset
//! is there but damaged, the compiled model definitions serve. The loader
//! keeps the reason ([`BundledCatalogFallback`]), so the user can see it.

use std::path::{Path, PathBuf};

use crate::pinning::{pin_catalog_models, NoSupportedModels, PinnedTemplates};
use crate::prime_inference::is_private_prime_inference_model_id;
use crate::schema::{parse_model_catalog, InvalidEntries, ModelCatalogError};
use crate::Model;

/// The packaged models asset file name.
pub const PACKAGED_MODEL_CATALOG_FILE: &str = "models.bundled.json";

/// The packaged MCP services asset file name (parsed by the plugins lane).
pub const PACKAGED_MCP_CATALOG_FILE: &str = "mcp-services.bundled.json";

/// Location of the bundled catalog assets.
#[derive(Debug, Clone)]
pub struct BundledAssets {
    dir: PathBuf,
}

impl BundledAssets {
    /// The package directory: `EUKHE_PACKAGE_DIR` when set (the wire-internal
    /// identifier, kept for TS parity), else the executable's directory.
    pub fn package_dir() -> PathBuf {
        std::env::var_os("EUKHE_PACKAGE_DIR")
            .filter(|value| !value.is_empty())
            .map_or_else(
                || {
                    std::env::current_exe()
                        .ok()
                        .and_then(|exe| exe.parent().map(Path::to_path_buf))
                        .unwrap_or_default()
                },
                PathBuf::from,
            )
    }

    /// Assets at the package root ([`BundledAssets::package_dir`]).
    #[must_use]
    pub fn at_package_root() -> Self {
        Self {
            dir: Self::package_dir(),
        }
    }

    /// Assets at an explicit directory (tests, staged installs).
    pub fn from_dir(dir: impl Into<PathBuf>) -> Self {
        Self { dir: dir.into() }
    }

    /// The directory the assets are read from.
    #[must_use]
    pub fn dir(&self) -> &Path {
        &self.dir
    }

    /// The path of the bundled models snapshot.
    #[must_use]
    pub fn models_path(&self) -> PathBuf {
        self.dir.join(PACKAGED_MODEL_CATALOG_FILE)
    }

    /// Raw text of the bundled models snapshot. `Ok(None)`: the install has
    /// no snapshot, and the compiled catalog serves.
    ///
    /// # Errors
    ///
    /// Fails when the file is there but cannot be read.
    pub fn read_models(&self) -> std::io::Result<Option<String>> {
        match std::fs::read_to_string(self.models_path()) {
            Ok(text) => Ok(Some(text)),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(None),
            Err(error) => Err(error),
        }
    }

    /// Raw bytes of the bundled MCP services snapshot (the plugins lane owns
    /// parsing it).
    #[must_use]
    pub fn read_mcp_services(&self) -> Option<String> {
        std::fs::read_to_string(self.dir.join(PACKAGED_MCP_CATALOG_FILE)).ok()
    }
}

/// Why the install's bundled models snapshot is not used.
#[derive(Debug, thiserror::Error)]
pub enum BundledModelsDefect {
    /// The file is there, but it cannot be read.
    #[error("it cannot be read: {0}")]
    Unreadable(#[source] std::io::Error),
    /// The file is not valid JSON.
    #[error("it is not valid JSON: {0}")]
    InvalidJson(#[source] serde_json::Error),
    /// The file does not match the model catalog schema.
    #[error("it is not a valid model catalog: {0}")]
    InvalidCatalog(#[source] ModelCatalogError),
    /// No entry of the file pins to a transport of this client.
    #[error("its models do not pin to a transport of this client: {0}")]
    Unpinnable(#[source] NoSupportedModels),
}

/// The compiled catalog serves in place of a damaged bundled snapshot.
/// This is the reason, for the user to see.
#[derive(Debug, thiserror::Error)]
#[error(
    "the bundled model catalog {} is not used, because {defect}; the compiled catalog serves in its place",
    path.display()
)]
pub struct BundledCatalogFallback {
    /// The path of the damaged snapshot.
    pub path: PathBuf,
    /// What is wrong with the snapshot.
    #[source]
    pub defect: BundledModelsDefect,
}

/// Load and pin the bundled models snapshot. The same steps as TS
/// `loadBundledModels`.
///
/// # Errors
///
/// Fails when the asset is not valid JSON, does not match the catalog
/// schema, or has no entry that pins to a compiled transport.
pub fn load_bundled_models(
    asset: &str,
    templates: &PinnedTemplates,
) -> Result<Vec<Model>, BundledModelsDefect> {
    let payload: serde_json::Value =
        serde_json::from_str(asset).map_err(BundledModelsDefect::InvalidJson)?;
    let catalog = parse_model_catalog(&payload, InvalidEntries::Reject)
        .map_err(BundledModelsDefect::InvalidCatalog)?;
    let mut models = pin_catalog_models(catalog.models.clone(), templates)
        .map_err(BundledModelsDefect::Unpinnable)?;
    // Pinning skips Prime Inference (that domain ships compiled). Keep the
    // asset's public entries on the compiled Prime Inference transport.
    for model in catalog.models {
        if model.provider != "prime-inference"
            || model.api != "openai-completions"
            || model.base_url != crate::prime_inference::PRIME_INFERENCE_BASE_URL
            || is_private_prime_inference_model_id(&model.id)
        {
            continue;
        }
        models.push(model);
    }
    Ok(models)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::transports;
    use serde_json::json;

    fn asset(models: impl AsRef<[serde_json::Value]>) -> String {
        serde_json::to_string_pretty(&json!({"schemaVersion": 1, "models": models.as_ref()}))
            .unwrap()
    }

    fn entry(id: &str, provider: &str) -> serde_json::Value {
        let compiled = transports::compiled_models();
        let template = compiled
            .iter()
            .find(|m| m.provider == provider)
            .expect("compiled provider");
        json!({
            "id": id,
            "name": id,
            "api": template.api,
            "provider": template.provider,
            "baseUrl": template.base_url,
            "reasoning": false,
            "input": ["text"],
            "cost": {"input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0},
            "contextWindow": 128_000,
            "maxTokens": 4_096,
        })
    }

    #[test]
    fn loads_and_pins_only_the_asset_entries() {
        let asset = asset(vec![entry("m1", "anthropic"), entry("m2", "openai")]);
        let models =
            load_bundled_models(&asset, &PinnedTemplates::from_compiled()).expect("loaded");
        let keys: Vec<(&str, &str)> = models
            .iter()
            .map(|model| (model.provider.as_str(), model.id.as_str()))
            .collect();
        assert_eq!(keys, [("anthropic", "m1"), ("openai", "m2")]);
    }

    #[test]
    fn damaged_asset_reports_its_defect() {
        let not_json = "{\"not json";
        let json_error = serde_json::from_str::<serde_json::Value>(not_json).unwrap_err();
        assert_eq!(
            load_bundled_models(not_json, &PinnedTemplates::from_compiled())
                .unwrap_err()
                .to_string(),
            BundledModelsDefect::InvalidJson(json_error).to_string()
        );
        let damaged = asset(vec![json!({"id": "broken"})]);
        let schema_error = parse_model_catalog(
            &serde_json::from_str(&damaged).unwrap(),
            InvalidEntries::Reject,
        )
        .unwrap_err();
        assert_eq!(
            load_bundled_models(&damaged, &PinnedTemplates::from_compiled())
                .unwrap_err()
                .to_string(),
            BundledModelsDefect::InvalidCatalog(schema_error).to_string()
        );
    }

    #[test]
    fn from_dir_reads_assets() {
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(dir.path().join(PACKAGED_MCP_CATALOG_FILE), "{}").unwrap();
        let assets = BundledAssets::from_dir(dir.path());
        assert!(assets.read_mcp_services().is_some());
        assert_eq!(assets.read_models().unwrap(), None);
        assert_eq!(assets.dir(), dir.path());
    }
}
