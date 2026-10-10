//! The plugins-catalog snapshot source for resolution: the packaged bundled
//! snapshot (`<package-dir>/mcp-services.bundled.json`, generated at build
//! time and shipped beside the executable), else nothing (the compiled
//! linear/notion fallback still resolves). Read-only and fail-closed; the
//! catalog is never fetched.

use super::catalog_schema::{parse_plugins_catalog, PluginsCatalog};

/// The packaged bundled snapshot (`EUKHE_PACKAGE_DIR` override included),
/// read through the models catalog's asset reader (same package-dir
/// resolution). Every read or parse error yields `None` — the caller keeps
/// the compiled built-ins and never surfaces the error into a session.
pub fn bundled_plugins_snapshot() -> Option<PluginsCatalog> {
    let assets = eukhe_models::bundled::BundledAssets::at_package_root();
    let raw = assets.read_mcp_services()?;
    parse_plugins_catalog(raw.as_bytes()).ok()
}
