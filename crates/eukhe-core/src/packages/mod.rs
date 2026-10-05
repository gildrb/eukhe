//! Package manager subsystem: install/remove/list/update of `npm:`, git, and
//! local-dir package sources against the settings store, plus the
//! configured-npm/git child-process flows.
//!
//! Session resource resolution lives here as well: `PackageManager::resolve`
//! produces the ranked skill/prompt/theme paths sessions consume.
//!
//! Non-goals: loading/executing session-resource code and Eukhe
//! self-updates.

mod git;
mod manager;
mod npm;
mod process;
pub(crate) mod resolve;
pub mod resource_config;
mod source;
mod update;

#[cfg(test)]
mod tests;

pub use manager::{
    BundledSkillsDir, ConfiguredPackage, PackageManager, PackageManagerOptions, PackageUpdate,
    ProgressAction, ProgressEvent, ProgressEventKind, UserOrProject,
};
pub use resolve::{
    MetadataSource, MissingSourceAction, PathMetadata, ResolvedPaths, ResolvedResource,
    ResourceOrigin, ResourceType,
};
pub use source::{
    parse_git_url, GitSource, LocalSource, NpmSource, ParsedSource, SourceDefect, SourceParseError,
    SourcePart, SourceScope,
};

use std::fmt::Write as _;
use std::path::PathBuf;

/// The TS `CONFIG_DIR_NAME` (project-local settings/packages root).
pub use crate::settings::CONFIG_DIR_NAME;

/// Network probe timeout for npm/git operations (10s).
pub(crate) use npm::NETWORK_TIMEOUT_MS;

/// True when `EUKHE_OFFLINE` disables all package network operations.
pub(crate) fn is_offline_mode_enabled() -> bool {
    std::env::var("EUKHE_OFFLINE").is_ok_and(|value| {
        value == "1" || value.eq_ignore_ascii_case("true") || value.eq_ignore_ascii_case("yes")
    })
}

/// The package directory: `EUKHE_PACKAGE_DIR` wins (matching the TS
/// `getPackageDir` override), then the directory of the executable (the
/// packaged bun-binary layout).
pub(crate) fn package_dir() -> PathBuf {
    if let Ok(env_dir) = std::env::var("EUKHE_PACKAGE_DIR") {
        if !env_dir.is_empty() {
            return expand_tilde(&env_dir);
        }
    }
    std::env::current_exe()
        .ok()
        .and_then(|exe| exe.parent().map(std::path::Path::to_path_buf))
        .unwrap_or_else(|| PathBuf::from("."))
}

/// The bundled docs directory (TS `getDocsPath`): `<package dir>/docs`.
#[must_use]
pub fn docs_path() -> PathBuf {
    package_dir().join("docs")
}

fn expand_tilde(path: &str) -> PathBuf {
    if path == "~" {
        return home_dir();
    }
    if let Some(rest) = path.strip_prefix("~/") {
        return home_dir().join(rest);
    }
    PathBuf::from(path)
}

fn home_dir() -> PathBuf {
    eukhe_types::platform::home_dir().unwrap_or_else(|| PathBuf::from("/"))
}

/// The workspace root of the source checkout this binary was built from
/// (`<root>/crates/eukhe-core`, baked in at compile time), shared by every
/// package-dir resolution that falls back to the source-checkout layout.
/// Only `Some` while the running executable lives inside that checkout
/// (`target/…`): a shipped or copied binary never consults the build
/// machine's path, which anyone could create on the user's machine.
pub(crate) fn source_checkout_root() -> Option<&'static std::path::Path> {
    static ROOT: std::sync::LazyLock<Option<PathBuf>> = std::sync::LazyLock::new(|| {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .ancestors()
            .nth(2)?;
        checkout_containing(root, &std::env::current_exe().ok()?)
    });
    ROOT.as_deref()
}

/// `root` (canonical) when `exe` resolves to a path inside it.
fn checkout_containing(root: &std::path::Path, exe: &std::path::Path) -> Option<PathBuf> {
    let root = std::fs::canonicalize(root).ok()?;
    std::fs::canonicalize(exe)
        .ok()?
        .starts_with(&root)
        .then_some(root)
}

/// The directory of built-in skills shipped with the package (TS
/// `getBundledSkillsDir`): `skills/` next to the executable (the packaged
/// layout), falling back to the workspace `skills/` for a binary running
/// from inside its source checkout ([`source_checkout_root`]; TS keeps
/// built-in skills at the package root next to `src/`).
pub(crate) fn get_bundled_skills_dir() -> PathBuf {
    let packaged = package_dir().join("skills");
    if packaged.is_dir() {
        return packaged;
    }
    if let Some(root) = source_checkout_root() {
        let source_checkout = root.join("skills");
        if source_checkout.is_dir() {
            return source_checkout;
        }
    }
    packaged
}

/// Root every resolve-only temporary package install lives under.
pub(crate) fn temporary_root() -> PathBuf {
    std::env::temp_dir().join("pi-extensions")
}

/// Stable temporary directory for resolve-only package installs (the hash
/// keys on prefix+suffix so the same source always maps to one checkout).
pub(crate) fn temporary_dir(prefix: &str, suffix: Option<&str>) -> PathBuf {
    use sha2::{Digest, Sha256};

    let mut hasher = Sha256::new();
    hasher.update(format!("{prefix}-{}", suffix.unwrap_or_default()).as_bytes());
    let digest = hasher.finalize();
    let hash: String = digest[..4].iter().fold(String::new(), |mut output, byte| {
        let _ = write!(output, "{byte:02x}");
        output
    });
    temporary_root()
        .join(prefix)
        .join(&hash)
        .join(suffix.unwrap_or_default())
}

#[cfg(test)]
pub(crate) mod test_support {
    /// Process-wide env reads and writes (HOME, `EUKHE_OFFLINE`) serialize
    /// through one lock across the packages test modules: parallel test
    /// threads in the same binary otherwise race the process env.
    pub(crate) static ENV_MUTEX: std::sync::Mutex<()> = std::sync::Mutex::new(());
}
