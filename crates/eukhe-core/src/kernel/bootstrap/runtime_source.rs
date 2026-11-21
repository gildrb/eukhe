//! Where the `rlm` sources of this build live: the packaged
//! sidecar layout, then the source-checkout fallback. A missing runtime
//! source is a hard error: there is no registry fallback (the
//! `eukhe-runtime` name is not ours on any package index).

use std::path::{Path, PathBuf};

use anyhow::anyhow;

use super::toolchain::expand_home;

/// Directory of the installed `rlm` sources. The Rust binary
/// ships the same sidecar layout the compiled TS executable uses; an explicit
/// `EUKHE_PACKAGE_DIR` override wins (matching the TS `getPackageDir`).
fn package_dir() -> PathBuf {
    if let Ok(env_dir) = std::env::var("EUKHE_PACKAGE_DIR") {
        if !env_dir.is_empty() {
            return expand_home(&env_dir);
        }
    }
    let exe_dir = std::env::current_exe()
        .ok()
        .and_then(|exe| exe.parent().map(Path::to_path_buf))
        .unwrap_or_else(|| PathBuf::from("."));
    exe_dir
}

/// Every place the runtime source may live, in priority order (present or
/// not, so a miss can name them all): the packaged exe-adjacent sidecar
/// (the TS `runtimeCandidateDirs` bun-binary candidates, `EUKHE_PACKAGE_DIR`
/// included through [`package_dir`]), then the source checkout's
/// `rlm/` — only for a binary running from inside that checkout
/// ([`crate::packages::source_checkout_root`]).
fn runtime_candidate_dirs() -> Vec<PathBuf> {
    let package = package_dir();
    let mut candidates = vec![package.join("rlm"), package.join("dist").join("rlm")];
    candidates.extend(crate::packages::source_checkout_root().map(|root| root.join("rlm")));
    candidates
}

/// The directory of the `rlm` sources this build runs.
///
/// # Errors
///
/// Returns an error naming every place looked at when none holds the
/// runtime.
pub fn resolve_runtime_source_dir() -> anyhow::Result<PathBuf> {
    select_runtime_source_dir(&runtime_candidate_dirs())
}

/// The first candidate holding a runtime `pyproject.toml`, else an
/// actionable error naming every place looked at.
fn select_runtime_source_dir(candidates: &[PathBuf]) -> anyhow::Result<PathBuf> {
    if let Some(found) = candidates
        .iter()
        .find(|candidate| candidate.join("pyproject.toml").exists())
    {
        return Ok(found.clone());
    }
    let looked = candidates
        .iter()
        .map(|candidate| candidate.display().to_string())
        .collect::<Vec<_>>()
        .join(", ");
    Err(anyhow!(
        "the rlm kernel runtime directory was not found (looked in: {looked}); \
         reinstall eukhe so rlm/ ships beside the binary, or set EUKHE_PACKAGE_DIR \
         to the directory that contains it"
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn missing_runtime_source_is_a_hard_error() -> anyhow::Result<()> {
        // Regression: no local runtime used to fall back to installing the
        // bare `eukhe-runtime` name from PyPI (an unclaimed name).
        let temp = tempfile::tempdir()?;
        let packaged = temp.path().join("rlm");
        let checkout = temp.path().join("checkout").join("rlm");
        std::fs::create_dir_all(&packaged)?;
        let error = select_runtime_source_dir(&[packaged.clone(), checkout.clone()])
            .expect_err("no runtime source must not resolve");
        assert_eq!(
            error.to_string(),
            format!(
                "the rlm kernel runtime directory was not found (looked in: {}, {}); \
                 reinstall eukhe so rlm/ ships beside the binary, or set \
                 EUKHE_PACKAGE_DIR to the directory that contains it",
                packaged.display(),
                checkout.display()
            )
        );
        Ok(())
    }
}
