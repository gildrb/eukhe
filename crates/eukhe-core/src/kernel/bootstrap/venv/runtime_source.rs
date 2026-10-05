//! The runtime source concern (moved with its concern): the packaged
//! sidecar layout, the source-checkout fallback, and the content identity
//! that invalidates an existing venv on any runtime change. A missing
//! runtime source is a hard error: there is no registry fallback (the
//! `eukhe-runtime` name is not ours on any package index).

use anyhow::{anyhow, Context};

use super::{expand_home, Digest, Path, PathBuf};

/// The hash-locked requirements of the kernel venv, exported from the
/// runtime's `uv.lock` (`make runtime-lock`): every distribution the
/// bootstrap installs besides the runtime itself, pinned with hashes.
pub(super) const RUNTIME_LOCK_FILE: &str = "requirements-kernel.txt";

/// Directory of the installed `eukhe-runtime` sources. The Rust binary
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
/// `eukhe-runtime/` — only for a binary running from inside that checkout
/// ([`crate::packages::source_checkout_root`]).
fn runtime_candidate_dirs() -> Vec<PathBuf> {
    let package = package_dir();
    let mut candidates = vec![
        package.join("eukhe-runtime"),
        package.join("dist").join("eukhe-runtime"),
    ];
    candidates
        .extend(crate::packages::source_checkout_root().map(|root| root.join("eukhe-runtime")));
    candidates
}

pub(super) fn resolve_runtime_source_dir() -> anyhow::Result<PathBuf> {
    select_runtime_source_dir(&runtime_candidate_dirs())
}

/// The first candidate holding a runtime `pyproject.toml`, else an
/// actionable error naming every place looked at.
pub(super) fn select_runtime_source_dir(candidates: &[PathBuf]) -> anyhow::Result<PathBuf> {
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
        "the eukhe-runtime kernel runtime directory was not found (looked in: {looked}); \
         reinstall eukhe so eukhe-runtime/ ships beside the binary, or set EUKHE_PACKAGE_DIR \
         to the directory that contains it"
    ))
}

/// Content identity of the runtime: a hash of every `rlm/*.py` file, the
/// packaged machine library under `src/rlm/machines` (wheel package data:
/// machine changes are runtime changes), `pyproject.toml`, and the
/// hash-locked kernel requirements, so any runtime or lock change
/// invalidates an existing venv.
///
/// # Errors
///
/// Returns an error when no runtime source directory exists or hashing it
/// fails (unreadable or missing runtime files, a missing lock file).
pub fn resolve_runtime_identity() -> anyhow::Result<String> {
    hash_runtime_source(&resolve_runtime_source_dir()?)
}

pub(super) fn hash_runtime_source(source_dir: &Path) -> anyhow::Result<String> {
    let lock = source_dir.join(RUNTIME_LOCK_FILE);
    if !lock.is_file() {
        return Err(anyhow!(
            "the kernel runtime at {} has no {RUNTIME_LOCK_FILE}; reinstall eukhe (a source \
             checkout regenerates it with `make runtime-lock`)",
            source_dir.display()
        ));
    }
    let rlm_dir = source_dir.join("src").join("rlm");
    let mut files = vec![source_dir.join("pyproject.toml"), lock];
    collect_python_files(&rlm_dir, &mut files)
        .with_context(|| format!("cannot hash runtime source at {}", source_dir.display()))?;
    collect_package_data_files(&rlm_dir.join("machines"), &mut files)?;
    files.sort();
    let mut hasher = sha2::Sha256::new();
    for file in &files {
        let relative = file.strip_prefix(source_dir)?;
        hasher.update(relative.to_string_lossy().as_bytes());
        hasher.update([0]);
        hasher.update(&std::fs::read(file)?);
        hasher.update([0]);
    }
    Ok(format!("sha256:{:x}", hasher.finalize()))
}

pub(super) fn collect_python_files(dir: &Path, files: &mut Vec<PathBuf>) -> anyhow::Result<()> {
    for entry in std::fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        if path.is_dir() {
            collect_python_files(&path, files)?;
        } else if path.extension().and_then(|e| e.to_str()) == Some("py") {
            files.push(path);
        }
    }
    Ok(())
}

/// Collect every file under the packaged machine library (`src/rlm/machines`,
/// any extension: the wheel ships the MACHINE.md files as package data), so
/// machine changes invalidate an existing venv exactly like a `.py` change.
fn collect_package_data_files(dir: &Path, files: &mut Vec<PathBuf>) -> anyhow::Result<()> {
    if !dir.is_dir() {
        return Ok(()); // a runtime payload without a machine library is legal
    }
    for entry in std::fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        if path.is_dir() {
            collect_package_data_files(&path, files)?;
        } else {
            files.push(path);
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn runtime_fixture(temp: &std::path::Path, machine_body: &str) -> anyhow::Result<()> {
        let rlm = temp.join("src").join("rlm");
        std::fs::create_dir_all(&rlm)?;
        std::fs::write(
            rlm.join("factory.py"),
            "X = 1
",
        )?;
        let machines = rlm.join("machines").join("review-sweep");
        std::fs::create_dir_all(&machines)?;
        std::fs::write(machines.join("MACHINE.md"), machine_body)?;
        std::fs::write(
            temp.join("pyproject.toml"),
            "[project]
",
        )?;
        std::fs::write(
            temp.join(RUNTIME_LOCK_FILE),
            "dill==0.4.1 --hash=sha256:aa\n",
        )?;
        Ok(())
    }

    #[test]
    fn missing_runtime_source_is_a_hard_error() -> anyhow::Result<()> {
        // Regression: no local runtime used to fall back to installing the
        // bare `eukhe-runtime` name from PyPI (an unclaimed name).
        let temp = tempfile::tempdir()?;
        let packaged = temp.path().join("eukhe-runtime");
        let checkout = temp.path().join("checkout").join("eukhe-runtime");
        std::fs::create_dir_all(&packaged)?;
        let error = select_runtime_source_dir(&[packaged.clone(), checkout.clone()])
            .expect_err("no runtime source must not resolve");
        assert_eq!(
            error.to_string(),
            format!(
                "the eukhe-runtime kernel runtime directory was not found (looked in: {}, {}); \
                 reinstall eukhe so eukhe-runtime/ ships beside the binary, or set \
                 EUKHE_PACKAGE_DIR to the directory that contains it",
                packaged.display(),
                checkout.display()
            )
        );
        Ok(())
    }

    #[test]
    fn runtime_without_its_lock_is_a_hard_error() -> anyhow::Result<()> {
        let temp = tempfile::tempdir()?;
        runtime_fixture(temp.path(), "---\n")?;
        std::fs::remove_file(temp.path().join(RUNTIME_LOCK_FILE))?;
        let error = hash_runtime_source(temp.path()).expect_err("an unlocked runtime must fail");
        assert_eq!(
            error.to_string(),
            format!(
                "the kernel runtime at {} has no {RUNTIME_LOCK_FILE}; reinstall eukhe (a source \
                 checkout regenerates it with `make runtime-lock`)",
                temp.path().display()
            )
        );
        Ok(())
    }

    #[test]
    fn lock_changes_invalidate_the_runtime_identity() -> anyhow::Result<()> {
        let temp = tempfile::tempdir()?;
        runtime_fixture(temp.path(), "---\n")?;
        let before = hash_runtime_source(temp.path())?;
        std::fs::write(
            temp.path().join(RUNTIME_LOCK_FILE),
            "dill==0.4.2 --hash=sha256:bb\n",
        )?;
        assert_ne!(before, hash_runtime_source(temp.path())?);
        Ok(())
    }

    #[test]
    fn machine_library_changes_invalidate_the_runtime_identity() -> anyhow::Result<()> {
        let temp = tempfile::tempdir()?;
        runtime_fixture(
            temp.path(),
            "---
name: review-sweep
",
        )?;
        let before = hash_runtime_source(temp.path())?;
        runtime_fixture(
            temp.path(),
            "---
name: review-sweep
version: 2
",
        )?;
        let after = hash_runtime_source(temp.path())?;
        assert_ne!(before, after, "a machine file change is a runtime change");

        // A runtime without the machine library still hashes cleanly.
        std::fs::remove_dir_all(temp.path().join("src").join("rlm").join("machines"))?;
        let bare = hash_runtime_source(temp.path())?;
        assert_ne!(bare, after);
        Ok(())
    }
}
