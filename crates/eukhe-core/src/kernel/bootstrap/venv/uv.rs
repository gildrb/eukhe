//! The uv discovery concern (moved with its concern): the PATH executable
//! search and the `ensure_uv` resolution with its install guidance.

use super::{anyhow, home_dir, Path, PathBuf};

/// Package-manager installs only: a piped install script runs unreviewed
/// remote code.
const UV_INSTALL_GUIDANCE: &str = "install it with your package manager \
     (`nix profile install nixpkgs#uv`, `brew install uv`) \
     or download a release from https://github.com/astral-sh/uv/releases and verify it \
     against the release's published sha256 checksum";

fn find_executable(name: &str) -> Option<PathBuf> {
    let path_value = std::env::var("PATH").ok()?;
    for dir in std::env::split_paths(&path_value) {
        if dir.as_os_str().is_empty() {
            continue;
        }
        let full_path = dir.join(name);
        if full_path.is_file() && is_executable(&full_path) {
            return Some(full_path);
        }
    }
    None
}

fn is_executable(path: &Path) -> bool {
    crate::platform::perms::is_executable(path)
}

/// Find `uv` on PATH or at `~/.local/bin/uv`. Returns `Err` with install
/// guidance when missing: the Rust binary never auto-installs (the TS
/// interactive confirm belongs to the CLI layer).
pub(crate) fn ensure_uv() -> anyhow::Result<String> {
    if let Some(from_path) = find_executable("uv") {
        return Ok(from_path.to_string_lossy().to_string());
    }
    let local_uv = home_dir().join(".local").join("bin").join("uv");
    if is_executable(&local_uv) {
        return Ok(local_uv.to_string_lossy().to_string());
    }
    Err(anyhow!(
        "uv is required to set up the Python kernel; {UV_INSTALL_GUIDANCE}"
    ))
}
