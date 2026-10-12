//! Compiles this build's identity into `EUKHE_BUILD_ID`: the product
//! version plus the source commit, so two builds of the same version (a
//! stale daemon and the client that should replace it) never read as the
//! same build.
//!
//! The commit comes from, in order:
//! 1. `EUKHE_BUILD_COMMIT` when set and non-empty: builds whose source has
//!    no `.git` (the Nix flake passes `self.rev`/`self.dirtyRev`) or whose
//!    tree the build itself modifies (the release workflow stamps the
//!    version into `Cargo.toml` before building).
//! 2. `git` in this checkout (no network): `HEAD`, plus a `.dirty` marker
//!    when tracked files differ from it. The marker is best effort: it is
//!    recomputed when `HEAD`, the branch ref, or the index changes.
//! 3. Neither: the identity is the bare version, and every such build of
//!    that version reads as the same build (a warning says so).

use std::path::{Path, PathBuf};
use std::process::Command;

/// The explicit commit override (see the module docs).
const COMMIT_ENV: &str = "EUKHE_BUILD_COMMIT";
/// Commit hashes are shortened to this many characters.
const SHORT_COMMIT_LEN: usize = 12;
/// The marker appended to the commit of a modified working tree.
const DIRTY_MARKER: &str = ".dirty";
/// The suffix Nix's `self.dirtyRev` carries.
const NIX_DIRTY_SUFFIX: &str = "-dirty";

fn main() {
    println!("cargo:rerun-if-env-changed={COMMIT_ENV}");
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let commit = commit_from_env().or_else(|| commit_from_git(&manifest_dir));
    let version = env!("CARGO_PKG_VERSION");
    let build_id = if let Some(commit) = commit {
        format!("{version}+{commit}")
    } else {
        println!(
            "cargo:warning=no source commit ({COMMIT_ENV} unset, git unavailable): the build id is the bare version {version}"
        );
        version.to_string()
    };
    println!("cargo:rustc-env=EUKHE_BUILD_ID={build_id}");
}

/// The commit `EUKHE_BUILD_COMMIT` names, shortened; a Nix `dirtyRev`
/// (`<rev>-dirty`) keeps its dirty marker.
fn commit_from_env() -> Option<String> {
    let value = std::env::var(COMMIT_ENV).ok()?;
    let value = value.trim();
    if value.is_empty() {
        return None;
    }
    Some(match value.strip_suffix(NIX_DIRTY_SUFFIX) {
        Some(rev) => format!("{}{DIRTY_MARKER}", short_commit(rev)),
        None => short_commit(value).to_string(),
    })
}

/// `HEAD` of the checkout holding this crate, with the dirty marker; `None`
/// when git or the repository is unavailable.
fn commit_from_git(manifest_dir: &Path) -> Option<String> {
    let head = git(manifest_dir, &["rev-parse", "HEAD"])?;
    watch_git_state(manifest_dir);
    let dirty = git(
        manifest_dir,
        &[
            "--no-optional-locks",
            "status",
            "--porcelain",
            "--untracked-files=no",
        ],
    )
    .is_some_and(|status| !status.is_empty());
    let commit = short_commit(&head);
    Some(if dirty {
        format!("{commit}{DIRTY_MARKER}")
    } else {
        commit.to_string()
    })
}

/// Rerun when the commit or the dirty state may have moved: `HEAD`, the
/// branch ref it points at (loose or packed), and the index. Only existing
/// files are watched: cargo reruns on every build for a missing one.
fn watch_git_state(manifest_dir: &Path) {
    let mut watched = vec![
        "HEAD".to_string(),
        "index".to_string(),
        "packed-refs".to_string(),
    ];
    if let Some(branch) = git(manifest_dir, &["symbolic-ref", "-q", "HEAD"]) {
        watched.push(branch);
    }
    for name in watched {
        let Some(path) = git(manifest_dir, &["rev-parse", "--git-path", &name]) else {
            continue;
        };
        let path = manifest_dir.join(path);
        if path.exists() {
            println!("cargo:rerun-if-changed={}", path.display());
        }
    }
}

/// The first [`SHORT_COMMIT_LEN`] characters of a commit hash (the whole
/// value when shorter).
fn short_commit(rev: &str) -> &str {
    rev.get(..SHORT_COMMIT_LEN).unwrap_or(rev)
}

/// One git command's trimmed stdout, run in `dir`; `None` when git is
/// missing or the command fails.
fn git(dir: &Path, args: &[&str]) -> Option<String> {
    let output = Command::new("git")
        .arg("-C")
        .arg(dir)
        .args(args)
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let stdout = String::from_utf8(output.stdout).ok()?;
    Some(stdout.trim().to_string())
}
