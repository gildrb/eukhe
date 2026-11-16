//! Compiles this build's identity: `EUKHE_VERSION`, the product version,
//! and `EUKHE_BUILD_ID`, the version plus the source it was built from,
//! so two builds of other sources (a stale daemon and the client that
//! should replace it) never read as the same build. `src/identity.rs`
//! holds the rules.
//!
//! The version is `EUKHE_RELEASE_VERSION` when the release workflow sets
//! it (a release of the workspace's series), else the workspace version
//! with `-dev`.
//!
//! The source comes from, in order:
//! 1. `EUKHE_BUILD_COMMIT` when set and non-empty: builds whose source has
//!    no `.git` (the Nix flake passes `self.rev`/`self.dirtyRev`) and the
//!    release workflow (the commit it releases). A Nix `dirtyRev`
//!    (`<rev>-dirty`) adds a hash of the build inputs (below).
//! 2. `git` in this checkout (no network): `HEAD`, plus `.dirty.<hash>`
//!    when the build inputs differ from it, the hash of their changes
//!    (`git diff HEAD` and the untracked files among them).
//! 3. Neither: `src.<hash>`, a hash of the build inputs.
//!
//! The build inputs are the files cargo compiles from: [`INPUTS`] (the
//! workspace manifest, lockfile and toolchain, and `crates/`),
//! without `target` and `node_modules` dirs. The script reruns when one
//! of them changes, so each changed build gets its own id; a release (one
//! commit, one version) always gets the same id.

#[path = "src/identity.rs"]
#[allow(dead_code)] // the crate's tests use what the build script does not
mod identity;

use std::path::{Path, PathBuf};
use std::process::Command;

use identity::{build_id, product_version, Digest, Source};

/// The explicit commit override (see the module docs).
const COMMIT_ENV: &str = "EUKHE_BUILD_COMMIT";
/// The release version the release workflow builds.
const RELEASE_ENV: &str = "EUKHE_RELEASE_VERSION";
/// The suffix Nix's `self.dirtyRev` carries.
const NIX_DIRTY_SUFFIX: &str = "-dirty";
/// The build inputs, relative to the workspace root.
const INPUTS: [&str; 4] = ["Cargo.toml", "Cargo.lock", "rust-toolchain.toml", "crates"];
/// Directories under the inputs that hold no build input.
const SKIPPED_DIRS: [&str; 2] = ["target", "node_modules"];

fn main() {
    println!("cargo:rerun-if-env-changed={COMMIT_ENV}");
    println!("cargo:rerun-if-env-changed={RELEASE_ENV}");
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let release = std::env::var(RELEASE_ENV)
        .ok()
        .filter(|value| !value.is_empty());
    let version = product_version(env!("CARGO_PKG_VERSION"), release.as_deref())
        .unwrap_or_else(|error| panic!("{error}"));
    let env_commit = std::env::var(COMMIT_ENV)
        .ok()
        .map(|value| value.trim().to_string())
        .filter(|value| !value.is_empty());
    let id = match origin(env_commit, &root) {
        Origin::EnvCommit(commit) => build_id(&version, &Source::Commit(&commit)),
        Origin::NixDirty(rev) => build_id(
            &version,
            &Source::Changed {
                commit: &rev,
                digest: files_digest(&root),
            },
        ),
        Origin::Git(GitState::Clean { head }) => build_id(&version, &Source::Commit(&head)),
        Origin::Git(GitState::Changed { head, digest }) => build_id(
            &version,
            &Source::Changed {
                commit: &head,
                digest,
            },
        ),
        Origin::Files => build_id(
            &version,
            &Source::Files {
                digest: files_digest(&root),
            },
        ),
    };
    println!("cargo:rustc-env=EUKHE_VERSION={version}");
    println!("cargo:rustc-env=EUKHE_BUILD_ID={id}");
}

/// Where this build's source comes from (see the module docs).
enum Origin {
    /// `EUKHE_BUILD_COMMIT`, a commit as it is.
    EnvCommit(String),
    /// `EUKHE_BUILD_COMMIT` of a Nix `dirtyRev`: the commit before `-dirty`.
    NixDirty(String),
    /// The checkout's git state.
    Git(GitState),
    /// No commit known: the build inputs themselves.
    Files,
}

/// The checkout's `HEAD`, and the hash of the build inputs' changes when
/// they differ from it.
enum GitState {
    Clean { head: String },
    Changed { head: String, digest: u64 },
}

/// The origin of this build: `env_commit` (trimmed, non-empty) when set,
/// else git in the checkout under `root`, else the files.
fn origin(env_commit: Option<String>, root: &Path) -> Origin {
    match env_commit {
        Some(commit) => match commit.strip_suffix(NIX_DIRTY_SUFFIX) {
            Some(rev) => Origin::NixDirty(rev.to_owned()),
            None => Origin::EnvCommit(commit),
        },
        None => git_source(root).map_or(Origin::Files, Origin::Git),
    }
}

/// The git state of the checkout holding the workspace; `None` when git or
/// the repository is unavailable.
fn git_source(root: &Path) -> Option<GitState> {
    let top = PathBuf::from(git_text(root, &["rev-parse", "--show-toplevel"])?);
    let head = git_text(&top, &["rev-parse", "HEAD"])?;
    watch_git_state(&top);
    let tracked = [&["ls-files", "-z", "--"][..], &INPUTS].concat();
    for path in nul_separated(&git_bytes(&top, &tracked)?) {
        watch(&top.join(path));
    }
    let diff = [
        &[
            "--no-optional-locks",
            "diff",
            "HEAD",
            "--binary",
            "--no-ext-diff",
            "--no-textconv",
            "--",
        ][..],
        &INPUTS,
    ]
    .concat();
    let changes = git_bytes(&top, &diff)?;
    let others = [
        &["ls-files", "-z", "--others", "--exclude-standard", "--"][..],
        &INPUTS,
    ]
    .concat();
    let mut untracked = nul_separated(&git_bytes(&top, &others)?);
    untracked.sort_unstable();
    if changes.is_empty() && untracked.is_empty() {
        return Some(GitState::Clean { head });
    }
    let digest = untracked
        .into_iter()
        .fold(Digest::new().update(&changes), |digest, path| {
            let file = top.join(&path);
            watch(&file);
            digest
                .update(path.as_bytes())
                // A file removed after listing is no longer a build input.
                .update(&std::fs::read(&file).unwrap_or_default())
        });
    Some(GitState::Changed {
        head,
        digest: digest.finish(),
    })
}

/// A hash of every build input file (path and content, in path order),
/// each watched.
fn files_digest(root: &Path) -> u64 {
    let mut files = INPUTS
        .iter()
        .flat_map(|input| collect_files(root, Path::new(input)))
        .collect::<Vec<_>>();
    files.sort_unstable();
    files
        .into_iter()
        .fold(Digest::new(), |digest, relative| {
            let file = root.join(&relative);
            watch(&file);
            digest
                .update(relative.to_string_lossy().as_bytes())
                // A file removed after listing is no longer a build input.
                .update(&std::fs::read(&file).unwrap_or_default())
        })
        .finish()
}

/// The files under `root/relative` (a file or a directory), relative to
/// `root`, skipping [`SKIPPED_DIRS`].
fn collect_files(root: &Path, relative: &Path) -> Vec<PathBuf> {
    let path = root.join(relative);
    if path.is_file() {
        return vec![relative.to_path_buf()];
    }
    let Ok(entries) = std::fs::read_dir(&path) else {
        return Vec::new();
    };
    entries
        .flatten()
        .flat_map(|entry| {
            let name = entry.file_name();
            let child = entry.path();
            if SKIPPED_DIRS.iter().any(|dir| name == *dir) && child.is_dir() {
                Vec::new()
            } else {
                collect_files(root, &relative.join(name))
            }
        })
        .collect()
}

/// Rerun when the commit may have moved: `HEAD`, the branch ref it points
/// at (loose or packed), and the index.
fn watch_git_state(top: &Path) {
    let branch = git_text(top, &["symbolic-ref", "-q", "HEAD"]);
    let watched = ["HEAD", "index", "packed-refs"]
        .map(str::to_owned)
        .into_iter()
        .chain(branch);
    for name in watched {
        if let Some(path) = git_text(top, &["rev-parse", "--git-path", &name]) {
            watch(&top.join(path));
        }
    }
}

/// Rerun when `path` changes. Only existing files are watched (cargo
/// reruns on every build for a missing one), and only paths a cargo
/// directive can carry (no newline).
fn watch(path: &Path) {
    let shown = path.display().to_string();
    if path.exists() && !shown.contains('\n') {
        println!("cargo:rerun-if-changed={shown}");
    }
}

fn nul_separated(bytes: &[u8]) -> Vec<String> {
    bytes
        .split(|byte| *byte == 0)
        .filter(|path| !path.is_empty())
        .map(|path| String::from_utf8_lossy(path).into_owned())
        .collect()
}

/// One git command's trimmed stdout, run in `dir`; `None` when git is
/// missing or the command fails.
fn git_text(dir: &Path, args: &[&str]) -> Option<String> {
    let stdout = String::from_utf8(git_bytes(dir, args)?).ok()?;
    Some(stdout.trim().to_string())
}

/// One git command's stdout, run in `dir`; `None` when git is missing or
/// the command fails.
fn git_bytes(dir: &Path, args: &[&str]) -> Option<Vec<u8>> {
    let output = Command::new("git")
        .arg("-C")
        .arg(dir)
        .args(args)
        .output()
        .ok()?;
    output.status.success().then_some(output.stdout)
}
