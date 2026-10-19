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
//! workspace manifest, lockfile and toolchain, `crates/`, `vendor/`),
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
const INPUTS: [&str; 5] = [
    "Cargo.toml",
    "Cargo.lock",
    "rust-toolchain.toml",
    "crates",
    "vendor",
];
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
    let id = match env_commit {
        Some(commit) => match commit.strip_suffix(NIX_DIRTY_SUFFIX) {
            Some(rev) => build_id(
                &version,
                &Source::Changed {
                    commit: rev,
                    digest: files_digest(&root),
                },
            ),
            None => build_id(&version, &Source::Commit(&commit)),
        },
        None => match git_source(&root) {
            Some((commit, Some(digest))) => build_id(
                &version,
                &Source::Changed {
                    commit: &commit,
                    digest,
                },
            ),
            Some((commit, None)) => build_id(&version, &Source::Commit(&commit)),
            None => build_id(
                &version,
                &Source::Files {
                    digest: files_digest(&root),
                },
            ),
        },
    };
    println!("cargo:rustc-env=EUKHE_VERSION={version}");
    println!("cargo:rustc-env=EUKHE_BUILD_ID={id}");
}

/// `HEAD` of the checkout holding the workspace and, when the build
/// inputs differ from it, the hash of their changes; `None` when git or
/// the repository is unavailable.
fn git_source(root: &Path) -> Option<(String, Option<u64>)> {
    let top = PathBuf::from(git_text(root, &["rev-parse", "--show-toplevel"])?);
    let head = git_text(&top, &["rev-parse", "HEAD"])?;
    watch_git_state(&top);
    let mut tracked = vec!["ls-files", "-z", "--"];
    tracked.extend(INPUTS);
    for path in nul_separated(&git_bytes(&top, &tracked)?) {
        watch(&top.join(path));
    }
    let mut diff = vec![
        "--no-optional-locks",
        "diff",
        "HEAD",
        "--binary",
        "--no-ext-diff",
        "--no-textconv",
        "--",
    ];
    diff.extend(INPUTS);
    let changes = git_bytes(&top, &diff)?;
    let mut untracked = vec!["ls-files", "-z", "--others", "--exclude-standard", "--"];
    untracked.extend(INPUTS);
    let mut untracked = nul_separated(&git_bytes(&top, &untracked)?);
    untracked.sort_unstable();
    if changes.is_empty() && untracked.is_empty() {
        return Some((head, None));
    }
    let mut digest = Digest::new();
    digest.update(&changes);
    for path in untracked {
        let file = top.join(&path);
        watch(&file);
        digest.update(path.as_bytes());
        digest.update(&std::fs::read(&file).unwrap_or_default());
    }
    Some((head, Some(digest.finish())))
}

/// A hash of every build input file (path and content, in path order),
/// each watched.
fn files_digest(root: &Path) -> u64 {
    let mut files = Vec::new();
    for input in INPUTS {
        collect_files(root, Path::new(input), &mut files);
    }
    files.sort_unstable();
    let mut digest = Digest::new();
    for relative in files {
        let file = root.join(&relative);
        watch(&file);
        digest.update(relative.to_string_lossy().as_bytes());
        digest.update(&std::fs::read(&file).unwrap_or_default());
    }
    digest.finish()
}

/// The files under `root/relative` (a file or a directory), relative to
/// `root`, skipping [`SKIPPED_DIRS`].
fn collect_files(root: &Path, relative: &Path, files: &mut Vec<PathBuf>) {
    let path = root.join(relative);
    if path.is_file() {
        files.push(relative.to_path_buf());
        return;
    }
    let Ok(entries) = std::fs::read_dir(&path) else {
        return;
    };
    for entry in entries.flatten() {
        let name = entry.file_name();
        let skipped = SKIPPED_DIRS.iter().any(|dir| name == *dir);
        if !(skipped && entry.path().is_dir()) {
            collect_files(root, &relative.join(name), files);
        }
    }
}

/// Rerun when the commit may have moved: `HEAD`, the branch ref it points
/// at (loose or packed), and the index.
fn watch_git_state(top: &Path) {
    let mut watched = vec![
        "HEAD".to_string(),
        "index".to_string(),
        "packed-refs".to_string(),
    ];
    if let Some(branch) = git_text(top, &["symbolic-ref", "-q", "HEAD"]) {
        watched.push(branch);
    }
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
