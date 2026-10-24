//! The rules of this build's identity, as pure functions: `build.rs`
//! includes this file (`#[path]`) and applies them to what it finds (the
//! environment, git, the source files); the crate's tests check them.

use eukhe_bend::rules::semver::{series, Series};

/// Commit hashes are shortened to this many characters.
pub(crate) const SHORT_COMMIT_LEN: usize = 12;

/// The suffix of a build's version that is no release.
pub(crate) const DEV_SUFFIX: &str = "-dev";

/// The product version of a build of workspace version `workspace`
/// (`X.Y.Z`, the series `X.Y`). A release build names its release
/// (`release`, from `EUKHE_RELEASE_VERSION`): a version of the
/// workspace's series (`eukhe-next-version` computes it; the rule runs as
/// its compiled Bend model, `eukhe_bend::rules::semver::series`). Any
/// other build is `<workspace>-dev`, so it never claims a release.
pub(crate) fn product_version(workspace: &str, release: Option<&str>) -> Result<String, String> {
    let Some(release) = release else {
        return Ok(format!("{workspace}{DEV_SUFFIX}"));
    };
    match series(workspace, release) {
        Ok(Series::Of) => Ok(release.to_string()),
        Ok(Series::NoVersion) => Err(format!(
            "EUKHE_RELEASE_VERSION {release:?} is not a version major.minor.patch"
        )),
        Ok(Series::Other) => Err(format!(
            "EUKHE_RELEASE_VERSION {release} is not of the series of the workspace version {workspace}"
        )),
        Err(error) => Err(format!(
            "EUKHE_RELEASE_VERSION {release:?} against the workspace version {workspace}: {error}"
        )),
    }
}

/// What a build was compiled from.
pub(crate) enum Source<'a> {
    /// A commit, unchanged.
    Commit(&'a str),
    /// A commit with changes; `digest` hashes the changes.
    Changed { commit: &'a str, digest: u64 },
    /// No known commit; `digest` hashes the source files.
    Files { digest: u64 },
}

/// The build id: `<version>+<commit>`, `<version>+<commit>.dirty.<digest>`
/// or `<version>+src.<digest>` (`<commit>` is 12 hex characters, `<digest>`
/// 16). Builds of other inputs get other ids, and a build of the same
/// inputs (a release: one commit, one version) gets the same one.
pub(crate) fn build_id(version: &str, source: &Source<'_>) -> String {
    match source {
        Source::Commit(commit) => format!("{version}+{}", short_commit(commit)),
        Source::Changed { commit, digest } => {
            format!("{version}+{}.dirty.{digest:016x}", short_commit(commit))
        }
        Source::Files { digest } => format!("{version}+src.{digest:016x}"),
    }
}

/// The first [`SHORT_COMMIT_LEN`] characters of a commit hash (the whole
/// value when shorter).
fn short_commit(rev: &str) -> &str {
    rev.get(..SHORT_COMMIT_LEN).unwrap_or(rev)
}

/// A 64-bit FNV-1a hash of a sequence of byte strings. Each one is hashed
/// with its length first, so `["ab", "c"]` and `["a", "bc"]` differ. It
/// tells builds apart; it is no defense against a crafted collision.
pub(crate) struct Digest(u64);

impl Digest {
    pub(crate) fn new() -> Self {
        Self(0xcbf2_9ce4_8422_2325)
    }

    pub(crate) fn update(&mut self, bytes: &[u8]) {
        let length = u64::try_from(bytes.len()).unwrap_or(u64::MAX);
        for byte in length.to_le_bytes().iter().chain(bytes) {
            self.0 ^= u64::from(*byte);
            self.0 = self.0.wrapping_mul(0x0000_0100_0000_01b3);
        }
    }

    pub(crate) fn finish(&self) -> u64 {
        self.0
    }
}
