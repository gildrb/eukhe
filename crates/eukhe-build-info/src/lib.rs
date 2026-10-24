//! This build's identity. [`VERSION`] is the product version: the release
//! a release build names, else the workspace version with `-dev`.
//! [`BUILD_ID`] adds the source it was built from (see `build.rs`), so a
//! daemon left running by another build of the same version reads as
//! another build and is replaced.
//!
//! A leaf crate on purpose: its build script reruns when a build input
//! changes, so only the crates that report or compare the identity
//! recompile with it.

#[cfg(test)]
mod identity;

/// The supervisor `runtime.buildId` prefix, a macro so `concat!` can use it.
macro_rules! daemon_build_id_prefix {
    () => {
        "eukhe-daemon-rs-"
    };
}

/// This build's product version: `X.Y.P` for a release build, else
/// `X.Y.Z-dev` (the workspace version).
pub const VERSION: &str = env!("EUKHE_VERSION");

/// This build: `<version>+<commit>`, `<version>+<commit>.dirty.<hash>`
/// (the build inputs changed since the commit) or `<version>+src.<hash>`
/// (no commit known); `<commit>` is 12 hex characters, `<hash>` 16.
pub const BUILD_ID: &str = env!("EUKHE_BUILD_ID");

/// The prefix of a supervisor's hello `runtime.buildId`; the build identity
/// (older daemons: the bare version) follows.
pub const DAEMON_BUILD_ID_PREFIX: &str = daemon_build_id_prefix!();

/// The `runtime.buildId` this build's supervisor reports in its hello.
pub const DAEMON_BUILD_ID: &str = concat!(daemon_build_id_prefix!(), env!("EUKHE_BUILD_ID"));

#[cfg(test)]
mod tests {
    use super::identity::{build_id, product_version, Digest, Source};
    use super::VERSION;

    fn digest(parts: &[&[u8]]) -> u64 {
        let mut digest = Digest::new();
        for part in parts {
            digest.update(part);
        }
        digest.finish()
    }

    #[test]
    fn a_local_build_never_claims_a_release() {
        assert_eq!(
            product_version("0.10.0", None),
            Ok("0.10.0-dev".to_string())
        );
        assert_eq!(VERSION, concat!(env!("CARGO_PKG_VERSION"), "-dev"));
    }

    /// The release check runs as the compiled Bend model
    /// (`laws/semver.bend` pins the rule): one answer of each kind.
    #[test]
    fn a_release_build_names_a_release_of_the_workspace_series() {
        let checked =
            ["0.10.7", "0.11.0", "0.10.07"].map(|release| product_version("0.10.0", Some(release)));
        assert_eq!(
            checked,
            [
                Ok("0.10.7".to_string()),
                Err("EUKHE_RELEASE_VERSION 0.11.0 is not of the series of the workspace version 0.10.0".to_string()),
                Err("EUKHE_RELEASE_VERSION \"0.10.07\" is not a version major.minor.patch".to_string()),
            ]
        );
    }

    // Regression: two dirty builds of one commit both read `<commit>.dirty`,
    // and every build without git the bare version, so the stale-daemon
    // check took a daemon of other sources for this build.
    #[test]
    fn builds_of_other_inputs_get_other_ids_and_equal_inputs_the_same() {
        let commit = "0123456789abcdef0123456789abcdef01234567";
        let ids = [
            build_id("0.10.3", &Source::Commit(commit)),
            build_id("0.10.3", &Source::Commit(commit)),
            build_id("0.10.0-dev", &Source::Commit(commit)),
            build_id(
                "0.10.0-dev",
                &Source::Changed {
                    commit,
                    digest: digest(&[b"diff one"]),
                },
            ),
            build_id(
                "0.10.0-dev",
                &Source::Changed {
                    commit,
                    digest: digest(&[b"diff two"]),
                },
            ),
            build_id(
                "0.10.0-dev",
                &Source::Files {
                    digest: digest(&[b"a.rs", b"fn a() {}"]),
                },
            ),
            build_id(
                "0.10.0-dev",
                &Source::Files {
                    digest: digest(&[b"a.rs", b"fn b() {}"]),
                },
            ),
        ];
        assert_eq!(
            ids,
            [
                "0.10.3+0123456789ab",
                "0.10.3+0123456789ab",
                "0.10.0-dev+0123456789ab",
                "0.10.0-dev+0123456789ab.dirty.55224e0637d0b8be",
                "0.10.0-dev+0123456789ab.dirty.8e219505c7292b64",
                "0.10.0-dev+src.c66425faecd753c8",
                "0.10.0-dev+src.b127a04b6cc1bc03",
            ]
            .map(String::from)
        );
    }

    #[test]
    fn the_digest_separates_its_parts() {
        assert_ne!(digest(&[b"ab", b"c"]), digest(&[b"a", b"bc"]));
    }
}
