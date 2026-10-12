//! This build's identity. Every build of one workspace version shares the
//! version string; [`BUILD_ID`] adds the source commit (see `build.rs`), so
//! a daemon left running by an earlier build of the same version reads as
//! another build and is replaced.
//!
//! A leaf crate on purpose: its build script reruns on every commit, so only
//! the crates that report or compare the identity recompile with it.

/// The supervisor `runtime.buildId` prefix, a macro so `concat!` can use it.
macro_rules! daemon_build_id_prefix {
    () => {
        "eukhe-daemon-rs-"
    };
}

/// This build: `<version>+<commit>` (`<commit>` is 12 hex characters, with
/// a `.dirty` suffix for a modified tree), or the bare `<version>` when the
/// source commit was unknown at compile time.
pub const BUILD_ID: &str = env!("EUKHE_BUILD_ID");

/// The prefix of a supervisor's hello `runtime.buildId`; the build identity
/// (older daemons: the bare version) follows.
pub const DAEMON_BUILD_ID_PREFIX: &str = daemon_build_id_prefix!();

/// The `runtime.buildId` this build's supervisor reports in its hello.
pub const DAEMON_BUILD_ID: &str = concat!(daemon_build_id_prefix!(), env!("EUKHE_BUILD_ID"));
