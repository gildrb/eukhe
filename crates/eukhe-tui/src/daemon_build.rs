//! The order of eukhe builds and the launcher's replacement verdict. A client compares its build with the build of the
//! daemon on its socket, then keeps the daemon or replaces it.
//!
//! A version `X.Y.Z` (each number in decimal without leading zeros, as in
//! `bend/semver.bend`, with at most 14 digits) is a release. A version
//! `X.Y.Z-<suffix>` (a `-dev` build or an older-scheme build such as
//! `0.9.9-main.46`) ranks below the releases of its series `X.Y`. Ranks
//! order by major, minor, release before prerelease, and patch. Any other
//! text has no rank and ranks below all versions; so does a version with a
//! number of 15 digits or more, past the range of the compiled Bend core's
//! numbers (2^48 - 1). Two builds with the same build id are the same
//! build; two other builds of an equal rank are not in order.
//!
//! Only an interactive start replaces a daemon, and only a daemon of a
//! lower rank. Thus a client never replaces a newer daemon, a background
//! client never replaces a daemon, and two builds cannot replace each other
//! in turn. The rule runs as its Bend model, `bend/replace.bend`, through
//! the compiled core's entry `bend/ffi_replace.bend`; `laws/replace.bend`
//! states `replace_never_downgrades`, `replacement_terminates`,
//! `background_never_replaces`, and pins the reading of a version
//! (`replace_rank_reads_semver`) and the entry (`replace_ffi_relation`,
//! `replace_ffi_verdict`).

use eukhe_bend::wire::{Reader, WireError, Writer};
use eukhe_bend::Entry;

/// The client that starts the daemon or connects to it again.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Caller {
    /// A start that the user runs in a terminal (the interactive TUI,
    /// `eukhe chat`). It can replace a daemon of a lower rank.
    Interactive,
    /// A client that runs in the background or connects again (the
    /// dashboard, the gateway, ACP, the relaunch of a lost daemon). It
    /// never replaces a running daemon. It starts a daemon only when no
    /// daemon listens.
    Background,
}

/// A build as a daemon client sees it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Build<'a> {
    /// The product version (the hello `appVersion`).
    pub version: &'a str,
    /// The build id (the hello `runtime.buildId`).
    pub id: &'a str,
}

impl Build<'static> {
    /// This build.
    pub const THIS: Self = Self {
        version: eukhe_build_info::VERSION,
        id: eukhe_build_info::DAEMON_BUILD_ID,
    };
}

/// How the daemon's build relates to the client's build.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Relation {
    /// The same build id.
    Same,
    /// The daemon's version has a lower rank.
    Older,
    /// The daemon's version has a higher rank: the client is the older one.
    Newer,
    /// Another build id with an equal rank.
    Other,
}

/// What a client start does with the running daemon.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Replacement {
    /// Replace the daemon (when it is idle).
    Replace,
    /// Keep the daemon; the relation tells how it relates to the client.
    Keep(Relation),
}

/// The chars of a version the core reads: a version of more than 64 chars
/// has no rank, so its first 65 decide its rank (law `replace_rank_cut`),
/// and a daemon's hello cannot push the request past the wire's longest
/// string.
const VERSION_CHARS: usize = 65;

/// The first [`VERSION_CHARS`] chars of `version`.
fn version_head(version: &str) -> &str {
    version
        .char_indices()
        .nth(VERSION_CHARS)
        .map_or(version, |(end, _)| &version[..end])
}

/// The request both entries start with: the two versions and whether the
/// build ids are equal (the model reads the ids only through that).
fn write_builds(writer: &mut Writer, client: Build<'_>, daemon: Build<'_>) {
    writer
        .str(version_head(client.version))
        .str(version_head(daemon.version))
        .bool(client.id == daemon.id);
}

/// A relation, by its tag in `bend/ffi_replace.bend`.
fn read_relation(reader: &mut Reader<'_>) -> Result<Relation, WireError> {
    Ok(match reader.tag_of(4, "a Rel tag")? {
        0 => Relation::Same,
        1 => Relation::Older,
        2 => Relation::Newer,
        // `tag_of` answered at most 3.
        3..=u32::MAX => Relation::Other,
    })
}

/// How the `daemon` build relates to the `client` build.
#[must_use]
pub fn relation(client: Build<'_>, daemon: Build<'_>) -> Relation {
    crate::bend_core::decide(
        Entry::Replace,
        |writer| {
            writer.tag(0);
            write_builds(writer, client, daemon);
        },
        read_relation,
    )
}

/// What a start of `client` by `caller` does with a running `daemon`: an
/// interactive start replaces an older daemon; every other start keeps it.
#[must_use]
pub fn replacement_verdict(client: Build<'_>, daemon: Build<'_>, caller: Caller) -> Replacement {
    crate::bend_core::decide(
        Entry::Replace,
        |writer| {
            writer.tag(1);
            write_builds(writer, client, daemon);
            writer.tag(match caller {
                Caller::Interactive => 0,
                Caller::Background => 1,
            });
        },
        |reader| {
            Ok(if reader.tag_of(2, "a Verdict tag")? == 0 {
                Replacement::Replace
            } else {
                Replacement::Keep(read_relation(reader)?)
            })
        },
    )
}

/// What a client says when the running daemon is newer than its build.
#[must_use]
pub fn older_client_notice(client: Build<'_>, daemon: Build<'_>) -> String {
    format!(
        "this eukhe (v{}) is older than the running daemon (v{}): update or run `eukhe shutdown`",
        client.version, daemon.version
    )
}

/// What a client says when it keeps a daemon of another build; `None` for
/// a daemon of its own build.
#[must_use]
pub fn kept_daemon_notice(client: Build<'_>, daemon: Build<'_>) -> Option<String> {
    match relation(client, daemon) {
        Relation::Same => None,
        Relation::Older => Some(format!(
            "The background service runs eukhe {}; it restarts on the next idle interactive start (or run: eukhe shutdown).",
            daemon.version
        )),
        Relation::Newer => Some(older_client_notice(client, daemon)),
        Relation::Other => Some(format!(
            "The background service runs another build of eukhe {} ({}); it does not restart automatically (run: eukhe shutdown).",
            daemon.version,
            daemon
                .id
                .strip_prefix(eukhe_build_info::DAEMON_BUILD_ID_PREFIX)
                .unwrap_or(daemon.id)
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn build<'a>(version: &'a str, id: &'a str) -> Build<'a> {
        Build { version, id }
    }

    /// A client older than the daemon tells the user so, through the real
    /// core call.
    #[test]
    fn an_older_client_names_the_newer_daemon() {
        let old = build("0.9.9-main.46", "eukhe-daemon-rs-0.9.9-main.46");
        let new = build("0.10.40", "eukhe-daemon-rs-0.10.40+0123456789ab");
        assert_eq!(
            kept_daemon_notice(old, new),
            Some(
                "this eukhe (v0.9.9-main.46) is older than the running daemon (v0.10.40): update or run `eukhe shutdown`"
                    .to_string()
            )
        );
    }

    /// A version longer than the wire's longest string reaches the core
    /// cut to its head: it has no rank, so an interactive start of a
    /// release replaces it, and no call fails.
    #[test]
    fn a_huge_version_has_no_rank() {
        let huge = format!("0.1.0-{}", "x".repeat(eukhe_bend::wire::STR_MAX));
        let daemon = build(&huge, "eukhe-daemon-rs-huge");
        let client = build("0.0.1", "eukhe-daemon-rs-0.0.1");
        assert_eq!(
            (
                replacement_verdict(client, daemon, Caller::Interactive),
                relation(daemon, client)
            ),
            (Replacement::Replace, Relation::Newer)
        );
    }

    /// Another build of the same version is not replaced; the client tells
    /// the user which build runs.
    #[test]
    fn another_build_of_the_same_version_is_kept_and_named() {
        let client = build("0.10.0-dev", "eukhe-daemon-rs-0.10.0-dev+aaaaaaaaaaaa");
        let daemon = build("0.10.0-dev", "eukhe-daemon-rs-0.10.0-dev+bbbbbbbbbbbb");
        assert_eq!(
            (
                replacement_verdict(client, daemon, Caller::Interactive),
                kept_daemon_notice(client, daemon)
            ),
            (
                Replacement::Keep(Relation::Other),
                Some(
                    "The background service runs another build of eukhe 0.10.0-dev (0.10.0-dev+bbbbbbbbbbbb); it does not restart automatically (run: eukhe shutdown)."
                        .to_string()
                )
            )
        );
    }
}
