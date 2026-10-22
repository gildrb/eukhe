//! The order of eukhe builds and the launcher's replacement verdict
//! (docs/daemon.md D1). A client compares its build with the build of the
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
//! in turn. The model is `bend/replace.bend`; `LAWS.bend` section `supervisor` states
//! `replace_never_downgrades`, `replacement_terminates` and
//! `background_never_replaces`; the bridge test is `daemon_build/bridge.rs`.

use std::cmp::Ordering;

#[cfg(test)]
mod bridge;

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

/// Release before prerelease, in the order of the derive.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Tier {
    Prerelease,
    Release,
}

/// The rank of a version, in the order of the derive: major, minor, tier,
/// patch. A version without a rank is `None`, which orders below `Some`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Rank {
    major: u64,
    minor: u64,
    tier: Tier,
    patch: u64,
}

/// A number in decimal without leading zeros, of at most 14 digits.
fn number(text: &str) -> Option<u64> {
    let canonical = !text.is_empty()
        && text.len() <= 14
        && text.bytes().all(|byte| byte.is_ascii_digit())
        && (text.len() == 1 || !text.starts_with('0'));
    canonical.then(|| text.parse().ok()).flatten()
}

fn rank(version: &str) -> Option<Rank> {
    let (core, tier) = match version.split_once('-') {
        Some((core, _suffix)) => (core, Tier::Prerelease),
        None => (version, Tier::Release),
    };
    let mut fields = core.split('.');
    let rank = Rank {
        major: number(fields.next()?)?,
        minor: number(fields.next()?)?,
        tier,
        patch: number(fields.next()?)?,
    };
    fields.next().is_none().then_some(rank)
}

/// How the `daemon` build relates to the `client` build.
#[must_use]
pub fn relation(client: Build<'_>, daemon: Build<'_>) -> Relation {
    if client.id == daemon.id {
        return Relation::Same;
    }
    match rank(daemon.version).cmp(&rank(client.version)) {
        Ordering::Less => Relation::Older,
        Ordering::Greater => Relation::Newer,
        Ordering::Equal => Relation::Other,
    }
}

/// What a start of `client` by `caller` does with a running `daemon`: an
/// interactive start replaces an older daemon; every other start keeps it.
#[must_use]
pub fn replacement_verdict(client: Build<'_>, daemon: Build<'_>, caller: Caller) -> Replacement {
    match (relation(client, daemon), caller) {
        (Relation::Older, Caller::Interactive) => Replacement::Replace,
        (kept, Caller::Interactive | Caller::Background) => Replacement::Keep(kept),
    }
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

    /// Releases order by semver precedence; a dev or older-scheme build
    /// ranks below the releases of its series; text that is no version
    /// ranks below everything.
    #[test]
    fn versions_rank_by_release_then_series() {
        let ascending = [
            "garbage",
            "0.9.0-dev",
            "0.9.9-main.46",
            "0.9.0",
            "0.9.9",
            "0.10.0-dev",
            "0.10.3-dev",
            "0.10.0",
            "0.10.40",
            "0.10.41",
            "1.0.0",
        ];
        let ranks: Vec<Option<Rank>> = ascending.iter().map(|version| rank(version)).collect();
        let mut sorted = ranks.clone();
        sorted.sort();
        sorted.dedup();
        assert_eq!(sorted, ranks);
        assert_eq!(
            ["01.2.3", "1.2", "1.2.3.4", "", "1..3", "+1.2.3"].map(rank),
            [None; 6]
        );
    }

    // Regression: an old dashboard (0.9.9-main.46) and a new TUI (0.10.40)
    // replaced each other's daemon forever. Now neither replaces a newer
    // daemon, and the background reconnects replace nothing.
    #[test]
    fn the_ping_pong_pair_settles_on_the_newer_build() {
        let old = build("0.9.9-main.46", "eukhe-daemon-rs-0.9.9-main.46");
        let new = build("0.10.40", "eukhe-daemon-rs-0.10.40+0123456789ab");
        let verdicts = [
            replacement_verdict(old, new, Caller::Background),
            replacement_verdict(old, new, Caller::Interactive),
            replacement_verdict(new, old, Caller::Background),
            replacement_verdict(new, old, Caller::Interactive),
            replacement_verdict(new, new, Caller::Interactive),
        ];
        assert_eq!(
            verdicts,
            [
                Replacement::Keep(Relation::Newer),
                Replacement::Keep(Relation::Newer),
                Replacement::Keep(Relation::Older),
                Replacement::Replace,
                Replacement::Keep(Relation::Same),
            ]
        );
        assert_eq!(
            kept_daemon_notice(old, new),
            Some(
                "this eukhe (v0.9.9-main.46) is older than the running daemon (v0.10.40): update or run `eukhe shutdown`"
                    .to_string()
            )
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
