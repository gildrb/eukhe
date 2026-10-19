//! The daemon-reconnect concern (TS #2458): a window that survived a daemon
//! restart reports it version-honestly -- when the restarted daemon is NEWER
//! than this window's binary, the recovered row says so instead of
//! pretending the window is updated.
//!
//! [`RecoveryKind`] names the reconnect drivers the interactive loop arms
//! (the unexpected-loss hiccup window and TS #2458's announced closing),
//! so the window's expiry row follows the flow that owns the recovery.

use crate::chat::StatusKind;
use crate::daemon_build::{relation, Build, Relation};

/// The reconnect driver that owns the run: which daemon closing armed it
/// decides the backoff and the expiry row.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RecoveryKind {
    /// An unexpected connection loss with no notice: a daemon hiccup --
    /// doubling backoff inside the reconnect window, its own expiry row.
    Lost,
    /// TS #2458 `reconnectAfterShutdown`: the daemon announced its
    /// closing. The pane waits bounded for it to come back on the same
    /// socket path and never relaunches it (an explicit stop stays
    /// stopped); the expiry is the saved-transcript close.
    Shutdown,
}

/// TS #2458 `formatDaemonReconnectBanner`: the row a recovered window
/// shows, from this window's build (`client`) and the restarted daemon's
/// build (`daemon`, [`DaemonClient::daemon_build`](crate::daemon_client::DaemonClient::daemon_build)),
/// in the order of [`crate::daemon_build`]. The row is version-honest: a
/// daemon that is not older than this window names the mismatch (the user
/// restarts the window to pick the update up), while an older daemon
/// reports without the advice (restarting this window would pick up
/// nothing).
pub(crate) fn reconnect_banner(client: Build<'_>, daemon: Build<'_>) -> (String, StatusKind) {
    let (client_version, daemon_version) = (client.version, daemon.version);
    match relation(client, daemon) {
        Relation::Same => (
            format!("Daemon restarted (v{client_version}) - reconnected"),
            StatusKind::Info,
        ),
        Relation::Older => (
            format!("Daemon restarted (v{daemon_version}), this window runs v{client_version}."),
            StatusKind::Info,
        ),
        Relation::Newer => (
            format!("Daemon restarted (v{daemon_version}), this window still runs v{client_version} - restart the window to pick up the update."),
            StatusKind::Warning,
        ),
        Relation::Other => (
            format!("Daemon restarted (v{daemon_version} (another build)), this window still runs v{client_version} - restart the window to pick up the update."),
            StatusKind::Warning,
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn build<'a>(version: &'a str, id: &'a str) -> Build<'a> {
        Build { version, id }
    }

    /// The TS #2458 banner table (interactive-update-relaunch.test.ts) on
    /// the order of eukhe builds: the recovered window's row is
    /// version-honest.
    #[test]
    fn the_banner_table_is_the_ts_table() {
        let banners = [
            reconnect_banner(build("1.2.3", "a"), build("1.2.3", "a")),
            reconnect_banner(build("1.2.3", "a"), build("2.0.0", "b")),
            reconnect_banner(build("1.2.3-beta.1", "a"), build("1.2.3", "b")),
            reconnect_banner(build("1.2.3", "a"), build("1.2.3-beta.1", "b")),
            reconnect_banner(build("0.10.40", "a"), build("0.9.9-main.46", "b")),
            reconnect_banner(build("0.9.9-main.46", "a"), build("0.10.40", "b")),
        ];
        assert_eq!(
            banners,
            [
                ("Daemon restarted (v1.2.3) - reconnected".to_string(), StatusKind::Info),
                ("Daemon restarted (v2.0.0), this window still runs v1.2.3 - restart the window to pick up the update.".to_string(), StatusKind::Warning),
                ("Daemon restarted (v1.2.3), this window still runs v1.2.3-beta.1 - restart the window to pick up the update.".to_string(), StatusKind::Warning),
                ("Daemon restarted (v1.2.3-beta.1), this window runs v1.2.3.".to_string(), StatusKind::Info),
                ("Daemon restarted (v0.9.9-main.46), this window runs v0.10.40.".to_string(), StatusKind::Info),
                ("Daemon restarted (v0.10.40), this window still runs v0.9.9-main.46 - restart the window to pick up the update.".to_string(), StatusKind::Warning),
            ]
        );
    }

    /// A same-version daemon of another build is not this window's build:
    /// the banner names it and advises the restart (F19).
    #[test]
    fn another_build_of_this_version_is_named_in_the_banner() {
        let another_build_banner = "Daemon restarted (v1.2.3 (another build)), this window still runs v1.2.3 - restart the window to pick up the update.";
        assert_eq!(
            reconnect_banner(build("1.2.3", "a"), build("1.2.3", "b")),
            (another_build_banner.to_string(), StatusKind::Warning)
        );
    }
}
