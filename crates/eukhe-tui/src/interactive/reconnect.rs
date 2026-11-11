//! The reconnect machinery (moved with its concern): the unexpected-loss
//! hiccup loop and the announced shutdown's bounded recovery - the loop
//! drivers, the session-plane re-attach, and the arming seam.

use super::{mpsc, AgentView, DaemonClient, DaemonClientEvent, Duration, RecoveryKind, SessionUi};

/// The in-flight reconnect attempt's connect leg: a spawned task's
/// bounded `DaemonClient::connect_with_retry` result (fresh client plus
/// its event receiver), reported back to the interactive loop through a
/// oneshot.
pub(super) type ReconnectConnect = tokio::sync::oneshot::Receiver<
    anyhow::Result<(DaemonClient, mpsc::UnboundedReceiver<DaemonClientEvent>)>,
>;

/// The client reconnect window after an unexpected daemon loss
/// (10 minutes). The relaunch happens much earlier: see
/// [`LOST_RELAUNCH_LATEST_MS`].
const RECONNECT_WINDOW: Duration = Duration::from_mins(10);

/// The first reconnect attempt after an unexpected loss.
const LOST_FIRST_ATTEMPT_MS: u64 = 1_000;

/// The latest time after an unexpected loss at which the recovery starts
/// its relaunch: the first attempt, plus that attempt's single connect
/// (the connect and the hello budgets of [`DaemonClient::connect`]).
const LOST_RELAUNCH_LATEST_MS: u64 = LOST_FIRST_ATTEMPT_MS
    + eukhe_client::daemon_client::CONNECT_TIMEOUT_MS
    + eukhe_client::daemon_client::HELLO_TIMEOUT_MS;

// A worker alive at the loss outlives the relaunch (the worker's lost-exit
// window derives from this bound).
const _: () =
    assert!(LOST_RELAUNCH_LATEST_MS <= eukhe_types::daemon::timing::CLIENT_RELAUNCH_WITHIN_MS);

/// How one reconnect attempt reaches the daemon.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ConnectLeg {
    /// Connect once.
    Connect,
    /// Relaunch the daemon of this client's build, then connect once.
    RelaunchThenConnect,
}

/// The connect leg of the next attempt of a `kind` recovery after
/// `failed_connects` failed connects. Only an unexpected loss relaunches
/// the daemon, from the attempt after the first failed connect on (the
/// launcher returns at once when a daemon already runs). An announced
/// shutdown never relaunches: an explicit stop stays stopped.
pub(super) fn connect_leg(kind: RecoveryKind, failed_connects: u32) -> ConnectLeg {
    match kind {
        RecoveryKind::Lost if failed_connects > 0 => ConnectLeg::RelaunchThenConnect,
        RecoveryKind::Lost | RecoveryKind::Shutdown => ConnectLeg::Connect,
    }
}

/// The reconnect backoff cap.
const RECONNECT_BACKOFF_MAX: Duration = Duration::from_secs(10);

/// TS #2458 `DAEMON_RECONNECT_TIMEOUT_MS`: the announced closing's
/// recovery window -- an explicit stop stays stopped, so the pane waits
/// for the daemon to come back bounded instead of retrying through the
/// hiccup window.
pub(super) const DAEMON_SHUTDOWN_RECONNECT_WINDOW: Duration = Duration::from_secs(60);

/// TS #2458 `SHUTDOWN_RECONNECT_RETRY_MS`: the shutdown recovery's poll
/// cadence (fixed, unlike the doubling hiccup backoff).
pub(super) const SHUTDOWN_RECONNECT_RETRY: Duration = Duration::from_millis(100);

/// TS `DAEMON_RECONNECT_TIMEOUT_MS`: the bounded session-plane reconnect
/// window after the direct worker link dies.
const SESSION_RECONNECT_WINDOW: Duration = Duration::from_mins(1);
/// Test seam: a number of milliseconds here replaces
/// [`SESSION_RECONNECT_WINDOW`], so a headless test of the expired window
/// waits on the window's end, not on a real minute.
const SESSION_RECONNECT_WINDOW_ENV: &str = "EUKHE_TEST_SESSION_RECONNECT_WINDOW_MS";
/// TS reconnect backoff cap (`min(2000, 100 * 2 ** min(attempt, 5))`).
const SESSION_RECONNECT_BACKOFF_MAX: Duration = Duration::from_secs(2);

/// The interactive loop's session re-attach driver (TS
/// `DaemonAgentConnection.reconnect` over a direct-transport loss): the
/// worker process behind the direct link died, so the attach retries
/// through the supervisor -- which respawns the worker and hands out a
/// fresh peer ticket -- with the TS backoff inside the TS window.
pub(super) struct SessionReconnect {
    pub(super) active_session_id: String,
    pub(super) deadline: tokio::time::Instant,
    pub(super) next_attempt: tokio::time::Instant,
    delay: Duration,
}

impl SessionReconnect {
    pub(super) fn start(active_session_id: &str) -> Self {
        let window = std::env::var(SESSION_RECONNECT_WINDOW_ENV)
            .ok()
            .and_then(|ms| ms.parse().ok())
            .map_or(SESSION_RECONNECT_WINDOW, Duration::from_millis);
        SessionReconnect {
            active_session_id: active_session_id.to_string(),
            deadline: tokio::time::Instant::now() + window,
            next_attempt: tokio::time::Instant::now(),
            delay: Duration::from_millis(100),
        }
    }

    /// The next attempt with doubling backoff (capped).
    pub(super) fn next_attempt(mut self) -> Self {
        self.delay = (self.delay * 2).min(SESSION_RECONNECT_BACKOFF_MAX);
        self.next_attempt = tokio::time::Instant::now() + self.delay;
        self
    }
}

/// One session-plane re-attach attempt. Returns the driver to keep (the
/// next attempt) or `None` when the session is back, the user switched
/// sessions, or the window closed.
pub(super) async fn retry_session_attach(
    session: &mut SessionUi,
    view: &mut AgentView,
    state: SessionReconnect,
) -> Option<SessionReconnect> {
    // The user switched sessions while the link was down: the new attach
    // owns its own connection, so this driver stops.
    if state.active_session_id != session.active_session_id {
        return None;
    }
    let Err(error) = session
        .reattach_session(crate::session_ui::ReattachBy::ActiveId, view)
        .await
    else {
        return None;
    };
    if tokio::time::Instant::now() <= state.deadline {
        return Some(state.next_attempt());
    }
    // TS terminal close: the window expired, the last error surfaces as
    // the closed event's error row, and the UI stays mounted. The next
    // submit tries the re-attach once more: the supervisor reopens the
    // session from storage once it can (a disk that filled up has room
    // again), so a session outlasting the window is not lost to this view.
    session.error_row(&format!("Daemon reconnection failed: {error}"), view);
    session.reconnection_failed = Some(error);
    session.dirty = true;
    None
}

/// The full reconnect window ran out: say why the surface is closing.
pub(super) fn close_expired_recovery(
    session: &mut SessionUi,
    view: &mut AgentView,
    kind: RecoveryKind,
) {
    match kind {
        RecoveryKind::Shutdown => {
            // TS #2458: the daemon never came back within the reconnect
            // timeout -- the saved-transcript close (the session file
            // survives on disk).
            session.note(
                "The Eukhe daemon shut down while this window was attached. The session transcript remains saved; restart Eukhe and reopen it from Agents View.",
                view,
            );
        }
        RecoveryKind::Lost => {
            session.note(
                "could not reconnect to the daemon within 10 minutes -- run `eukhe attach` to resume.",
                view,
            );
        }
    }
}

/// The interactive loop's full reconnect driver: attempts with backoff
/// inside the window; the user can leave with Ctrl+C at any point (UI
/// input keeps flowing through the same loop). Two closings arm it -- an
/// UNEXPECTED connection loss (the supervisor connection died mid-run -- a
/// daemon hiccup at load, 2026-09-24: the one-shot path exited the
/// operator's TUI with "the daemon connection closed"), and an ANNOUNCED
/// closing (TS #2458: the operator's own shutdown used to kill every
/// attached window) -- the pane keeps its transcript and editor and
/// retries instead of dying.
pub(super) struct ReconnectLoop {
    pub(super) deadline: tokio::time::Instant,
    pub(super) next_attempt: tokio::time::Instant,
    pub(super) delay: Duration,
    /// The closing that armed this driver: the reattach banner and the
    /// expiry row follow it.
    pub(super) kind: RecoveryKind,
    /// The connects that failed so far: [`connect_leg`] relaunches the
    /// daemon after the first.
    pub(super) failed_connects: u32,
}

impl ReconnectLoop {
    /// The unexpected-loss driver: the reconnect window with doubling
    /// backoff and its own expiry row.
    pub(super) fn start_lost() -> Self {
        let delay = Duration::from_millis(LOST_FIRST_ATTEMPT_MS);
        ReconnectLoop {
            deadline: tokio::time::Instant::now() + RECONNECT_WINDOW,
            next_attempt: tokio::time::Instant::now() + delay,
            delay,
            kind: RecoveryKind::Lost,
            failed_connects: 0,
        }
    }

    /// TS #2458 `reconnectAfterShutdown`: the announced closing. The
    /// window is the TS reconnect timeout (not the hiccup window -- an
    /// explicit stop stays stopped), the cadence is
    /// the TS fixed poll, and the expiry is the saved-transcript close.
    pub(super) fn start_shutdown() -> Self {
        ReconnectLoop {
            deadline: tokio::time::Instant::now() + DAEMON_SHUTDOWN_RECONNECT_WINDOW,
            next_attempt: tokio::time::Instant::now() + SHUTDOWN_RECONNECT_RETRY,
            delay: SHUTDOWN_RECONNECT_RETRY,
            kind: RecoveryKind::Shutdown,
            failed_connects: 0,
        }
    }

    /// The next attempt: doubling backoff (capped) for the hiccup
    /// window; the shutdown recovery keeps the TS fixed poll.
    pub(super) fn next_attempt(mut self) -> Self {
        if !matches!(self.kind, RecoveryKind::Shutdown) {
            self.delay = (self.delay * 2).min(RECONNECT_BACKOFF_MAX);
        }
        self.next_attempt = tokio::time::Instant::now() + self.delay;
        self
    }
}

/// TS #2458 `reconnectAfterShutdown`'s arming: an announced non-update
/// closing (`daemon_closing` with no update) keeps the pane mounted while
/// it waits bounded for the daemon to come back on the same socket path
/// (the recovery never relaunches the daemon -- an explicit stop stays
/// stopped). No-op when the notice is absent (a bare session stop stays
/// stopped) or a driver already owns the recovery; `true` when it armed.
pub(super) fn arm_shutdown_recovery(
    session: &mut SessionUi,
    view: &mut AgentView,
    reconnect: &mut Option<ReconnectLoop>,
    session_reconnect: &mut Option<SessionReconnect>,
) -> bool {
    if reconnect.is_some() || session.daemon_closing_notice.as_deref() != Some("shutdown") {
        return false;
    }
    session.note_as(
        "the Eukhe daemon shut down; waiting for it to come back...",
        crate::chat::StatusKind::Warning,
        view,
    );
    // TS #2458's yield rule: the shutdown recovery owns the run -- a
    // session-plane retry armed by an earlier direct-link loss would race
    // it through a dying supervisor, and its expiry would block submits
    // after a later reconnect lands.
    *session_reconnect = None;
    *reconnect = Some(ReconnectLoop::start_shutdown());
    session.dirty = true;
    true
}
