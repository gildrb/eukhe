//! The client-side and worker-side timing of a lost supervisor. The client
//! (`eukhe-tui`) and the worker (`eukhe-daemon`) both read these values, so
//! they live here. Each value derives from the values it must exceed; the
//! law `timeouts_ordered` (LAWS.bend, D1) proves the order of the
//! derivation and the `eukhe-daemon` bridge test checks that these values
//! are the derivation.

/// A client launcher waits this long for a spawned supervisor to greet.
pub const DAEMON_STARTUP_TIMEOUT_MS: u64 = 30_000;

/// An attached client relaunches a lost supervisor this soon after the
/// loss, at the latest.
pub const CLIENT_RELAUNCH_WITHIN_MS: u64 = 60_000;

/// A worker checks its supervisor's socket this often.
pub const WORKER_SUPERVISOR_CHECK_MS: u64 = 5_000;

/// The extra time a worker gives a lost supervisor after the latest moment
/// a relaunched supervisor answers (it makes the window five minutes).
pub const WORKER_LOST_EXIT_SLACK_MS: u64 = 205_000;

/// A worker whose supervisor stays unreachable this long exits (the
/// default of the lost-exit window). A client relaunches the supervisor,
/// the supervisor starts, and the worker sees it, all before this time.
pub const WORKER_LOST_EXIT_DEFAULT_MS: u64 = CLIENT_RELAUNCH_WITHIN_MS
    + DAEMON_STARTUP_TIMEOUT_MS
    + WORKER_SUPERVISOR_CHECK_MS
    + WORKER_LOST_EXIT_SLACK_MS;
