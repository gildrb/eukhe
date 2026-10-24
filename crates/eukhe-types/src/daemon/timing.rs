//! The client-side and worker-side timing of a lost supervisor. The client
//! (`eukhe-tui`) and the worker (`eukhe-daemon`) both read these values, so
//! they live here. The lost-exit window derives from them in the compiled
//! core (`eukhe-daemon` `timeouts::derived`): the law `timeouts_ordered`
//! (`laws/supervise.bend`, D1) proves the order of the derivation.

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
