//! The supervisor's timeouts. Each derived timeout comes from the
//! timeouts it must exceed, so an edit of one cannot reorder them: the law
//! `timeouts_ordered` (`laws/supervise.bend`, D1; the model in
//! bend/supervise.bend) proves the order of the derivation, and the
//! derivation runs as the compiled model: [`derived`] writes the base
//! values below (and those of `eukhe-types` `daemon::timing` and
//! `eukhe-core` `kernel::shared`) to `bend/ffi_timeouts.bend` once and
//! keeps its answer (laws `timeouts_ffi_*`, `laws/timeouts.bend`).
//!
//! - A stop gives a worker the whole kernel teardown plus the Harness
//!   close before the supervisor kills it.
//! - The supervisor's drain (the stop grace, then SIGTERM, then SIGKILL)
//!   ends before the launcher stops waiting for the old supervisor.
//! - Busy evidence is refreshed more often than it ages out.
//! - A worker that crashes in a loop is given up within the restart window.

use std::sync::LazyLock;

use eukhe_bend::wire::{Reader, Writer};
use eukhe_bend::Entry;
use eukhe_core::kernel::shared::{
    HOST_REQUEST_SHUTDOWN_TIMEOUT_MS, KERNEL_KILL_VERIFY_MS, KERNEL_SHUTDOWN_TIMEOUT_MS,
    KERNEL_TERM_GRACE_MS, SNAPSHOT_EXECUTION_TIMEOUT_MS,
};
use eukhe_types::daemon::timing::{
    CLIENT_RELAUNCH_WITHIN_MS, DAEMON_STARTUP_TIMEOUT_MS, WORKER_LOST_EXIT_SLACK_MS,
    WORKER_SUPERVISOR_CHECK_MS,
};

/// The worker's Harness close (pending commits flush, the lease releases)
/// after its kernel teardown.
pub const HARNESS_CLOSE_MS: u64 = 2_000;

/// After the stop grace, a worker gets SIGTERM, then this long to exit.
pub const WORKER_TERM_GRACE_MS: u64 = 2_000;

/// After SIGKILL, the supervisor waits this long for the worker's exit.
pub const WORKER_KILL_VERIFY_MS: u64 = 1_000;

/// What the launcher adds to the drain before it stops a supervisor that
/// did not exit (the supervisor's own exit after its last worker).
pub const LAUNCHER_DRAIN_MARGIN_MS: u64 = 2_000;

/// An idle shutdown asks every worker to quiesce at the same time and
/// waits this long for all the answers (one window, not one per worker).
/// A worker that does not answer in time counts as busy.
pub const QUIESCE_ANSWER_MS: u64 = 5_000;

/// A worker re-records its busy evidence this often while it has work.
pub const BUSY_REFRESH_MS: u64 = 5 * 60_000;

/// A boot this soon after a busy worker's crash revives it, however long
/// its run already took.
pub const REVIVAL_BOOT_WINDOW_MS: u64 = 25 * 60_000;

/// A worker that fails more often than this inside the restart window is
/// given up.
pub const RESTART_GIVE_UP_AFTER: u32 = 5;

/// The first restart pause; each further failure in the window doubles it.
pub const RESTART_BASE_BACKOFF_MS: u64 = 250;

/// The longest restart pause.
pub const RESTART_MAX_BACKOFF_MS: u64 = 30_000;

/// A worker whose crash loop repeats at most this long after each restart
/// is given up (it is a loop, not a rare crash).
pub const RESTART_CRASH_LOOP_MS: u64 = 120_000;

/// The timeouts derived from the base values (ms), as the compiled core
/// answers them.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Derived {
    /// The longest kernel teardown: the snapshot flush, the host-request
    /// drain, the shutdown send, its reply, the exit wait, then SIGTERM
    /// and SIGKILL.
    pub kernel_teardown_ms: u64,
    /// The cooperative grace of every stop (ADR 0011): a routed `kill` or
    /// `shutdown` gets this long to settle before the supervisor kills the
    /// worker. It covers the longest kernel teardown and the Harness close.
    pub stop_grace_ms: u64,
    /// The longest stop of one worker: the grace, SIGTERM, SIGKILL.
    /// Workers stop in parallel, so this is the supervisor's drain too.
    pub supervisor_drain_ms: u64,
    /// How long a launcher waits for a supervisor it asked to shut down
    /// before it kills it: after the supervisor's whole drain.
    pub launcher_shutdown_wait_ms: u64,
    /// How long a parent waits for the kill of one RLM child session: the
    /// parent's kill route grace, then the child's whole drain, then the
    /// margin.
    pub rlm_child_kill_timeout_ms: u64,
    /// A worker whose supervisor stays unreachable this long exits (the
    /// default of the lost-exit window). A client relaunches the
    /// supervisor, the supervisor starts, and the worker sees it, all
    /// before this time.
    pub worker_lost_exit_default_ms: u64,
    /// How long a `busy` recovery record still proves interrupted live
    /// work: one refresh period plus the boot window. A record older than
    /// this is residue of a run that already ended; the session stays down
    /// and reopens through the next client create.
    pub revival_busy_evidence_max_age_ms: u64,
    /// A quiesced worker opens its run gate again after this long when no
    /// stop and no release came (its supervisor died while it decided).
    /// The hold outlasts the answer window and then the stop's own grace,
    /// so a committed shutdown reaches the worker before the gate opens.
    pub quiesce_hold_ms: u64,
    /// The window the restart failures are counted in (monotonic clock):
    /// the give-up count of crash loops, each failure at most the longest
    /// pause plus the loop period after the one before it.
    pub restart_window_ms: u64,
}

/// The derived timeouts: the compiled core's answer on the base values,
/// asked once per process.
#[must_use]
pub fn derived() -> &'static Derived {
    static DERIVED: LazyLock<Derived> =
        LazyLock::new(|| eukhe_bend::expect_core(Entry::Timeouts, derive()));
    &DERIVED
}

/// Every base value is a small constant: each fits the wire.
fn derive() -> Result<Derived, eukhe_bend::Error> {
    let mut request = Writer::new();
    request
        .nat(SNAPSHOT_EXECUTION_TIMEOUT_MS)
        .nat(HOST_REQUEST_SHUTDOWN_TIMEOUT_MS)
        .nat(KERNEL_SHUTDOWN_TIMEOUT_MS)
        .nat(KERNEL_TERM_GRACE_MS)
        .nat(KERNEL_KILL_VERIFY_MS)
        .nat(HARNESS_CLOSE_MS)
        .nat(WORKER_TERM_GRACE_MS)
        .nat(WORKER_KILL_VERIFY_MS)
        .nat(LAUNCHER_DRAIN_MARGIN_MS)
        .nat(BUSY_REFRESH_MS)
        .nat(REVIVAL_BOOT_WINDOW_MS)
        .nat(CLIENT_RELAUNCH_WITHIN_MS)
        .nat(DAEMON_STARTUP_TIMEOUT_MS)
        .nat(WORKER_SUPERVISOR_CHECK_MS)
        .nat(WORKER_LOST_EXIT_SLACK_MS)
        .nat(u64::from(RESTART_GIVE_UP_AFTER))
        .nat(RESTART_MAX_BACKOFF_MS)
        .nat(RESTART_CRASH_LOOP_MS)
        .nat(QUIESCE_ANSWER_MS);
    let reply = eukhe_bend::call(Entry::Timeouts, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let derived = Derived {
        kernel_teardown_ms: reader.nat()?,
        stop_grace_ms: reader.nat()?,
        supervisor_drain_ms: reader.nat()?,
        launcher_shutdown_wait_ms: reader.nat()?,
        rlm_child_kill_timeout_ms: reader.nat()?,
        worker_lost_exit_default_ms: reader.nat()?,
        revival_busy_evidence_max_age_ms: reader.nat()?,
        quiesce_hold_ms: reader.nat()?,
        restart_window_ms: reader.nat()?,
    };
    reader.end()?;
    Ok(derived)
}

#[cfg(test)]
mod tests {
    use super::{derived, Derived};

    /// The compiled core answers the base values eukhe ships.
    #[test]
    fn the_core_derives_the_shipped_timeouts() {
        assert_eq!(
            *derived(),
            Derived {
                kernel_teardown_ms: 28_000,
                stop_grace_ms: 30_000,
                supervisor_drain_ms: 33_000,
                launcher_shutdown_wait_ms: 35_000,
                rlm_child_kill_timeout_ms: 65_000,
                worker_lost_exit_default_ms: 300_000,
                revival_busy_evidence_max_age_ms: 1_800_000,
                quiesce_hold_ms: 35_000,
                restart_window_ms: 900_000,
            }
        );
    }
}
