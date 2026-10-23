//! The supervisor's timeouts. Each one derives from the timeouts it must
//! exceed, so an edit of one cannot reorder them: the law
//! `timeouts_ordered` (`laws/supervise.bend`, D1; the model in bend/supervise.bend)
//! proves the order of the derivation, and the bridge test
//! (`crate::supervision_bridge`) checks that these values are the
//! derivation.
//!
//! - A stop gives a worker the whole kernel teardown plus the Harness
//!   close before the supervisor kills it.
//! - The supervisor's drain (the stop grace, then SIGTERM, then SIGKILL)
//!   ends before the launcher stops waiting for the old supervisor.
//! - Busy evidence is refreshed more often than it ages out.
//! - A worker that crashes in a loop is given up within the restart window.

use eukhe_core::kernel::shared::KERNEL_TEARDOWN_TOTAL_MS;

/// The worker's Harness close (pending commits flush, the lease releases)
/// after its kernel teardown.
pub const HARNESS_CLOSE_MS: u64 = 2_000;

/// The cooperative grace of every stop (ADR 0011): a routed `kill` or
/// `shutdown` gets this long to settle before the supervisor kills the
/// worker. It covers the longest kernel teardown and the Harness close.
pub const STOP_GRACE_MS: u64 = KERNEL_TEARDOWN_TOTAL_MS + HARNESS_CLOSE_MS;

/// After the stop grace, a worker gets SIGTERM, then this long to exit.
pub const WORKER_TERM_GRACE_MS: u64 = 2_000;

/// After SIGKILL, the supervisor waits this long for the worker's exit.
pub const WORKER_KILL_VERIFY_MS: u64 = 1_000;

/// The longest stop of one worker: the grace, SIGTERM, SIGKILL. Workers
/// stop in parallel, so this is the supervisor's drain too.
pub const SUPERVISOR_DRAIN_MS: u64 = STOP_GRACE_MS + WORKER_TERM_GRACE_MS + WORKER_KILL_VERIFY_MS;

/// What the launcher adds to the drain before it stops a supervisor that
/// did not exit (the supervisor's own exit after its last worker).
pub const LAUNCHER_DRAIN_MARGIN_MS: u64 = 2_000;

/// How long a launcher waits for a supervisor it asked to shut down
/// before it kills it: after the supervisor's whole drain.
pub const LAUNCHER_SHUTDOWN_WAIT_MS: u64 = SUPERVISOR_DRAIN_MS + LAUNCHER_DRAIN_MARGIN_MS;

/// An idle shutdown asks every worker to quiesce at the same time and
/// waits this long for all the answers (one window, not one per worker).
/// A worker that does not answer in time counts as busy.
pub const QUIESCE_ANSWER_MS: u64 = 5_000;

/// A quiesced worker opens its run gate again after this long when no
/// stop and no release came (its supervisor died while it decided). The
/// hold outlasts the answer window and then the stop's own grace, so a
/// committed shutdown reaches the worker before the gate opens.
pub const QUIESCE_HOLD_MS: u64 = QUIESCE_ANSWER_MS + STOP_GRACE_MS;

/// How long a parent waits for the kill of one RLM child session: the
/// parent's kill route grace, then the child's whole drain, then the
/// margin.
pub const RLM_CHILD_KILL_TIMEOUT_MS: u64 =
    STOP_GRACE_MS + SUPERVISOR_DRAIN_MS + LAUNCHER_DRAIN_MARGIN_MS;

/// A worker re-records its busy evidence this often while it has work.
pub const BUSY_REFRESH_MS: u64 = 5 * 60_000;

/// A boot this soon after a busy worker's crash revives it, however long
/// its run already took.
pub const REVIVAL_BOOT_WINDOW_MS: u64 = 25 * 60_000;

/// How long a `busy` recovery record still proves interrupted live work:
/// one refresh period plus the boot window. A record older than this is
/// residue of a run that already ended; the session stays down and reopens
/// through the next client create.
pub const REVIVAL_BUSY_EVIDENCE_MAX_AGE_MS: u64 = BUSY_REFRESH_MS + REVIVAL_BOOT_WINDOW_MS;

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

/// The window the restart failures are counted in (monotonic clock): the
/// give-up count of crash loops, each failure at most the longest pause
/// plus the loop period after the one before it.
pub const RESTART_WINDOW_MS: u64 =
    (RESTART_GIVE_UP_AFTER as u64 + 1) * (RESTART_MAX_BACKOFF_MS + RESTART_CRASH_LOOP_MS);
