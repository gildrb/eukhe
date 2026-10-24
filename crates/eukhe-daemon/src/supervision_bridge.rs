//! The D1 bridges: the supervisor code its Bend models abstract (`laws/supervise.bend`,
//! `laws/revive.bend`, proved in `proof/supervise/` and `proof/revive/`) and
//! the models run the same scenarios and must print the same transcript,
//! byte for byte.
//!
//! - The timeouts against `bridge/bridge_supervise.bend` (they are `const`
//!   expressions: no core call can replace them).
//! - [`busy_evidence_fresh`] on the refresh schedule against
//!   `bridge/bridge_revive.bend`.
//!
//! The restart budget, the orphan exit and the replacement's gate, commit
//! and adoption run as their compiled models (`bend/ffi_supervise.bend`,
//! `bend/ffi_orphan.bend`, `bend/ffi_launcher.bend`): no bridge.
//!
//! Each `bridge/bridge_*.bend` file documents its events and its output.
//! [`compare`] runs them (and skips without `bend`, unless
//! `EUKHE_REQUIRE_BEND` is set).

use std::fmt::Write as _;

use eukhe_core::kernel::shared::{
    HOST_REQUEST_SHUTDOWN_TIMEOUT_MS, KERNEL_KILL_VERIFY_MS, KERNEL_SHUTDOWN_TIMEOUT_MS,
    KERNEL_TEARDOWN_TOTAL_MS, KERNEL_TERM_GRACE_MS, SNAPSHOT_EXECUTION_TIMEOUT_MS,
};
use eukhe_durable::testing::bridge::{compare, Rng, Scenario};
use eukhe_types::daemon::timing::{
    CLIENT_RELAUNCH_WITHIN_MS, DAEMON_STARTUP_TIMEOUT_MS, WORKER_LOST_EXIT_DEFAULT_MS,
    WORKER_LOST_EXIT_SLACK_MS, WORKER_SUPERVISOR_CHECK_MS,
};

use crate::revival_gate::busy_evidence_fresh;
use crate::timeouts::{
    BUSY_REFRESH_MS, HARNESS_CLOSE_MS, LAUNCHER_DRAIN_MARGIN_MS, LAUNCHER_SHUTDOWN_WAIT_MS,
    QUIESCE_ANSWER_MS, QUIESCE_HOLD_MS, RESTART_CRASH_LOOP_MS, RESTART_GIVE_UP_AFTER,
    RESTART_MAX_BACKOFF_MS, RESTART_WINDOW_MS, REVIVAL_BOOT_WINDOW_MS,
    REVIVAL_BUSY_EVIDENCE_MAX_AGE_MS, RLM_CHILD_KILL_TIMEOUT_MS, STOP_GRACE_MS,
    SUPERVISOR_DRAIN_MS, WORKER_KILL_VERIFY_MS, WORKER_TERM_GRACE_MS,
};

/// The revival model counts time in seconds.
const REVIVE_UNIT_MS: u64 = 1_000;

fn units(ms: u64, unit: u64) -> u64 {
    assert_eq!(ms % unit, 0, "{ms} ms is not a multiple of {unit} ms");
    ms / unit
}

/// The timeouts' base values and the derived values, as the Rust
/// constants hold them.
fn timeouts_scenario() -> (String, String) {
    let events = format!(
        "t {SNAPSHOT_EXECUTION_TIMEOUT_MS} {HOST_REQUEST_SHUTDOWN_TIMEOUT_MS} {KERNEL_SHUTDOWN_TIMEOUT_MS} {KERNEL_TERM_GRACE_MS} {KERNEL_KILL_VERIFY_MS} {HARNESS_CLOSE_MS} {WORKER_TERM_GRACE_MS} {WORKER_KILL_VERIFY_MS} {LAUNCHER_DRAIN_MARGIN_MS} {BUSY_REFRESH_MS} {REVIVAL_BOOT_WINDOW_MS} {CLIENT_RELAUNCH_WITHIN_MS} {DAEMON_STARTUP_TIMEOUT_MS} {WORKER_SUPERVISOR_CHECK_MS} {WORKER_LOST_EXIT_SLACK_MS} {RESTART_GIVE_UP_AFTER} {RESTART_MAX_BACKOFF_MS} {RESTART_CRASH_LOOP_MS} {QUIESCE_ANSWER_MS}\n"
    );
    let transcript = format!(
        "t {KERNEL_TEARDOWN_TOTAL_MS} {STOP_GRACE_MS} {SUPERVISOR_DRAIN_MS} {LAUNCHER_SHUTDOWN_WAIT_MS} {RLM_CHILD_KILL_TIMEOUT_MS} {WORKER_LOST_EXIT_DEFAULT_MS} {REVIVAL_BUSY_EVIDENCE_MAX_AGE_MS} {QUIESCE_HOLD_MS} {RESTART_WINDOW_MS}\n"
    );
    (events, transcript)
}

/// The timeouts as derived.
#[test]
fn the_timeouts_derive_as_their_model() {
    let (events, transcript) = timeouts_scenario();
    compare(
        "bridge/bridge_supervise.bend",
        [Scenario {
            name: "timeouts".to_owned(),
            events,
            transcript,
        }],
    );
}

/// Runs of any length, crashes anywhere, boots near the boot window's
/// edge: a busy worker records at its run start and then every refresh.
#[test]
fn the_revival_runs_as_its_model() {
    let mut rng = Rng(0x0de1_7a11);
    let refresh = units(BUSY_REFRESH_MS, REVIVE_UNIT_MS);
    let boot = units(REVIVAL_BOOT_WINDOW_MS, REVIVE_UNIT_MS);
    let start_ms = 1_700_000_000_000u64;
    let mut events = String::new();
    let mut transcript = String::new();
    for _ in 0..80 {
        let crash = match rng.below(3) {
            0 => rng.range(0, refresh * 2),
            1 => rng.range(0, 12 * 60 * 60),
            _ => refresh * rng.range(1, 30) + rng.range(0, 2) - 1,
        };
        // The edge of the max age too: the evidence one second younger,
        // exactly as old, and one second older.
        let delay = match rng.below(3) {
            0 => rng.range(boot.saturating_sub(refresh), boot + refresh),
            1 => refresh + boot - crash % refresh + rng.range(0, 2) - 1,
            _ => rng.range(0, boot * 2),
        };
        writeln!(events, "v {refresh} {boot} {crash} {delay}").unwrap();
        let last_record_ms = start_ms + (crash / refresh) * refresh * REVIVE_UNIT_MS;
        let boot_ms = start_ms + (crash + delay) * REVIVE_UNIT_MS;
        let fresh = busy_evidence_fresh(last_record_ms, boot_ms);
        writeln!(transcript, "v {}", u8::from(fresh)).unwrap();
    }
    compare(
        "bridge/bridge_revive.bend",
        [Scenario {
            name: "long runs".to_owned(),
            events,
            transcript,
        }],
    );
}
