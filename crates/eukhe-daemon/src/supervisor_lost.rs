//! Worker orphan garbage collection: the supervisor-lost exit monitor, port
//! of the TS daemon-mode `startSupervisorMonitor` /
//! `checkSupervisorAvailability` / `exitIfSupervisorOrphanedForTooLong`.
//!
//! A session worker outlives its supervisor process: the supervisor spawns
//! it detached (its own process group), so a supervisor that dies without
//! a graceful stop — a crash, a SIGKILL from a test harness — leaves the
//! worker listening on a socket nobody will dial again. The TS product
//! garbage-collects such workers: while the supervisor socket stays
//! unreachable and no authenticated supervisor connection is held, the
//! worker exits after a bounded window instead of lingering forever.
//! Sessions persist on disk, and a later supervisor spawns fresh workers on
//! demand, so an unreachable-supervisor worker serves nothing by lingering.
//!
//! Divergence from TS, documented: the TS monitor first tries to launch a
//! replacement supervisor (`launchReplacementSupervisor`) and exits only
//! when that fails; the Rust port has no replacement-launch machinery yet,
//! so this monitor implements the TS give-up branch directly (exit after
//! the window). A supervisor restart inside the window is still seamless:
//! the socket's return resets the absence timer and the registration link
//! re-presents the worker's identity.
//!
//! Divergence from TS, documented: TS `hasOngoingSessionWork` defers the
//! give-up exit for as long as session work is in flight, with no upper
//! bound. Work that can never settle once the supervisor is gone — a run
//! wedged on a tool or a held host request, a queued input stranded behind
//! a failed run (nothing drains the inbox until the next prompt) — then
//! keeps the orphan alive forever. Here ongoing work defers the exit by at
//! most one more window ([`exit_due`]); the exit's session close aborts a
//! still-live run, and the durable session resumes it on a later
//! supervisor's demand.

use std::path::Path;
use std::sync::atomic::Ordering;
use std::sync::Arc;
use std::time::Duration;

use crate::worker::{Worker, WORKER_SUPERVISOR_LOST_EXIT_MS_ENV};

/// TS `DEFAULT_WORKER_SUPERVISOR_LOST_EXIT_MS`: five minutes.
const DEFAULT_LOST_EXIT_MS: u64 = 5 * 60_000;
/// TS `scheduleSupervisorAvailabilityCheck` cadence: the first check
/// 1.5s after boot, then every 5s.
const FIRST_CHECK: Duration = Duration::from_millis(1_500);
const CHECK_INTERVAL: Duration = Duration::from_secs(5);
/// Bounded probe: a supervisor socket that answers slower than this counts
/// as unreachable for the window bookkeeping.
const CONNECT_TIMEOUT: Duration = Duration::from_secs(1);

/// The supervisor-lost exit window (TS `workerSupervisorLostExitMs`): the
/// env override when it is a finite non-negative number, else the default.
fn lost_exit_ms() -> u64 {
    lost_exit_ms_from(
        std::env::var(WORKER_SUPERVISOR_LOST_EXIT_MS_ENV)
            .ok()
            .as_deref(),
    )
}

/// The TS parse contract: `Number(raw)` kept only when finite and >= 0.
fn lost_exit_ms_from(raw: Option<&str>) -> u64 {
    raw.and_then(|raw| raw.parse::<f64>().ok())
        .filter(|value| value.is_finite() && *value >= 0.0)
        .map_or(DEFAULT_LOST_EXIT_MS, |value| value as u64)
}

/// Whether the supervisor socket accepts connections (TS
/// `canConnectToSupervisor`): a connect that lands at all proves a live
/// supervisor owns the socket.
async fn supervisor_reachable(socket: &Path) -> bool {
    crate::socket::can_connect(socket, CONNECT_TIMEOUT).await
}

/// Arm the orphan-exit monitor for `worker` (a no-op task spawn; the
/// monitor runs for the worker process's whole lifetime, like the TS
/// `startSupervisorMonitor` timer chain).
pub(crate) fn start(worker: Arc<Worker>) {
    tokio::spawn(async move {
        monitor(worker).await;
    });
}

/// The availability-check loop. Every iteration mirrors the TS
/// `checkSupervisorAvailability` guard order: a shutdown in flight or a
/// live authenticated supervisor connection disarms the monitor, a
/// reachable socket resets the absence timer, and a socket that stays
/// unreachable exits the worker once [`exit_due`] says so.
async fn monitor(worker: Arc<Worker>) {
    let window = Duration::from_millis(lost_exit_ms());
    let mut absent_since: Option<tokio::time::Instant> = None;
    let mut delay = FIRST_CHECK;
    loop {
        tokio::time::sleep(delay).await;
        delay = CHECK_INTERVAL;
        if worker.core.lock().unwrap().shutdown_requested
            || worker.supervisor_claims.load(Ordering::SeqCst) > 0
        {
            absent_since = None;
            continue;
        }
        if supervisor_reachable(&worker.config.supervisor_socket_path).await {
            absent_since = None;
            continue;
        }
        let since = *absent_since.get_or_insert_with(tokio::time::Instant::now);
        // TS `hasOngoingSessionWork`: an active run owns the worker a
        // little longer; its turn end lets the next availability check
        // reconsider (bounded: see `exit_due`).
        let ongoing = worker.core.lock().unwrap().has_ongoing_work();
        if exit_due(since.elapsed(), window, ongoing) {
            exit_orphaned(&worker, since).await;
        }
    }
}

/// Whether a worker whose supervisor has been unreachable for `absent`
/// exits now: once the whole `window` passed with no session work in
/// flight, or — when work is still in flight — once a second window
/// passed too. The cap is what makes the exit bounded: work that can never
/// settle without a supervisor would otherwise defer it forever.
fn exit_due(absent: Duration, window: Duration, ongoing: bool) -> bool {
    if ongoing {
        absent >= window.saturating_mul(2)
    } else {
        absent >= window
    }
}

/// The TS give-up exit: dispose the session's kernel, persist the recovery
/// journal, close the listener and remove the worker's own socket file,
/// and end the process (the same sequence the routed `shutdown` command
/// runs: the session close aborts a run still in flight past the
/// ongoing-work cap, so nothing else needs to settle first). The kernel
/// dispose is the TS `shutdown(0)` close pass (`closeSession` -> runtime
/// dispose -> `IpythonKernelProvisioner.dispose`): the process exit runs
/// no destructors, so an undisposed kernel would be orphaned here.
async fn exit_orphaned(worker: &Worker, absent_since: tokio::time::Instant) {
    eprintln!(
        "eukhe-daemon worker: supervisor {} unreachable for {}s; exiting orphaned worker",
        worker.config.supervisor_socket_path.display(),
        absent_since.elapsed().as_secs()
    );
    worker.close_hosted_session().await;
    let _ = worker.record_recovery(false, "shutdown");
    // The listener closes FIRST and the cleanup probes the path with the
    // owner's bind provably released (the TS graceful-shutdown sequence,
    // shared with the routed `shutdown`), so both a REPLACED file and a
    // POISONED capture (a replacement landing in the bind->capture
    // window) spare a successor worker's live socket - the
    // deterministic-path relaunch - while the worker's own dead file
    // still unlinks through the identity gate.
    worker.close_listener_then_cleanup_socket().await;
    std::process::exit(0);
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The window parse is the TS `workerSupervisorLostExitMs` contract:
    /// any finite non-negative number wins, everything else (absent,
    /// garbage, negative, NaN) falls back to the default.
    #[test]
    fn lost_exit_window_parses_the_ts_contract() {
        assert_eq!(lost_exit_ms_from(None), DEFAULT_LOST_EXIT_MS);
        assert_eq!(lost_exit_ms_from(Some("garbage")), DEFAULT_LOST_EXIT_MS);
        assert_eq!(lost_exit_ms_from(Some("-1")), DEFAULT_LOST_EXIT_MS);
        assert_eq!(lost_exit_ms_from(Some("NaN")), DEFAULT_LOST_EXIT_MS);
        assert_eq!(lost_exit_ms_from(Some("0")), 0);
        assert_eq!(lost_exit_ms_from(Some("15000")), 15_000);
        assert_eq!(lost_exit_ms_from(Some("15000.5")), 15_000);
    }

    /// Idle workers exit at the window; in-flight work defers the exit by
    /// exactly one more window, never indefinitely.
    #[test]
    fn ongoing_work_defers_the_exit_by_at_most_one_more_window() {
        let window = Duration::from_secs(15);
        assert!(!exit_due(Duration::from_secs(14), window, false));
        assert!(exit_due(window, window, false));
        assert!(!exit_due(window, window, true));
        assert!(!exit_due(Duration::from_secs(29), window, true));
        assert!(exit_due(Duration::from_secs(30), window, true));
        assert!(exit_due(Duration::from_secs(7_200), window, true));
        assert!(exit_due(Duration::ZERO, Duration::ZERO, true));
    }

    fn lost_exit_ms_from(raw: Option<&str>) -> u64 {
        raw.and_then(|raw| raw.parse::<f64>().ok())
            .filter(|value| value.is_finite() && *value >= 0.0)
            .map_or(DEFAULT_LOST_EXIT_MS, |value| value as u64)
    }
}
