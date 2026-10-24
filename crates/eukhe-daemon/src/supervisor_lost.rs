//! The worker's exit when its supervisor is lost (port of the TS
//! daemon-mode `startSupervisorMonitor` / `checkSupervisorAvailability` /
//! `exitIfSupervisorOrphanedForTooLong`).
//!
//! A session worker can outlive its supervisor: the supervisor spawns it
//! detached (in its own process group), so a supervisor that stops without
//! a graceful stop (a crash, a SIGKILL) leaves the worker without a
//! supervisor. The worker checks the supervisor socket every
//! [`WORKER_SUPERVISOR_CHECK_MS`]. When the socket answers again (an
//! attached client relaunches a lost supervisor), the absence timer resets
//! and the registration link shows the worker to the new supervisor.
//!
//! When the socket stays unreachable for the lost-exit window (default
//! [`crate::timeouts::Derived::worker_lost_exit_default_ms`];
//! [`orphan_decision`], the compiled Bend model `bend/ffi_orphan.bend`,
//! gives work in flight one more window), the worker exits. The exit never
//! aborts work that can resume (the law `orphan_never_aborts_resumable`,
//! `laws/orphan.bend`):
//!
//! - Without work ([`OrphanExit::Close`]), the worker closes its session
//!   and records it idle.
//! - With work ([`OrphanExit::Handover`]), the worker records its session
//!   busy and exits without an abort and without a session close. Its
//!   storage commits are already durable, so the next supervisor's boot
//!   revival resumes the run from storage.
//!
//! The decision and the closed admission happen in one critical section
//! of the session lock, so no new run starts after the decision.

use std::path::Path;
use std::sync::atomic::Ordering;
use std::sync::Arc;
use std::time::Duration;

use eukhe_bend::wire::NAT_MAX;
use eukhe_types::daemon::timing::WORKER_SUPERVISOR_CHECK_MS;

use crate::work_gate::{orphan_decision, orphan_exit, OrphanExit};
use crate::worker::{Worker, WORKER_SUPERVISOR_LOST_EXIT_MS_ENV};

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
        .map_or(
            crate::timeouts::derived().worker_lost_exit_default_ms,
            |value| value as u64,
        )
}

/// Whether the supervisor socket accepts connections (TS
/// `canConnectToSupervisor`): a connect that lands at all proves a live
/// supervisor owns the socket.
async fn supervisor_reachable(socket: &Path) -> bool {
    crate::socket::can_connect(socket, CONNECT_TIMEOUT).await
}

/// Start the orphan-exit monitor for `worker`. The monitor runs for the
/// whole life of the worker process.
pub(crate) fn start(worker: Arc<Worker>) {
    tokio::spawn(async move {
        monitor(worker).await;
    });
}

/// The availability-check loop. A shutdown in flight or a live
/// authenticated supervisor connection disarms the monitor, a reachable
/// socket resets the absence timer, and a socket that stays unreachable
/// exits the worker when the orphan decision says so: once the whole
/// window passed with no session work in flight, or, when work is in
/// flight, once a second window passed too (the laws
/// `orphan_idle_exit_due` and `orphan_work_exit_due`). The cap keeps the
/// exit bounded: work that cannot settle without a supervisor would
/// otherwise keep the worker alive forever.
async fn monitor(worker: Arc<Worker>) {
    // The Bend core's wire carries Nats up to NAT_MAX (about 3170 years of
    // ms): a window past it is `None` and never expires (the law
    // `orphan_capped_window_never_expires`); the absence saturates at it.
    let window_ms = Some(lost_exit_ms()).filter(|window| *window <= NAT_MAX);
    let check = Duration::from_millis(WORKER_SUPERVISOR_CHECK_MS);
    let mut checks = tokio::time::interval_at(tokio::time::Instant::now() + check, check);
    checks.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Delay);
    let mut absent_since: Option<tokio::time::Instant> = None;
    loop {
        checks.tick().await;
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
        let work = worker.session_work().await;
        let absent_ms = u64::try_from(since.elapsed().as_millis())
            .unwrap_or(u64::MAX)
            .min(NAT_MAX);
        if orphan_decision(window_ms, absent_ms, work).0 {
            let exit = leave_orphaned(&worker).await;
            eprintln!(
                "eukhe-daemon worker: supervisor {} unreachable for {}s; orphaned worker exits ({exit:?})",
                worker.config.supervisor_socket_path.display(),
                since.elapsed().as_secs()
            );
            std::process::exit(0);
        }
    }
}

/// Why a worker gives its work to the next supervisor.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum HandoverCause {
    /// The supervisor is lost (the orphan exit).
    Orphaned,
    /// A supervisor replacement asked for the work.
    Replaced,
}

impl HandoverCause {
    /// The recovery journal's operation of the handover record.
    fn operation(self) -> &'static str {
        match self {
            Self::Orphaned => "orphaned",
            Self::Replaced => "handover",
        }
    }
}

/// Give the session's work to the next supervisor: record the session
/// busy (the revival evidence), close the listener, and remove the
/// worker's own socket file. This does not abort the run and does not
/// close the session: the storage commits are already durable, and the
/// next supervisor's revival resumes the run. The caller must close the
/// admission (`shutdown_requested`) first, and ends the process after.
pub(crate) async fn hand_over(worker: &Worker, cause: HandoverCause) {
    let _ = worker.record_recovery(true, cause.operation());
    worker.close_listener_then_cleanup_socket().await;
}

/// The orphan exit without the process exit (the caller ends the
/// process). Close the admission under the session lock, then choose the
/// exit from the session's whole work ([`Worker::session_work`]: a
/// background job, an unsettled child or workflow run, a queued inbox
/// input count too); then run it. [`OrphanExit::Close`]
/// closes the session (nothing to abort; this also disposes its kernel,
/// because the process exit runs no destructors) and records it idle.
/// [`OrphanExit::Handover`] runs [`hand_over`]. Both close the listener
/// first and then remove only the worker's own socket file, so a
/// successor's live socket at the same path stays.
pub(crate) async fn leave_orphaned(worker: &Worker) -> OrphanExit {
    worker
        .core
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .shutdown_requested = true;
    let exit = orphan_exit(worker.session_work().await);
    match exit {
        OrphanExit::Close => {
            worker.close_hosted_session().await;
            let _ = worker.record_recovery(false, "shutdown");
            worker.close_listener_then_cleanup_socket().await;
        }
        OrphanExit::Handover => hand_over(worker, HandoverCause::Orphaned).await,
    }
    exit
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The window parse is the TS `workerSupervisorLostExitMs` contract:
    /// any finite non-negative number wins, everything else (absent,
    /// garbage, negative, NaN) falls back to the default.
    #[test]
    fn lost_exit_window_parses_the_ts_contract() {
        let parsed = [
            None,
            Some("garbage"),
            Some("-1"),
            Some("NaN"),
            Some("0"),
            Some("15000"),
            Some("15000.5"),
        ]
        .map(lost_exit_ms_from);
        let default = crate::timeouts::derived().worker_lost_exit_default_ms;
        assert_eq!(
            parsed,
            [default, default, default, default, 0, 15_000, 15_000]
        );
    }

    /// The Rust codec of the orphan call: the work's tag, the window's
    /// `Maybe`, the reply's flag and exit tag reach the compiled model and
    /// come back (the laws pin the decision itself).
    #[test]
    fn the_orphan_decision_crosses_the_core() {
        use crate::work_gate::Work;
        assert_eq!(
            orphan_decision(Some(15_000), 30_000, Work::Ongoing),
            (true, OrphanExit::Handover)
        );
        assert_eq!(
            orphan_decision(Some(15_000), 29_999, Work::Ongoing),
            (false, OrphanExit::Handover)
        );
        assert_eq!(
            orphan_decision(Some(15_000), 15_000, Work::Idle),
            (true, OrphanExit::Close)
        );
        assert_eq!(
            orphan_decision(None, NAT_MAX, Work::Idle),
            (false, OrphanExit::Close)
        );
    }
}
