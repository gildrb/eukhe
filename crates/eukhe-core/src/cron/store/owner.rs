//! The owner of cron dispatch claims: each dispatch record names the
//! process that claimed it ([`ProcessIdentity`]). This process's runs (the
//! dispatches it runs now) live in the compiled core
//! ([`eukhe_bend::rules::cron::Runs`]), which decides every update of a
//! jobs file: a claim adds the dispatches it makes, a finish of its own
//! run or the end of a run ([`RunningDispatch`] drops) removes one, and a
//! recovery reads them. This file holds the identity, the stepper and the
//! liveness probe the store asks about the other owners on record.

use std::sync::{Arc, LazyLock, Mutex, PoisonError};

use eukhe_bend::rules::cron::{Disk, Op, Runs, Served};
use eukhe_types::platform::process::ProcessIdentity;

use super::AgentCronDispatch;

/// How a claim owner judges whether another process still runs.
///
/// Implementations answer from the platform (pid and start identity) or,
/// in tests, from a simulated set of processes. A process that cannot be
/// judged counts as alive: to take over a live claim is worse than to wait.
pub(crate) trait OwnerLiveness: Send + Sync {
    /// Whether the process `owner` still runs.
    fn is_alive(&self, owner: &ProcessIdentity) -> bool;
}

/// The liveness the platform reports.
struct PlatformLiveness;

impl OwnerLiveness for PlatformLiveness {
    fn is_alive(&self, owner: &ProcessIdentity) -> bool {
        owner.is_alive()
    }
}

/// This process as the owner of cron dispatch claims.
pub(crate) struct ClaimOwner {
    identity: ProcessIdentity,
    /// The dispatches this process runs now, in the compiled core.
    runs: Mutex<Runs>,
    liveness: Box<dyn OwnerLiveness>,
}

/// The one owner of every store of this process: stores of one process
/// share their runs, so one store never clears the live claim of another.
static THIS_PROCESS: LazyLock<Arc<ClaimOwner>> = LazyLock::new(|| {
    Arc::new(ClaimOwner::new(
        ProcessIdentity::current(),
        Box::new(PlatformLiveness),
    ))
});

impl ClaimOwner {
    /// An owner with this identity, no runs, that judges other owners with
    /// `liveness`.
    #[must_use]
    pub(crate) fn new(identity: ProcessIdentity, liveness: Box<dyn OwnerLiveness>) -> Self {
        Self {
            identity,
            runs: Mutex::new(Runs::new()),
            liveness,
        }
    }

    /// The owner of this process.
    pub(crate) fn this_process() -> Arc<Self> {
        Arc::clone(&THIS_PROCESS)
    }

    pub(crate) fn identity(&self) -> &ProcessIdentity {
        &self.identity
    }

    pub(crate) fn is_alive(&self, owner: &ProcessIdentity) -> bool {
        self.liveness.is_alive(owner)
    }

    /// The update `op` of the file `disk` by this process, numbered `me`.
    pub(crate) fn serve(&self, me: u64, disk: &Disk<'_>, op: &Op<'_>) -> Served {
        self.runs
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .serve(me, disk, op)
    }

    fn end(&self, dispatch: &str) {
        self.runs
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .end(dispatch);
    }
}

/// A claimed dispatch this process runs. Its run is live until its result
/// is recorded or it drops (the pass that runs it unwinds). Then a
/// recovery of this process may clear a claim left on record.
pub struct RunningDispatch {
    dispatch: AgentCronDispatch,
    owner: Arc<ClaimOwner>,
}

impl RunningDispatch {
    pub(crate) fn new(dispatch: AgentCronDispatch, owner: Arc<ClaimOwner>) -> Self {
        Self { dispatch, owner }
    }

    #[must_use]
    pub fn dispatch(&self) -> &AgentCronDispatch {
        &self.dispatch
    }
}

impl Drop for RunningDispatch {
    fn drop(&mut self) {
        self.owner.end(&self.dispatch.id);
    }
}

/// Simulated processes for tests: a process is dead once its pid is in
/// the shared set.
#[cfg(test)]
struct SimulatedLiveness(Arc<Mutex<std::collections::HashSet<u32>>>);

#[cfg(test)]
impl OwnerLiveness for SimulatedLiveness {
    fn is_alive(&self, owner: &ProcessIdentity) -> bool {
        !self
            .0
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .contains(&owner.pid)
    }
}

#[cfg(test)]
impl ClaimOwner {
    /// The simulated process `pid`, which sees the processes in `dead` as
    /// dead.
    pub(crate) fn simulated(
        pid: u32,
        dead: &Arc<Mutex<std::collections::HashSet<u32>>>,
    ) -> Arc<Self> {
        Arc::new(Self::new(
            ProcessIdentity {
                pid,
                process_start_id: Some(format!("sim:{pid}")),
            },
            Box::new(SimulatedLiveness(Arc::clone(dead))),
        ))
    }
}
