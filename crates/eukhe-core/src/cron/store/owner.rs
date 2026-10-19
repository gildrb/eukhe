//! The owner of cron dispatch claims: each dispatch record names the
//! process that claimed it ([`ProcessIdentity`]), and this process keeps
//! the set of the dispatches it runs now. A recovery clears a claim only
//! when it is this process's own claim with no live dispatch, or when its
//! owner is dead: the live claim of another process is never cleared.

use std::collections::HashSet;
use std::sync::{Arc, LazyLock, Mutex, PoisonError};

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
    /// The ids of the dispatches this process runs now.
    running: Mutex<HashSet<String>>,
    liveness: Box<dyn OwnerLiveness>,
}

/// The one owner of every store of this process: stores of one process
/// share their running dispatches, so one store never clears the live
/// claim of another.
static THIS_PROCESS: LazyLock<Arc<ClaimOwner>> = LazyLock::new(|| {
    Arc::new(ClaimOwner::new(
        ProcessIdentity::current(),
        Box::new(PlatformLiveness),
    ))
});

impl ClaimOwner {
    /// An owner with this identity that judges other owners with `liveness`.
    #[must_use]
    pub(crate) fn new(identity: ProcessIdentity, liveness: Box<dyn OwnerLiveness>) -> Self {
        Self {
            identity,
            running: Mutex::new(HashSet::new()),
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

    pub(crate) fn start_running(&self, dispatch_id: &str) {
        self.running
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .insert(dispatch_id.to_string());
    }

    pub(crate) fn stop_running(&self, dispatch_id: &str) {
        self.running
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .remove(dispatch_id);
    }

    /// Whether a recovery by this owner may clear the claim `dispatch_id`
    /// of `owner`: its own claim with no live dispatch, or a dead owner's.
    pub(crate) fn may_clear(&self, owner: &ProcessIdentity, dispatch_id: &str) -> bool {
        if *owner == self.identity {
            return !self
                .running
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .contains(dispatch_id);
        }
        !self.liveness.is_alive(owner)
    }
}

/// A claimed dispatch this process runs. Its run is live until it drops:
/// after the result is recorded, or when the pass that runs it unwinds.
/// Then a recovery of this process may clear a claim left on record.
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
        self.owner.stop_running(&self.dispatch.id);
    }
}

/// Simulated processes for tests: a process is dead once its pid is in
/// the shared set.
#[cfg(test)]
struct SimulatedLiveness(Arc<Mutex<HashSet<u32>>>);

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
    pub(crate) fn simulated(pid: u32, dead: &Arc<Mutex<HashSet<u32>>>) -> Arc<Self> {
        Arc::new(Self::new(
            ProcessIdentity {
                pid,
                process_start_id: Some(format!("sim:{pid}")),
            },
            Box::new(SimulatedLiveness(Arc::clone(dead))),
        ))
    }
}
