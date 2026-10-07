//! This session's hold on the chat's root-turn lease (one root turn at a
//! time across every process on the chat). A root call takes it on its
//! first request; the logger takes it to log outside a call. Only the
//! logger gives it back: once every root conversation of the session is
//! idle and logged, or when the session closes. The lease belongs to the
//! chat connection, so a crash frees it.

use std::time::Duration;

use tokio::sync::{Mutex, MutexGuard};

use crate::durable::{TurnWait, TurnWaitSink};
use crate::memory::{Memory, TurnLease};

/// How long a call's lease request may take before the call counts as
/// waiting: a free chat grants within one round trip to its owner, so only
/// a turn queued behind another window's reports a wait.
const WAIT_SHOWN_AFTER: Duration = Duration::from_millis(250);

/// The lease, held or not.
#[derive(Default)]
pub(crate) struct TurnState {
    lease: Option<TurnLease>,
    /// The session closed: no lease is taken again.
    closed: bool,
}

impl TurnState {
    pub fn held(&self) -> bool {
        self.lease.is_some()
    }

    /// The session (re)opened: the lease may be taken again.
    pub fn open(&mut self) {
        self.closed = false;
    }

    /// Give the lease back to the owner.
    ///
    /// # Errors
    ///
    /// The owner cannot be reached.
    pub async fn release(&mut self) -> anyhow::Result<()> {
        match self.lease.take() {
            Some(lease) => lease.release().await,
            None => Ok(()),
        }
    }

    /// Give the lease back for good: the session closes.
    ///
    /// # Errors
    ///
    /// The owner cannot be reached.
    pub async fn close(&mut self) -> anyhow::Result<()> {
        self.closed = true;
        self.release().await
    }
}

/// The session's root turn. The state lock is held only briefly; waiting
/// for the owner's grant holds the acquire lock alone, so the logger can
/// decide about the lease while a call waits.
#[derive(Default)]
pub(crate) struct RootTurn {
    state: Mutex<TurnState>,
    acquire: Mutex<()>,
}

impl RootTurn {
    /// The lease state, exclusively.
    pub async fn lock(&self) -> MutexGuard<'_, TurnState> {
        self.state.lock().await
    }

    /// Take the lease when this session does not hold it.
    ///
    /// # Errors
    ///
    /// The owner cannot be reached, or the session closed.
    pub async fn ensure(&self, memory: &Memory) -> anyhow::Result<()> {
        let _acquiring = self.acquire.lock().await;
        {
            let state = self.state.lock().await;
            if state.closed {
                anyhow::bail!("the session closed");
            }
            if state.held() {
                return Ok(());
            }
        }
        let lease = memory.acquire_turn().await?;
        let mut state = self.state.lock().await;
        if state.closed {
            drop(state);
            lease.release().await?;
            anyhow::bail!("the session closed");
        }
        state.lease = Some(lease);
        Ok(())
    }

    /// Hold the lease for a root call. The logger keeps it while the call's
    /// run is live; a release that raced the claim is noticed under the
    /// state lock and the lease taken again. A wait behind another window's
    /// turn is reported to `sink`: `Waiting` once it has lasted
    /// [`WAIT_SHOWN_AFTER`], then `Cleared` when it ends however it ends
    /// (granted, failed, or dropped by an abort).
    ///
    /// # Errors
    ///
    /// The owner cannot be reached, or the session closed.
    pub async fn claim(&self, memory: &Memory, sink: Option<&TurnWaitSink>) -> anyhow::Result<()> {
        let claim = async {
            loop {
                self.ensure(memory).await?;
                if self.state.lock().await.held() {
                    return anyhow::Ok(());
                }
            }
        };
        tokio::pin!(claim);
        match tokio::time::timeout(WAIT_SHOWN_AFTER, &mut claim).await {
            Ok(claimed) => claimed,
            Err(_still_waiting) => {
                let _shown = sink.map(|sink| {
                    sink(TurnWait::Waiting);
                    ShownWait {
                        sink: TurnWaitSink::clone(sink),
                    }
                });
                claim.await
            }
        }
    }
}

/// A reported wait: [`TurnWait::Cleared`] when it drops.
struct ShownWait {
    sink: TurnWaitSink,
}

impl Drop for ShownWait {
    fn drop(&mut self) {
        (self.sink)(TurnWait::Cleared);
    }
}
