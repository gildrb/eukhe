//! The chat's root-turn lease: many windows are one chat, and its root
//! turns run one at a time, in the order they asked.
//!
//! The owner keeps the lease: one holder, then the waiters in arrival
//! order. A lease belongs to the connection that asked for it (or to the
//! owner's own process) and ends when its holder releases or drops it,
//! when its waiter stops waiting, or when that connection closes, so a
//! client that crashes frees the chat at once.
//!
//! When the owner itself goes away, its leases go with it: the next owner
//! starts with no holder, while a client that held the lease may still be
//! running its turn. The turn file, `chat/turn`, keeps the two turns
//! apart: a holder locks it once the owner grants the lease and unlocks it
//! before releasing, and the OS unlocks it when the holder dies. A lease
//! the new owner grants waits on the file until the old holder's turn
//! ends. So two turns never overlap, and nothing waits on a process that
//! is gone.

use std::collections::VecDeque;
use std::sync::atomic::Ordering;

use anyhow::Context as _;
use tokio::sync::oneshot;

use super::{
    unexpected, ClientFrame, Command, Disconnected, Link, Memory, Outcome, Reply, Request,
};

/// The file a lease holder keeps locked for its whole turn.
pub(super) const TURN_FILE: &str = "turn";

/// Who asked the owner for a lease.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Origin {
    /// The owner's own process.
    Local,
    /// One client connection, numbered by the owner.
    Connection(u64),
}

/// A lease at the owner: its asker names it, unique per origin.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct LeaseKey {
    origin: Origin,
    lease: u64,
}

/// The owner's side of the lease: the holder, then the waiters in arrival
/// order.
#[derive(Debug, Default)]
pub(super) struct Turns {
    holder: Option<LeaseKey>,
    waiting: VecDeque<(LeaseKey, oneshot::Sender<Outcome>)>,
}

impl Turns {
    pub(super) fn acquire(&mut self, origin: Origin, lease: u64, reply: oneshot::Sender<Outcome>) {
        self.waiting.push_back((LeaseKey { origin, lease }, reply));
        self.grant_next();
    }

    /// End a lease, held or still waited for. A lease the owner does not
    /// know (it ended with its connection, or before an owner change) is
    /// already over.
    pub(super) fn release(&mut self, origin: Origin, lease: u64) {
        let key = LeaseKey { origin, lease };
        if self.holder == Some(key) {
            self.holder = None;
        } else {
            self.waiting.retain(|(waiter, _)| *waiter != key);
        }
        self.grant_next();
    }

    /// A client connection closed: every lease it held or waited for ends.
    pub(super) fn closed(&mut self, connection: u64) {
        let origin = Origin::Connection(connection);
        if self.holder.is_some_and(|holder| holder.origin == origin) {
            self.holder = None;
        }
        self.waiting.retain(|(waiter, _)| waiter.origin != origin);
        self.grant_next();
    }

    fn grant_next(&mut self) {
        while self.holder.is_none() {
            let Some((key, reply)) = self.waiting.pop_front() else {
                return;
            };
            // A waiter that stopped waiting is passed over; its release
            // (or its connection's close) comes after and finds nothing.
            if reply.send(Outcome::Ok(Reply::Granted)).is_ok() {
                self.holder = Some(key);
            }
        }
    }
}

impl Memory {
    /// Wait for, then hold, the chat's root-turn lease: one root turn at a
    /// time across every process on the chat, in the order they asked.
    /// Dropping the future cancels the wait; a lease granted meanwhile ends
    /// at once.
    ///
    /// # Errors
    ///
    /// Returns an error when the owner cannot be reached or the turn file
    /// cannot be locked.
    #[tracing::instrument(name = "chat_memory.acquire_turn", skip_all)]
    pub async fn acquire_turn(&self) -> anyhow::Result<TurnLease> {
        let lease = self.inner.next_lease.fetch_add(1, Ordering::SeqCst);
        for _ in 0..4 {
            let link = self.link().await?;
            // From here a dropped future ends the lease at the owner,
            // whether it is still waited for or already granted.
            let mut release = LeaseRelease {
                link: Some(link.clone()),
                lease,
            };
            let reply = match &link {
                Link::Owner(owner) => owner.request(Request::AcquireTurn { lease }).await?,
                Link::Client(client) => match client.request(&Request::AcquireTurn { lease }).await
                {
                    Ok(Outcome::Ok(reply)) => reply,
                    Ok(Outcome::Error(error)) => return Err(anyhow::anyhow!(error)),
                    Err(Disconnected) => {
                        // The connection is gone, and every lease of it
                        // with it: ask again on the next link.
                        release.link = None;
                        self.forget(client).await;
                        continue;
                    }
                },
            };
            match reply {
                Reply::Granted => {}
                other => return Err(unexpected(&other)),
            }
            let path = self.inner.dir.join(TURN_FILE);
            let file = std::fs::OpenOptions::new()
                .create(true)
                .truncate(false)
                .write(true)
                .open(&path)
                .with_context(|| format!("cannot open the turn file {}", path.display()))?;
            let file = match file.try_lock() {
                Ok(()) => file,
                // A holder from before an owner change still runs its
                // turn: wait for it on a blocking thread. A wait that is
                // cancelled unlocks the file as soon as it gets it (the
                // file drops with the unread result).
                Err(std::fs::TryLockError::WouldBlock) => {
                    tokio::task::spawn_blocking(move || file.lock().map(|()| file))
                        .await
                        .context("the turn file wait stopped")?
                        .with_context(|| format!("cannot lock the turn file {}", path.display()))?
                }
                Err(std::fs::TryLockError::Error(error)) => {
                    return Err(anyhow::Error::new(error)
                        .context(format!("cannot lock the turn file {}", path.display())))
                }
            };
            return Ok(TurnLease { file, release });
        }
        anyhow::bail!(
            "the chat memory at {} keeps losing its owner",
            self.inner.dir.display()
        )
    }
}

/// The chat's root-turn lease, from [`Memory::acquire_turn`] until
/// [`TurnLease::release`] or drop.
#[must_use = "the turn's lease ends when it is dropped"]
pub struct TurnLease {
    // Declared first, so it drops first: the turn file unlocks before the
    // owner hands the lease on.
    file: std::fs::File,
    release: LeaseRelease,
}

impl std::fmt::Debug for TurnLease {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("TurnLease")
            .field("lease", &self.release.lease)
            .finish_non_exhaustive()
    }
}

impl TurnLease {
    /// End the turn: unlock the turn file, then hand the lease on.
    ///
    /// # Errors
    ///
    /// Returns an error when the owner cannot take the release. A lease
    /// whose connection is gone has ended already.
    #[tracing::instrument(name = "chat_memory.release_turn", skip_all)]
    pub async fn release(self) -> anyhow::Result<()> {
        let TurnLease { file, mut release } = self;
        drop(file);
        let Some(link) = release.link.take() else {
            return Ok(());
        };
        let request = Request::Release {
            lease: release.lease,
        };
        let reply = match link {
            Link::Owner(owner) => owner.request(request).await?,
            Link::Client(client) => match client.request(&request).await {
                Ok(Outcome::Ok(reply)) => reply,
                Ok(Outcome::Error(error)) => return Err(anyhow::anyhow!(error)),
                // The owner ended the connection's leases when it closed.
                Err(Disconnected) => return Ok(()),
            },
        };
        match reply {
            Reply::Released => Ok(()),
            other => Err(unexpected(&other)),
        }
    }
}

/// Ends one lease at the owner when dropped, so a cancelled wait or a
/// dropped lease never leaves the chat held.
struct LeaseRelease {
    /// `None` once ended, or when the connection the lease belongs to is
    /// gone.
    link: Option<Link>,
    lease: u64,
}

impl Drop for LeaseRelease {
    fn drop(&mut self) {
        let Some(link) = self.link.take() else {
            return;
        };
        let request = Request::Release { lease: self.lease };
        match link {
            Link::Owner(owner) => {
                let (reply, _) = oneshot::channel();
                // A stopped actor holds no leases.
                let _ = owner.commands.send(Command::Request {
                    origin: Origin::Local,
                    request,
                    reply,
                });
            }
            Link::Client(client) => {
                // The reply has no waiter, so the reader drops it. A closed
                // connection ended its leases at the owner already.
                let _ = client.send(&ClientFrame::Request {
                    id: client.next_id.fetch_add(1, Ordering::SeqCst),
                    request,
                });
            }
        }
    }
}
