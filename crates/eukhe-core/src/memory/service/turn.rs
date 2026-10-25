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
//! ends, polling it, so a cancelled wait leaves nothing behind. So two
//! turns never overlap, and nothing waits on a process that is gone.
//!
//! The lease itself runs as the compiled Bend core: `Turns` keeps one
//! state of the stepper `bend/ffi_lease.bend` (`eukhe_bend::rules::lease`),
//! sends it each ask, release and closed connection, and only delivers
//! the grants it answers. Its laws: `lease_*` in `laws/lease.bend` (H6).

use std::collections::HashMap;
use std::sync::atomic::Ordering;
use std::time::Duration;

use anyhow::Context as _;
use eukhe_bend::rules::lease::{Answer, Lease};
use tokio::sync::oneshot;

use super::{answered, unexpected, Disconnected, Link, Memory, Outcome, Reply, Request};

/// How often a granted lease tries the turn file of a holder from before
/// an owner change: a poll, not a blocking lock, so a dropped wait leaves
/// no thread behind that would still take the file (H6.2).
const TURN_FILE_POLL: Duration = Duration::from_millis(50);

/// The file a lease holder keeps locked for its whole turn.
pub(super) const TURN_FILE: &str = "turn";

/// Who asked the owner for a lease.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum Origin {
    /// The owner's own process.
    Local,
    /// One client connection, numbered by the owner.
    Connection(u64),
}

/// A lease at the owner: its asker names it, unique per origin.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct LeaseKey {
    origin: Origin,
    lease: u64,
}

/// The owner's side of the lease: the holder and the waiters live in the
/// compiled core, each named by the key its ask got there; here only each
/// lease's name and the reply of a waiter not granted yet.
#[derive(Debug, Default)]
pub(super) struct Turns {
    lease: Lease,
    /// The core's key of each lease it holds or queues.
    keys: HashMap<LeaseKey, u64>,
    /// Per core key: its lease, and the reply of a waiter not granted yet.
    leases: HashMap<u64, (LeaseKey, Option<oneshot::Sender<Outcome>>)>,
}

impl Turns {
    pub(super) fn acquire(&mut self, origin: Origin, lease: u64, reply: oneshot::Sender<Outcome>) {
        let key = LeaseKey { origin, lease };
        let (core, answer) = self.lease.ask(origin.number());
        self.keys.insert(key, core);
        self.leases.insert(core, (key, Some(reply)));
        self.act(answer);
    }

    /// End a lease, held or still waited for. A lease the core no longer
    /// holds (it ended with its connection, or before an owner change) is
    /// already over.
    pub(super) fn release(&mut self, origin: Origin, lease: u64) {
        if let Some(&core) = self.keys.get(&LeaseKey { origin, lease }) {
            let answer = self.lease.release(core);
            self.act(answer);
        }
    }

    /// A client connection closed: every lease it held or waited for ends.
    pub(super) fn closed(&mut self, connection: u64) {
        let answer = self.lease.crash(Origin::Connection(connection).number());
        self.act(answer);
    }

    /// Forget the leases the core ended, then deliver its grant. A waiter
    /// that stopped waiting (its reply is gone) never gets the lease: its
    /// grant is released at once and the core hands the lease on.
    fn act(&mut self, mut answer: Answer) {
        loop {
            for core in &answer.ended {
                if let Some((key, _)) = self.leases.remove(core) {
                    self.keys.remove(&key);
                }
            }
            let Some(core) = answer.grant else {
                return;
            };
            let reply = self
                .leases
                .get_mut(&core)
                .and_then(|(_, reply)| reply.take());
            match reply.map(|reply| reply.send(Outcome::Ok(Reply::Granted))) {
                Some(Ok(())) => return,
                Some(Err(_)) | None => answer = self.lease.release(core),
            }
        }
    }
}

impl Origin {
    /// The core's number of this origin: 0 the owner's own process, c + 1
    /// client connection c (one per accepted connection, far below the
    /// wire's bound of 10^14).
    fn number(self) -> u64 {
        match self {
            Origin::Local => 0,
            Origin::Connection(connection) => connection.saturating_add(1),
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
            let file = loop {
                match file.try_lock() {
                    Ok(()) => break file,
                    // A holder from before an owner change still runs its
                    // turn: wait for it to end.
                    Err(std::fs::TryLockError::WouldBlock) => {
                        tokio::time::sleep(TURN_FILE_POLL).await;
                    }
                    Err(std::fs::TryLockError::Error(error)) => {
                        return Err(anyhow::Error::new(error)
                            .context(format!("cannot lock the turn file {}", path.display())))
                    }
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
        let deadline = request.reply_deadline();
        let reply = match link {
            Link::Owner(owner) => owner.request(request).await?,
            Link::Client(client) => match answered(deadline, client.request(&request)).await? {
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
            // A stopped actor holds no leases.
            Link::Owner(owner) => owner.post(request),
            // The reply has no waiter, so the reader drops it. A closed
            // connection ended its leases at the owner already.
            Link::Client(client) => client.post(request),
        }
    }
}
