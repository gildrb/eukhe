//! The OAuth refresh of an expired stored credential: one token fetch in
//! flight per provider and document, its outcome given to every caller
//! that joined it, and the credential stored before the flight ends.
//!
//! Every decision is the compiled Bend core's: one stepper per auth
//! document, the desk (`bend/ffi_auth_flight.bend` over
//! `bend/auth_flight.bend` section The desk the Rust runs; laws
//! `laws/auth_flight/`), and what each read of the auth document means
//! (`bend/ffi_auth_read.bend` over section The reads the Rust judges; laws
//! `auth_read_*`, `laws/auth_read.bend`): whether a stored credential is
//! fresh, whether a refresh can start, whether a peer's credential stands
//! at the store. This module is the event loop around them, with no
//! policy: each caller's thread sends the desk its caller's events in the
//! order they come (it arrives; its read, judged by the core, its fetch or
//! its write found something; it unwinds) under one mutex, delivers every
//! (caller, act) pair of the reply to that caller's mailbox, and takes its
//! own next act from its own mailbox. The reads, the fetch and the write
//! run with no lock held. An act that serves or stores a credential means
//! the payload of the event it answers, which the reporting thread holds:
//! the desk never sees a credential, and this module keeps none. No Rust
//! copy of a rule remains.

use std::collections::HashMap;
use std::sync::mpsc::{self, Sender};
#[cfg(test)]
use std::sync::Condvar;
use std::sync::{Mutex, MutexGuard, PoisonError};

use eukhe_bend::wire::{Reader, WireError, Writer, NAT_MAX};
use eukhe_bend::{Entry, Stepper};

use super::refresh_error::{AuthFileError, RefreshError};
use super::types::AuthCredential;

#[cfg(test)]
mod tests;

/// What a refresh gives its caller: the credential to serve, or why there
/// is none.
pub(crate) type Outcome = Result<AuthCredential, RefreshError>;

/// What a read of the auth document found under the provider.
#[allow(
    clippy::large_enum_variant,
    reason = "a read lives for one step; boxing the credential would allocate on every read"
)]
pub(crate) enum Stored {
    /// The document could not be read or parsed: why.
    Unreadable(AuthFileError),
    /// No credential under the provider.
    Missing,
    /// The provider's credential.
    Credential(AuthCredential),
}

/// One read of the auth document: what it found, and the clock (ms since
/// the epoch) when it read it.
pub(crate) struct Read {
    pub(crate) found: Stored,
    pub(crate) at: i64,
}

/// The reads, the fetch and the write of a refresh. The auth manager
/// implements it over the auth document and the OAuth integration; the
/// tests over a scripted document. The core judges what each read found.
pub(crate) trait RefreshIo {
    /// Read the provider's stored credential before the refresh boards.
    fn load(&mut self) -> Read;

    /// Read the provider's stored credential again, as the leader of a
    /// flight, before it fetches.
    fn check(&mut self) -> Read;

    /// A new credential from the token endpoint, or why none came back.
    fn fetch(&mut self) -> Outcome;

    /// Under the document's lock, read the provider's stored credential
    /// and ask `stands` whether it stands (a peer process refreshed
    /// meanwhile): if it does, write nothing and give it back; else write
    /// `credential` and give it back. `Err` when the write failed.
    fn store(&mut self, credential: AuthCredential, stands: &dyn Fn(&Read) -> bool) -> Outcome;
}

/// What a read is for (the core's `Ask`).
#[derive(Clone, Copy)]
enum Ask {
    Load,
    Check,
    Store,
}

/// The core's judgment of a read (its `Verdict`).
enum Verdict {
    /// The read credential is fresh: serve it, or land the flight on it.
    Serve,
    /// The read credential is not fresh: board, or fetch.
    Refresh,
    /// No refresh can start.
    Refuse,
    /// A peer's credential stands: the store writes nothing.
    KeepPeer,
    /// The store writes the fetched credential.
    Write,
}

/// What a read found, as the core reads it.
#[derive(Clone, Copy)]
enum Seen<'a> {
    Unreadable,
    Missing,
    Credential(&'a AuthCredential),
}

impl Read {
    fn seen(&self) -> Seen<'_> {
        match &self.found {
            Stored::Unreadable(_) => Seen::Unreadable,
            Stored::Missing => Seen::Missing,
            Stored::Credential(credential) => Seen::Credential(credential),
        }
    }
}

/// A clock or an expiry as the wire carries it: an instant before the
/// epoch as 0, one past the wire's largest Nat (the year 5138) as that
/// Nat. For every clock below it, `clock < expiry` reads the same.
fn wire_ms(ms: i64) -> u64 {
    u64::try_from(ms).unwrap_or(0).min(NAT_MAX)
}

/// The core's judgment, for `ask`, of what a read at `at` (ms since the
/// epoch) found.
fn judge(ask: Ask, at: i64, found: Seen<'_>) -> Result<Verdict, eukhe_bend::Error> {
    let mut request = Writer::new();
    request
        .tag(match ask {
            Ask::Load => 0,
            Ask::Check => 1,
            Ask::Store => 2,
        })
        .nat(wire_ms(at));
    match found {
        Seen::Unreadable => request.tag(0),
        Seen::Missing => request.tag(1),
        Seen::Credential(AuthCredential::ApiKey { .. } | AuthCredential::McpStaticToken { .. }) => {
            request.tag(2)
        }
        Seen::Credential(AuthCredential::Oauth { expires, .. }) => {
            request.tag(3).nat(wire_ms(*expires))
        }
    };
    let reply = eukhe_bend::call(Entry::AuthRead, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let verdict = match reader.tag_of(5, "a verdict on a read")? {
        0 => Verdict::Serve,
        1 => Verdict::Refresh,
        2 => Verdict::Refuse,
        3 => Verdict::KeepPeer,
        // `tag_of` answers a tag below 5: this is 4.
        _ => Verdict::Write,
    };
    reader.end()?;
    Ok(verdict)
}

/// Whether the stored credential `read` found stands against the fetched
/// one at the store: the core's judgment.
fn peer_stands(read: &Read) -> bool {
    let stands = judge(Ask::Store, read.at, read.seen()).and_then(|verdict| match verdict {
        Verdict::KeepPeer => Ok(true),
        Verdict::Write => Ok(false),
        Verdict::Serve | Verdict::Refresh | Verdict::Refuse => {
            Err(inconsistent("a kept peer or a write"))
        }
    });
    eukhe_bend::expect_core(Entry::AuthRead, stands)
}

/// Whether `credential` is fresh at `now` (ms since the epoch): the core's
/// judgment of a stored credential the auth lookup read.
pub(crate) fn fresh(credential: &AuthCredential, now: i64) -> bool {
    let fresh =
        judge(Ask::Check, now, Seen::Credential(credential)).and_then(|verdict| match verdict {
            Verdict::Serve => Ok(true),
            Verdict::Refresh => Ok(false),
            Verdict::Refuse | Verdict::KeepPeer | Verdict::Write => {
                Err(inconsistent("a serve or a refresh"))
            }
        });
    eukhe_bend::expect_core(Entry::AuthRead, fresh)
}

/// What a caller's read, fetch or write found (the desk's `Fd`), with the
/// payload the desk's acts may mean.
enum Found {
    LoadFresh(AuthCredential),
    LoadExpired,
    LoadFailed(RefreshError),
    CheckFresh(AuthCredential),
    CheckExpired,
    FetchOk(AuthCredential),
    FetchFailed(RefreshError),
    Stored(Outcome),
}

impl Found {
    /// Its code on the wire, and its payload.
    fn split(self) -> (u64, Option<Outcome>) {
        match self {
            Found::LoadFresh(credential) => (0, Some(Ok(credential))),
            Found::LoadExpired => (1, None),
            Found::LoadFailed(cause) => (2, Some(Err(cause))),
            Found::CheckFresh(credential) => (3, Some(Ok(credential))),
            Found::CheckExpired => (4, None),
            Found::FetchOk(credential) => (5, Some(Ok(credential))),
            Found::FetchFailed(cause) => (6, Some(Err(cause))),
            Found::Stored(outcome) => (7, Some(outcome)),
        }
    }

    /// What the load of a caller of `provider` found: the core's verdict
    /// on the read.
    fn load(provider: &str, read: Read) -> Found {
        let verdict = judge(Ask::Load, read.at, read.seen());
        let found = verdict.and_then(|verdict| match (verdict, read.found) {
            (Verdict::Serve, Stored::Credential(credential)) => Ok(Found::LoadFresh(credential)),
            (Verdict::Refresh, _) => Ok(Found::LoadExpired),
            (Verdict::Refuse, Stored::Unreadable(cause)) => Ok(Found::LoadFailed(cause.into())),
            (Verdict::Refuse, Stored::Missing) => Ok(Found::LoadFailed(RefreshError::NotStored {
                provider: provider.to_string(),
            })),
            (Verdict::Refuse, Stored::Credential(_)) => {
                Ok(Found::LoadFailed(RefreshError::NotOAuth {
                    provider: provider.to_string(),
                }))
            }
            (Verdict::Serve, Stored::Unreadable(_) | Stored::Missing)
            | (Verdict::KeepPeer | Verdict::Write, _) => {
                Err(inconsistent("a load's serve, refresh or refusal"))
            }
        });
        eukhe_bend::expect_core(Entry::AuthRead, found)
    }

    /// What the leader's check found: the core's verdict on the read.
    fn check(read: Read) -> Found {
        let verdict = judge(Ask::Check, read.at, read.seen());
        let found = verdict.and_then(|verdict| match (verdict, read.found) {
            (Verdict::Serve, Stored::Credential(credential)) => Ok(Found::CheckFresh(credential)),
            (Verdict::Refresh, _) => Ok(Found::CheckExpired),
            (Verdict::Serve, Stored::Unreadable(_) | Stored::Missing)
            | (Verdict::Refuse | Verdict::KeepPeer | Verdict::Write, _) => {
                Err(inconsistent("a check's serve or refresh"))
            }
        });
        eukhe_bend::expect_core(Entry::AuthRead, found)
    }
}

/// An act of the desk's reply (the core's `Act`).
enum Act {
    Load,
    Check,
    Fetch,
    Store,
    Wait,
    Done,
    Fail(String),
}

/// What a caller does next: an act, with the payload it means.
enum Order {
    Load,
    Check,
    Fetch,
    Store(AuthCredential),
    Wait,
    Done(Outcome),
    /// The flight this caller waited on ended without an outcome (its
    /// leader unwound): the core's text of the failure.
    Unlanded(String),
}

/// What a caller's order leads to: an event to report, a wait for its next
/// order, or the outcome of its refresh.
enum Next {
    Report(Found),
    Wait,
    Over(Outcome),
}

/// A reply of the core that the request cannot give: an inconsistent build.
fn inconsistent(expected: &'static str) -> eukhe_bend::Error {
    WireError::Malformed { at: 0, expected }.into()
}

/// The failure of a flight of `provider` whose leader unwound before it
/// landed: the core's `text` (`gone` in `bend/auth_flight.bend`), typed.
fn unlanded(provider: &str, text: &str) -> RefreshError {
    let cause = RefreshError::Unlanded {
        provider: provider.to_string(),
    };
    let typed = if cause.to_string() == text {
        Ok(())
    } else {
        Err(inconsistent(
            "the failure of a flight that ended without an outcome",
        ))
    };
    eukhe_bend::expect_core(Entry::AuthFlight, typed);
    cause
}

impl Act {
    /// The order this act gives, with the payload of the event it answers.
    fn order(self, payload: Option<&Outcome>) -> Result<Order, eukhe_bend::Error> {
        Ok(match self {
            Act::Load => Order::Load,
            Act::Check => Order::Check,
            Act::Fetch => Order::Fetch,
            Act::Store => match payload {
                Some(Ok(credential)) => Order::Store(credential.clone()),
                Some(Err(_)) | None => return Err(inconsistent("a store of a fetched credential")),
            },
            Act::Wait => Order::Wait,
            Act::Done => Order::Done(
                payload
                    .cloned()
                    .ok_or_else(|| inconsistent("a done with what an event found"))?,
            ),
            Act::Fail(cause) => Order::Unlanded(cause),
        })
    }
}

impl Order {
    /// Do this order for a caller of `provider`: the read (judged by the
    /// core), fetch or write it asks for.
    fn take(self, provider: &str, io: &mut impl RefreshIo) -> Next {
        match self {
            Order::Load => Next::Report(Found::load(provider, io.load())),
            Order::Check => Next::Report(Found::check(io.check())),
            Order::Fetch => Next::Report(match io.fetch() {
                Ok(credential) => Found::FetchOk(credential),
                Err(cause) => Found::FetchFailed(cause),
            }),
            Order::Store(credential) => {
                Next::Report(Found::Stored(io.store(credential, &peer_stands)))
            }
            Order::Wait => Next::Wait,
            Order::Done(outcome) => Next::Over(outcome),
            Order::Unlanded(text) => Next::Over(Err(unlanded(provider, &text))),
        }
    }
}

/// The desk of one document: the core's stepper, and the mailbox of each
/// live caller (removed when the caller's refresh ends).
struct Desk {
    core: Stepper,
    mailboxes: HashMap<u64, Sender<Order>>,
}

impl Desk {
    /// An empty desk (the stepper's open answers nothing).
    fn open() -> Result<Self, eukhe_bend::Error> {
        let (core, reply) = Stepper::open(Entry::AuthFlight, "")?;
        Reader::reply(&reply)?.end()?;
        Ok(Desk {
            core,
            mailboxes: HashMap::new(),
        })
    }

    /// The (caller, act) pairs the desk answers to `event`.
    fn pairs(&mut self, mut event: Writer) -> Result<Vec<(u64, Act)>, eukhe_bend::Error> {
        let reply = self.core.step(&event.finish()?)?;
        let mut reader = Reader::reply(&reply)?;
        let count = reader.count()?;
        let mut pairs = Vec::with_capacity(count);
        for _ in 0..count {
            let caller = reader.nat()?;
            let act = match reader.tag_of(7, "an act of the desk")? {
                0 => Act::Load,
                1 => Act::Check,
                2 => Act::Fetch,
                3 => Act::Store,
                4 => Act::Wait,
                5 => Act::Done,
                // `tag_of` answers a tag below 7: this is 6.
                _ => Act::Fail(reader.str()?.to_owned()),
            };
            pairs.push((caller, act));
        }
        reader.end()?;
        Ok(pairs)
    }

    /// Deliver each pair to its caller's mailbox; a caller whose refresh
    /// ends leaves the desk's mailboxes.
    fn deliver(
        &mut self,
        pairs: Vec<(u64, Act)>,
        payload: Option<&Outcome>,
    ) -> Result<(), eukhe_bend::Error> {
        for (caller, act) in pairs {
            let order = act.order(payload)?;
            let ends = matches!(order, Order::Done(_) | Order::Unlanded(_));
            self.mailboxes
                .get(&caller)
                .ok_or_else(|| inconsistent("an act for a live caller"))?
                .send(order)
                .map_err(|_| inconsistent("a live caller's mailbox"))?;
            if ends {
                self.mailboxes.remove(&caller);
            }
        }
        Ok(())
    }

    /// A caller of `provider` arrives with its mailbox: its number at the
    /// desk, the caller of the reply's one pair.
    fn arrive(&mut self, provider: &str, mailbox: Sender<Order>) -> Result<u64, eukhe_bend::Error> {
        let mut event = Writer::new();
        event.tag(0).str(provider);
        let pairs = self.pairs(event)?;
        let caller = match pairs.as_slice() {
            [(caller, _)] => *caller,
            _ => return Err(inconsistent("the arrival's one pair")),
        };
        self.mailboxes.insert(caller, mailbox);
        self.deliver(pairs, None)?;
        Ok(caller)
    }

    /// Caller `caller` found `found`.
    fn found(&mut self, caller: u64, found: Found) -> Result<(), eukhe_bend::Error> {
        let (code, payload) = found.split();
        let mut event = Writer::new();
        event.tag(1).nat(caller).nat(code);
        let pairs = self.pairs(event)?;
        self.deliver(pairs, payload.as_ref())
    }

    /// Caller `caller` left with no outcome.
    fn unwind(&mut self, caller: u64) -> Result<(), eukhe_bend::Error> {
        let mut event = Writer::new();
        event.tag(2).nat(caller);
        let pairs = self.pairs(event)?;
        self.mailboxes.remove(&caller);
        self.deliver(pairs, None)
    }

    /// How many wait on `provider`'s flight; `None` when it has none.
    #[cfg(test)]
    fn joiners(&mut self, provider: &str) -> Result<Option<u64>, eukhe_bend::Error> {
        let mut event = Writer::new();
        event.tag(3).str(provider);
        let reply = self.core.step(&event.finish()?)?;
        let mut reader = Reader::reply(&reply)?;
        let joiners = if reader.maybe()? {
            Some(reader.nat()?)
        } else {
            None
        };
        reader.end()?;
        Ok(joiners)
    }
}

/// The refresh flights of one auth document, shared by every thread that
/// refreshes through it: the [`Desk`] under a mutex (and, for the tests, a
/// condvar told after every event).
pub struct RefreshFlights {
    desk: Mutex<Desk>,
    #[cfg(test)]
    changed: Condvar,
}

impl Default for RefreshFlights {
    fn default() -> Self {
        RefreshFlights {
            desk: Mutex::new(eukhe_bend::expect_core(Entry::AuthFlight, Desk::open())),
            #[cfg(test)]
            changed: Condvar::new(),
        }
    }
}

impl RefreshFlights {
    /// The desk, recovered from a poisoned mutex: every event leaves the
    /// stepper whole, so a panic elsewhere cannot leave it half changed.
    fn desk(&self) -> MutexGuard<'_, Desk> {
        self.desk.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Send the desk one event under its mutex.
    fn event<T>(&self, send: impl FnOnce(&mut Desk) -> Result<T, eukhe_bend::Error>) -> T {
        let answer = eukhe_bend::expect_core(Entry::AuthFlight, send(&mut self.desk()));
        #[cfg(test)]
        self.changed.notify_all();
        answer
    }

    /// Run one caller's refresh of `provider` to its outcome: arrive, then
    /// do each act the desk sends to this caller's mailbox, and report what
    /// each read (as the core judges it), fetch or write found.
    pub(crate) fn refresh(&self, provider: &str, io: &mut impl RefreshIo) -> Outcome {
        let (sender, mailbox) = mpsc::channel();
        let mut caller = Caller {
            flights: self,
            id: self.event(|desk| desk.arrive(provider, sender)),
            done: false,
        };
        loop {
            let order = eukhe_bend::expect_core(
                Entry::AuthFlight,
                mailbox
                    .recv()
                    .map_err(|_| inconsistent("an act for a live caller")),
            );
            match order.take(provider, io) {
                Next::Report(found) => self.event(|desk| desk.found(caller.id, found)),
                Next::Wait => {}
                Next::Over(outcome) => {
                    caller.done = true;
                    return outcome;
                }
            }
        }
    }
}

#[cfg(test)]
impl RefreshFlights {
    /// Block until `provider`'s flight in flight has `joiners` joiners.
    pub(crate) fn wait_for_joiners(&self, provider: &str, joiners: u64) {
        let mut desk = self.desk();
        while eukhe_bend::expect_core(Entry::AuthFlight, desk.joiners(provider)) != Some(joiners) {
            desk = self
                .changed
                .wait(desk)
                .unwrap_or_else(PoisonError::into_inner);
        }
    }
}

/// One caller at the desk. Dropped before its refresh is done (a panic in
/// the OAuth integration), it tells the desk it unwound; the desk lands a
/// flight it led for the callers waiting on it.
struct Caller<'a> {
    flights: &'a RefreshFlights,
    id: u64,
    done: bool,
}

impl Drop for Caller<'_> {
    fn drop(&mut self) {
        if !self.done {
            let id = self.id;
            self.flights.event(|desk| desk.unwind(id));
        }
    }
}
