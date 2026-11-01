//! The OAuth refresh of an expired stored credential: one token fetch in
//! flight per provider and document, its outcome given to every caller
//! that joined it, and the credential stored before the flight ends.
//!
//! Every decision is the compiled Bend core's: one stepper per auth
//! document, the desk (`bend/ffi_auth_flight.bend` over
//! `bend/auth_flight.bend` section The desk the Rust runs; laws
//! `laws/auth_flight/`). This module is the event loop around it, with no
//! policy: each caller's thread sends the desk its caller's events in the
//! order they come (it arrives; its read, fetch or write found something;
//! it unwinds) under one mutex, delivers every (caller, act) pair of the
//! reply to that caller's mailbox, and takes its own next act from its own
//! mailbox. The reads, the fetch and the write run with no lock held. An
//! act that serves or stores a credential means the payload of the event
//! it answers, which the reporting thread holds: the desk never sees a
//! credential, and this module keeps none.

use std::collections::HashMap;
use std::sync::mpsc::{self, Sender};
#[cfg(test)]
use std::sync::Condvar;
use std::sync::{Mutex, MutexGuard, PoisonError};

use eukhe_bend::wire::{Reader, WireError, Writer};
use eukhe_bend::{Entry, Stepper};

use super::types::AuthCredential;

/// What a refresh gives its caller: the credential to serve, or why there
/// is none.
pub(crate) type Outcome = Result<AuthCredential, String>;

/// The reads, the fetch and the write of a refresh. The auth manager
/// implements it over the auth document and the OAuth integration.
pub(crate) trait RefreshIo {
    /// The stored credential when it is fresh, `None` when it expired, or
    /// why no refresh can start (no stored OAuth credential, an unreadable
    /// document).
    fn load(&mut self) -> Result<Option<AuthCredential>, String>;

    /// The stored credential when it is fresh now; `None` when it expired
    /// or the document cannot be read.
    fn check(&mut self) -> Option<AuthCredential>;

    /// A new credential from the token endpoint, or why none came back.
    fn fetch(&mut self) -> Outcome;

    /// Store `credential`, unless the stored credential is fresh (a peer
    /// process refreshed meanwhile): the stored credential after the
    /// write, or why the write failed.
    fn store(&mut self, credential: AuthCredential) -> Outcome;
}

/// What a caller's read, fetch or write found (the desk's `Fd`), with the
/// payload the desk's acts may mean.
enum Found {
    LoadFresh(AuthCredential),
    LoadExpired,
    LoadFailed(String),
    CheckFresh(AuthCredential),
    CheckExpired,
    FetchOk(AuthCredential),
    FetchFailed(String),
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
}

/// A reply of the core that the request cannot give: an inconsistent build.
fn inconsistent(expected: &'static str) -> eukhe_bend::Error {
    WireError::Malformed { at: 0, expected }.into()
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
            Act::Fail(cause) => Order::Done(Err(cause)),
        })
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
            let ends = matches!(order, Order::Done(_));
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
    /// each read, fetch or write found.
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
            let found = match order {
                Order::Load => match io.load() {
                    Ok(Some(credential)) => Found::LoadFresh(credential),
                    Ok(None) => Found::LoadExpired,
                    Err(cause) => Found::LoadFailed(cause),
                },
                Order::Check => match io.check() {
                    Some(credential) => Found::CheckFresh(credential),
                    None => Found::CheckExpired,
                },
                Order::Fetch => match io.fetch() {
                    Ok(credential) => Found::FetchOk(credential),
                    Err(cause) => Found::FetchFailed(cause),
                },
                Order::Store(credential) => Found::Stored(io.store(credential)),
                Order::Wait => continue,
                Order::Done(outcome) => {
                    caller.done = true;
                    return outcome;
                }
            };
            self.event(|desk| desk.found(caller.id, found));
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
