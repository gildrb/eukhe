//! The OAuth refresh of an expired stored credential as a state machine:
//! one token fetch in flight per provider and document, its outcome given
//! to every caller that joined it, and the credential stored before the
//! flight ends. Each caller takes its refresh one [`Leg`] at a time:
//! [`Leg::advance`] takes the steps that read, fetch and write,
//! [`FlightBook::advance`] the steps on the flights. The model is
//! `bend/auth_flight.bend`, its laws `laws/auth_flight.bend`; the bridge
//! test (`flight/bridge.rs`) runs both on the same interleavings.

use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::sync::{Condvar, Mutex, MutexGuard, PoisonError};

use super::types::AuthCredential;

#[cfg(test)]
mod bridge;

/// What a refresh gives its caller: the credential to serve, or why there
/// is none.
pub(crate) type Outcome = Result<AuthCredential, String>;

/// One refresh flight of a document, numbered in the order flights start.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct FlightId(u64);

/// Where one caller's refresh stands.
enum Leg {
    /// Read the stored credential: a fresh one is served.
    Load,
    /// Join the provider's flight in flight, or start a flight and lead it.
    Board,
    /// The leader reads the stored credential again: a flight that landed
    /// after this caller's load stored a fresh one.
    Check(FlightId),
    /// The leader fetches a new credential.
    Fetch(FlightId),
    /// The leader stores the fetched credential.
    Store(FlightId, AuthCredential),
    /// The leader ends the flight with its outcome, after the store.
    Land(FlightId, Outcome),
    /// A caller that joined the flight waits for its outcome.
    Wait(FlightId),
    /// The refresh is over.
    Done(Outcome),
}

/// The reads, the fetch and the write of a refresh. The auth manager
/// implements it over the auth document and the OAuth integration; the
/// bridge test over a scripted document.
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

impl Leg {
    /// Take this leg's step that reads, fetches or writes. A step on the
    /// flights leaves the leg as it is.
    fn advance(self, io: &mut impl RefreshIo) -> Leg {
        match self {
            Leg::Load => match io.load() {
                Ok(Some(credential)) => Leg::Done(Ok(credential)),
                Ok(None) => Leg::Board,
                Err(cause) => Leg::Done(Err(cause)),
            },
            Leg::Check(flight) => match io.check() {
                Some(credential) => Leg::Land(flight, Ok(credential)),
                None => Leg::Fetch(flight),
            },
            Leg::Fetch(flight) => match io.fetch() {
                Ok(credential) => Leg::Store(flight, credential),
                Err(cause) => Leg::Land(flight, Err(cause)),
            },
            Leg::Store(flight, credential) => Leg::Land(flight, io.store(credential)),
            Leg::Board | Leg::Land(..) | Leg::Wait(_) | Leg::Done(_) => self,
        }
    }
}

/// A provider's flight in flight, and how many callers joined it.
struct Flying {
    flight: FlightId,
    joiners: usize,
}

/// A landed flight's outcome, until each of its joiners took it.
struct Landed {
    outcome: Outcome,
    waiting: usize,
}

/// The flights of one document.
#[derive(Default)]
struct FlightBook {
    flying: HashMap<String, Flying>,
    landed: HashMap<FlightId, Landed>,
    started: u64,
}

impl FlightBook {
    /// Take this leg's step on the flights of `provider`. A step that
    /// reads, fetches or writes leaves the leg as it is.
    fn advance(&mut self, provider: &str, leg: Leg) -> Leg {
        match leg {
            Leg::Board => match self.flying.entry(provider.to_owned()) {
                Entry::Occupied(mut flying) => {
                    flying.get_mut().joiners += 1;
                    Leg::Wait(flying.get().flight)
                }
                Entry::Vacant(free) => {
                    let flight = FlightId(self.started);
                    self.started += 1;
                    free.insert(Flying { flight, joiners: 0 });
                    Leg::Check(flight)
                }
            },
            Leg::Land(flight, outcome) => {
                if let Some(flying) = self.flying.remove(provider) {
                    if flying.joiners > 0 {
                        self.landed.insert(
                            flight,
                            Landed {
                                outcome: outcome.clone(),
                                waiting: flying.joiners,
                            },
                        );
                    }
                }
                Leg::Done(outcome)
            }
            Leg::Wait(flight) => match self.landed.entry(flight) {
                Entry::Vacant(_) => Leg::Wait(flight),
                Entry::Occupied(mut landed) if landed.get().waiting > 1 => {
                    landed.get_mut().waiting -= 1;
                    Leg::Done(landed.get().outcome.clone())
                }
                Entry::Occupied(landed) => Leg::Done(landed.remove().outcome),
            },
            Leg::Load | Leg::Check(_) | Leg::Fetch(_) | Leg::Store(..) | Leg::Done(_) => leg,
        }
    }
}

/// The refresh flights of one auth document, shared by every thread that
/// refreshes through it: the [`FlightBook`] under a mutex, and a condvar
/// that tells waiting callers the book changed.
#[derive(Default)]
pub struct RefreshFlights {
    book: Mutex<FlightBook>,
    changed: Condvar,
}

impl RefreshFlights {
    /// The book, recovered from a poisoned mutex: every step leaves the
    /// book whole, so a panic elsewhere cannot leave it half changed.
    fn book(&self) -> MutexGuard<'_, FlightBook> {
        self.book.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Run one caller's refresh of `provider` to its outcome. The steps
    /// that read, fetch and write run with no lock held; the steps on the
    /// flights run under the book's mutex. A caller that joined a flight
    /// blocks until the flight lands.
    pub(crate) fn refresh(&self, provider: &str, io: &mut impl RefreshIo) -> Outcome {
        let mut lead = Lead {
            flights: self,
            provider,
            flight: None,
        };
        let mut leg = Leg::Load;
        loop {
            leg = match leg {
                Leg::Done(outcome) => return outcome,
                Leg::Load | Leg::Check(_) | Leg::Fetch(_) | Leg::Store(..) => leg.advance(io),
                Leg::Board | Leg::Land(..) | Leg::Wait(_) => {
                    let mut book = self.book();
                    let mut next = book.advance(provider, leg);
                    self.changed.notify_all();
                    while let Leg::Wait(flight) = next {
                        book = self
                            .changed
                            .wait(book)
                            .unwrap_or_else(PoisonError::into_inner);
                        next = book.advance(provider, Leg::Wait(flight));
                    }
                    lead.flight = match next {
                        Leg::Check(flight) => Some(flight),
                        Leg::Load
                        | Leg::Board
                        | Leg::Fetch(_)
                        | Leg::Store(..)
                        | Leg::Land(..)
                        | Leg::Wait(_)
                        | Leg::Done(_) => None,
                    };
                    next
                }
            };
        }
    }
}

#[cfg(test)]
impl RefreshFlights {
    /// Block until `provider`'s flight in flight has `joiners` joiners.
    pub(crate) fn wait_for_joiners(&self, provider: &str, joiners: usize) {
        let mut book = self.book();
        while book.flying.get(provider).map(|flying| flying.joiners) != Some(joiners) {
            book = self
                .changed
                .wait(book)
                .unwrap_or_else(PoisonError::into_inner);
        }
    }
}

/// The flight a caller leads. A refresh that unwinds before it lands its
/// flight (a panic in the OAuth integration) lands it here with a failure,
/// so no caller that joined it waits forever.
struct Lead<'a> {
    flights: &'a RefreshFlights,
    provider: &'a str,
    flight: Option<FlightId>,
}

impl Drop for Lead<'_> {
    fn drop(&mut self) {
        if let Some(flight) = self.flight.take() {
            let outcome = Err(format!(
                "the token refresh of {} ended without an outcome",
                self.provider
            ));
            self.flights
                .book()
                .advance(self.provider, Leg::Land(flight, outcome));
            self.flights.changed.notify_all();
        }
    }
}
