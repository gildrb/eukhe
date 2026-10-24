//! The OAuth refresh of an expired stored credential as a state machine:
//! one token fetch in flight per provider and document, its outcome given
//! to every caller that joined it, and the credential stored before the
//! flight ends. Each caller takes its refresh one [`Leg`] at a time.
//!
//! What follows each step is the compiled Bend core's decision
//! (`bend/ffi_auth_flight.bend` over `bend/auth_flight.bend` section The
//! decisions the Rust takes; laws `flight_ffi_*`, `flight_step_*` and
//! `flight_next_*_is_model`, `laws/auth_flight.bend`): [`Leg::advance`]
//! reads, fetches or writes and asks the core's call which leg follows;
//! [`FlightBook::advance`] asks the document's book, the core's stepper.
//! The Rust keeps the bytes (the credentials, the failures, a landed
//! flight's outcome under its number) and the interleaving: the threads,
//! the book's mutex and condvar, the unwind that lands a flight. The bridge
//! test (`flight/bridge.rs`) runs that dispatch over the core's decisions
//! and the model on the same interleavings.

use std::collections::HashMap;
use std::sync::{Condvar, Mutex, MutexGuard, PoisonError};

use eukhe_bend::wire::{Reader, WireError, Writer};
use eukhe_bend::{Entry, Stepper};

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

/// What a read, fetch or write found (the core's `Io`), with what it
/// found: the credential or the failure the next leg carries.
enum Found {
    LoadFresh(AuthCredential),
    LoadExpired,
    LoadFailed(String),
    CheckFresh(FlightId, AuthCredential),
    CheckExpired(FlightId),
    FetchOk(FlightId, AuthCredential),
    FetchFailed(FlightId, String),
    Stored(FlightId, Outcome),
}

/// A reply of the core that the request cannot give: an inconsistent build.
fn inconsistent(expected: &'static str) -> eukhe_bend::Error {
    WireError::Malformed { at: 0, expected }.into()
}

impl Leg {
    /// Take this leg's step that reads, fetches or writes. A step on the
    /// flights leaves the leg as it is.
    fn advance(self, io: &mut impl RefreshIo) -> Leg {
        let found = match self {
            Leg::Load => match io.load() {
                Ok(Some(credential)) => Found::LoadFresh(credential),
                Ok(None) => Found::LoadExpired,
                Err(cause) => Found::LoadFailed(cause),
            },
            Leg::Check(flight) => match io.check() {
                Some(credential) => Found::CheckFresh(flight, credential),
                None => Found::CheckExpired(flight),
            },
            Leg::Fetch(flight) => match io.fetch() {
                Ok(credential) => Found::FetchOk(flight, credential),
                Err(cause) => Found::FetchFailed(flight, cause),
            },
            Leg::Store(flight, credential) => Found::Stored(flight, io.store(credential)),
            Leg::Board | Leg::Land(..) | Leg::Wait(_) | Leg::Done(_) => return self,
        };
        eukhe_bend::expect_core(Entry::AuthFlight, follow(found))
    }
}

/// The leg after a step that found `found`: the core's call decides it;
/// the leg carries what was found. A flight number is the book's, so it
/// fits the wire.
fn follow(found: Found) -> Result<Leg, eukhe_bend::Error> {
    let mut request = Writer::new();
    let carried = match found {
        Found::LoadFresh(credential) => {
            request.tag(0);
            Some(Ok(credential))
        }
        Found::LoadExpired => {
            request.tag(1);
            None
        }
        Found::LoadFailed(cause) => {
            request.tag(2);
            Some(Err(cause))
        }
        Found::CheckFresh(FlightId(flight), credential) => {
            request.tag(3).nat(flight);
            Some(Ok(credential))
        }
        Found::CheckExpired(FlightId(flight)) => {
            request.tag(4).nat(flight);
            None
        }
        Found::FetchOk(FlightId(flight), credential) => {
            request.tag(5).nat(flight);
            Some(Ok(credential))
        }
        Found::FetchFailed(FlightId(flight), cause) => {
            request.tag(6).nat(flight);
            Some(Err(cause))
        }
        Found::Stored(FlightId(flight), outcome) => {
            request.tag(7).nat(flight);
            Some(outcome)
        }
    };
    let reply = eukhe_bend::call(Entry::AuthFlight, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let leg = match reader.tag_of(5, "the leg after a step")? {
        0 => Leg::Board,
        1 => Leg::Fetch(FlightId(reader.nat()?)),
        2 => {
            let flight = FlightId(reader.nat()?);
            match carried {
                Some(Ok(credential)) => Leg::Store(flight, credential),
                Some(Err(_)) | None => return Err(inconsistent("a store of a fetched credential")),
            }
        }
        3 => {
            let flight = FlightId(reader.nat()?);
            Leg::Land(
                flight,
                carried.ok_or_else(|| inconsistent("a land on what a step found"))?,
            )
        }
        // `tag_of` answers a tag below 5: this is 4.
        _ => Leg::Done(carried.ok_or_else(|| inconsistent("a refresh done with what it found"))?),
    };
    reader.end()?;
    Ok(leg)
}

/// The book's answer to one event (the core's `BOut`).
enum Answer {
    Lead(FlightId),
    Join(FlightId),
    Kept,
    Dropped,
    NotYet,
    Take,
    TakeLast,
    // Only the tests ask how many joined (`RefreshFlights::wait_for_joiners`).
    #[cfg_attr(not(test), allow(dead_code))]
    Joiners(Option<u64>),
}

/// The flights of one document: the book in the compiled core (who is in
/// flight, who joined, which landed outcome still waits for a joiner, the
/// next flight's number), and the outcomes it keeps, under their flight.
struct FlightBook {
    core: Stepper,
    landed: HashMap<FlightId, Outcome>,
}

impl FlightBook {
    /// An empty book.
    fn new() -> Self {
        FlightBook {
            core: eukhe_bend::expect_core(Entry::AuthFlight, open_book()),
            landed: HashMap::new(),
        }
    }

    /// Take this leg's step on the flights of `provider`. A step that
    /// reads, fetches or writes leaves the leg as it is.
    fn advance(&mut self, provider: &str, leg: Leg) -> Leg {
        eukhe_bend::expect_core(Entry::AuthFlight, self.advance_call(provider, leg))
    }

    fn advance_call(&mut self, provider: &str, leg: Leg) -> Result<Leg, eukhe_bend::Error> {
        Ok(match leg {
            Leg::Board => {
                let mut event = Writer::new();
                event.tag(0).str(provider);
                match self.ask(event)? {
                    Answer::Lead(flight) => Leg::Check(flight),
                    Answer::Join(flight) => Leg::Wait(flight),
                    Answer::Kept
                    | Answer::Dropped
                    | Answer::NotYet
                    | Answer::Take
                    | Answer::TakeLast
                    | Answer::Joiners(_) => return Err(inconsistent("a lead or a join")),
                }
            }
            Leg::Land(flight, outcome) => {
                let mut event = Writer::new();
                event.tag(1).str(provider).nat(flight.0);
                match self.ask(event)? {
                    Answer::Kept => {
                        self.landed.insert(flight, outcome.clone());
                    }
                    Answer::Dropped => {}
                    Answer::Lead(_)
                    | Answer::Join(_)
                    | Answer::NotYet
                    | Answer::Take
                    | Answer::TakeLast
                    | Answer::Joiners(_) => {
                        return Err(inconsistent("a kept or a dropped outcome"))
                    }
                }
                Leg::Done(outcome)
            }
            Leg::Wait(flight) => {
                let mut event = Writer::new();
                event.tag(2).nat(flight.0);
                match self.ask(event)? {
                    Answer::NotYet => Leg::Wait(flight),
                    Answer::Take => Leg::Done(
                        self.landed
                            .get(&flight)
                            .cloned()
                            .ok_or_else(|| inconsistent("a kept outcome"))?,
                    ),
                    Answer::TakeLast => Leg::Done(
                        self.landed
                            .remove(&flight)
                            .ok_or_else(|| inconsistent("a kept outcome"))?,
                    ),
                    Answer::Lead(_)
                    | Answer::Join(_)
                    | Answer::Kept
                    | Answer::Dropped
                    | Answer::Joiners(_) => return Err(inconsistent("an outcome or a wait")),
                }
            }
            Leg::Load | Leg::Check(_) | Leg::Fetch(_) | Leg::Store(..) | Leg::Done(_) => leg,
        })
    }

    /// The book's answer to `event`.
    fn ask(&mut self, mut event: Writer) -> Result<Answer, eukhe_bend::Error> {
        let reply = self.core.step(&event.finish()?)?;
        let mut reader = Reader::reply(&reply)?;
        let answer = match reader.tag_of(8, "an answer of the flight book")? {
            0 => Answer::Lead(FlightId(reader.nat()?)),
            1 => Answer::Join(FlightId(reader.nat()?)),
            2 => Answer::Kept,
            3 => Answer::Dropped,
            4 => Answer::NotYet,
            5 => Answer::Take,
            6 => Answer::TakeLast,
            // `tag_of` answers a tag below 8: this is 7.
            _ => Answer::Joiners(if reader.maybe()? {
                Some(reader.nat()?)
            } else {
                None
            }),
        };
        reader.end()?;
        Ok(answer)
    }
}

/// The core's stepper on an empty book (its reply is empty).
fn open_book() -> Result<Stepper, eukhe_bend::Error> {
    let (core, reply) = Stepper::open(Entry::AuthFlight, "")?;
    Reader::reply(&reply)?.end()?;
    Ok(core)
}

/// The refresh flights of one auth document, shared by every thread that
/// refreshes through it: the [`FlightBook`] under a mutex, and a condvar
/// that tells waiting callers the book changed.
pub struct RefreshFlights {
    book: Mutex<FlightBook>,
    changed: Condvar,
}

impl Default for RefreshFlights {
    fn default() -> Self {
        RefreshFlights {
            book: Mutex::new(FlightBook::new()),
            changed: Condvar::new(),
        }
    }
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
    pub(crate) fn wait_for_joiners(&self, provider: &str, joiners: u64) {
        let mut book = self.book();
        loop {
            let mut event = Writer::new();
            event.tag(3).str(provider);
            let answer = eukhe_bend::expect_core(Entry::AuthFlight, book.ask(event));
            if matches!(answer, Answer::Joiners(Some(n)) if n == joiners) {
                return;
            }
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
