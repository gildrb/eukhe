//! The bridge between the refresh flights ([`Leg::advance`],
//! [`FlightBook::advance`]) and their Bend model (`bend/auth_flight.bend`,
//! whose laws `laws/auth_flight.bend` states and `PROOF.bend` proves): both
//! run the same interleavings and must print the same transcript, byte for
//! byte.
//!
//! A scenario is a list of events (`bend/bridge_auth_flight.bend` documents
//! the format): callers arrive and take their steps in any order, fetches
//! succeed or fail, a peer stores a fresh credential, the stored credential
//! expires. The Rust side drives one flight book and one leg per caller
//! over a scripted document, with the dispatch of
//! [`super::RefreshFlights::refresh`] (a waiting caller takes a step that
//! leaves it waiting instead of blocking), and prints after each event the
//! fetches, the stored credential and every caller's leg; the Bend side
//! builds `bend/bridge_auth_flight.bend` into a native binary and prints
//! the same from the model.
//!
//! [`compare`] runs it (and skips without `bend`, unless
//! `EUKHE_REQUIRE_BEND` is set).

use std::fmt::Write as _;

use eukhe_durable::testing::bridge::{compare, Rng, Scenario};

use super::{FlightBook, FlightId, Leg, Outcome, RefreshIo};
use crate::auth::types::AuthCredential;

const PROVIDER: &str = "x-bridge";

/// Credential `n` of a scenario: its access token is `c<n>`.
fn credential(n: u64) -> AuthCredential {
    AuthCredential::Oauth {
        access: format!("c{n}"),
        refresh: None,
        expires: 0,
        account_id: None,
        enterprise_url: None,
        endpoint: None,
        token_endpoint: None,
        client_id: None,
        resource: None,
        issuer: None,
    }
}

fn access(credential: &AuthCredential) -> &str {
    match credential {
        AuthCredential::Oauth { access, .. } => access,
        AuthCredential::ApiKey { key, .. } => key,
        AuthCredential::McpStaticToken { bearer, .. } => bearer,
    }
}

/// The number `n` of credential `c<n>`.
fn number(credential: &AuthCredential) -> u64 {
    access(credential)
        .trim_start_matches('c')
        .parse()
        .expect("a scenario credential is c<n>")
}

/// The scripted document: the stored credential and whether it is fresh,
/// the fetches made, and whether the next fetch succeeds. The n-th fetch
/// gives credential `c<n>` or failure `e<n>`.
struct Doc {
    stored: u64,
    fresh: bool,
    fetches: u64,
    fetch_ok: bool,
}

impl Doc {
    fn new() -> Self {
        Doc {
            stored: 0,
            fresh: false,
            fetches: 0,
            fetch_ok: true,
        }
    }
}

impl RefreshIo for Doc {
    fn load(&mut self) -> Result<Option<AuthCredential>, String> {
        Ok(self.check())
    }

    fn check(&mut self) -> Option<AuthCredential> {
        self.fresh.then(|| credential(self.stored))
    }

    fn fetch(&mut self) -> Outcome {
        self.fetches += 1;
        if self.fetch_ok {
            Ok(credential(self.fetches))
        } else {
            Err(format!("e{}", self.fetches))
        }
    }

    fn store(&mut self, fetched: AuthCredential) -> Outcome {
        if !self.fresh {
            self.stored = number(&fetched);
            self.fresh = true;
        }
        Ok(credential(self.stored))
    }
}

fn show_outcome(outcome: &Outcome) -> String {
    match outcome {
        Ok(credential) => access(credential).to_owned(),
        Err(cause) => cause.clone(),
    }
}

fn show_leg(leg: &Leg) -> String {
    match leg {
        Leg::Load => "L".to_owned(),
        Leg::Board => "B".to_owned(),
        Leg::Check(FlightId(flight)) => format!("C{flight}"),
        Leg::Fetch(FlightId(flight)) => format!("F{flight}"),
        Leg::Store(FlightId(flight), credential) => format!("S{flight}:{}", access(credential)),
        Leg::Land(FlightId(flight), outcome) => format!("N{flight}:{}", show_outcome(outcome)),
        Leg::Wait(FlightId(flight)) => format!("W{flight}"),
        Leg::Done(outcome) => format!("D:{}", show_outcome(outcome)),
    }
}

/// The scenarios as they run on the Rust state machine: their events, for
/// the model, and the transcript the state machine printed.
struct Run {
    book: FlightBook,
    doc: Doc,
    legs: Vec<Leg>,
    events: String,
    transcript: String,
}

impl Run {
    fn new() -> Self {
        Run {
            book: FlightBook::default(),
            doc: Doc::new(),
            legs: Vec::new(),
            events: String::new(),
            transcript: String::new(),
        }
    }

    /// A new world: a new book, the store holds credential 0, expired.
    fn reset(&mut self) {
        self.book = FlightBook::default();
        self.doc = Doc::new();
        self.legs.clear();
        self.events.push_str("9\n");
        self.transcript.push_str("new\n");
    }

    fn print(&mut self) {
        let legs = self.legs.iter().map(show_leg).collect::<Vec<_>>().join(",");
        let fresh = if self.doc.fresh { '+' } else { '-' };
        let _ = writeln!(
            self.transcript,
            "f={} s=c{}{fresh} c={legs}",
            self.doc.fetches, self.doc.stored
        );
    }

    fn arrive(&mut self) {
        self.legs.push(Leg::Load);
        self.events.push_str("0\n");
        self.print();
    }

    /// Caller `caller` takes its next step; a fetch at it succeeds when
    /// `fetch` says so.
    fn step(&mut self, caller: usize, fetch: Fetch) {
        self.doc.fetch_ok = matches!(fetch, Fetch::Succeeds);
        let leg = std::mem::replace(&mut self.legs[caller], Leg::Load);
        self.legs[caller] = match leg {
            Leg::Load | Leg::Check(_) | Leg::Fetch(_) | Leg::Store(..) => {
                leg.advance(&mut self.doc)
            }
            Leg::Board | Leg::Land(..) | Leg::Wait(_) | Leg::Done(_) => {
                self.book.advance(PROVIDER, leg)
            }
        };
        let _ = writeln!(self.events, "1 {caller} {}", u8::from(self.doc.fetch_ok));
        self.print();
    }

    /// A peer process stores a fresh, newer credential.
    fn peer(&mut self) {
        self.doc.stored += 1;
        self.doc.fresh = true;
        self.events.push_str("2\n");
        self.print();
    }

    fn expire(&mut self) {
        self.doc.fresh = false;
        self.events.push_str("3\n");
        self.print();
    }
}

/// How a fetch at a step ends.
#[derive(Clone, Copy)]
enum Fetch {
    Succeeds,
    Fails,
}

/// One world under random traffic: callers arrive and step in any order,
/// fetches fail a quarter of the time, peers write and credentials expire.
fn scenario(run: &mut Run, rng: &mut Rng, events: u64) {
    run.reset();
    for _ in 0..events {
        let callers = (0..run.legs.len()).collect::<Vec<_>>();
        let fetch = if rng.chance(75) {
            Fetch::Succeeds
        } else {
            Fetch::Fails
        };
        match (rng.below(100), rng.pick(&callers)) {
            (0..=14, _) | (_, None) => run.arrive(),
            (15..=89, Some(caller)) => run.step(caller, fetch),
            (90..=94, Some(_)) => run.peer(),
            (95..=u64::MAX, Some(_)) => run.expire(),
        }
    }
}

/// Every scenario, in one file: each starts a new world.
fn scenarios() -> Run {
    let mut run = Run::new();
    let mut rng = Rng(0x2545_f491_4f6c_dd1d);
    for _ in 0..300 {
        let events = rng.range(10, 80);
        scenario(&mut run, &mut rng, events);
    }
    run
}

#[test]
fn the_rust_flight_machine_equals_the_bend_model() {
    let run = scenarios();
    compare(
        "bend/bridge_auth_flight.bend",
        [Scenario {
            name: "every scenario".to_owned(),
            events: run.events,
            transcript: run.transcript,
        }],
    );
}

#[test]
fn a_caller_that_boards_before_the_store_joins_the_flight() {
    // The CI flake's window: the second caller loads the expired
    // credential while the first caller's fetch is in flight, and boards
    // after the fetch, before the flight ends. The flight stays in flight
    // until its credential is stored, so the second caller joins it and
    // never fetches; a third caller after the end loads the stored
    // credential.
    let mut run = Run::new();
    run.reset();
    run.arrive();
    run.arrive();
    for caller in [0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1] {
        run.step(caller, Fetch::Succeeds);
    }
    run.arrive();
    run.step(2, Fetch::Succeeds);
    assert_eq!(
        run.transcript,
        "new\n\
         f=0 s=c0- c=L\n\
         f=0 s=c0- c=L,L\n\
         f=0 s=c0- c=B,L\n\
         f=0 s=c0- c=C0,L\n\
         f=0 s=c0- c=F0,L\n\
         f=1 s=c0- c=S0:c1,L\n\
         f=1 s=c0- c=S0:c1,B\n\
         f=1 s=c1+ c=N0:c1,B\n\
         f=1 s=c1+ c=N0:c1,W0\n\
         f=1 s=c1+ c=N0:c1,W0\n\
         f=1 s=c1+ c=N0:c1,W0\n\
         f=1 s=c1+ c=D:c1,W0\n\
         f=1 s=c1+ c=D:c1,D:c1\n\
         f=1 s=c1+ c=D:c1,D:c1,L\n\
         f=1 s=c1+ c=D:c1,D:c1,D:c1\n"
    );
}
