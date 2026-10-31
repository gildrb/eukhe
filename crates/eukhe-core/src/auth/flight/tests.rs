//! The refresh flights through the compiled core: what a read means
//! (entry `auth_read`), which leg follows each step (entry `auth_flight`,
//! its call) and the document's book (its stepper), with the outcomes the
//! Rust keeps for each landed flight. Each transcript steps the callers by
//! hand, in the order a scenario picks, over a scripted document whose
//! clock and expiries the core judges.

use std::fmt::Write as _;

use super::{fresh, FlightBook, FlightId, Leg, Outcome, Read, RefreshFlights, RefreshIo, Stored};
use crate::auth::types::AuthCredential;

const PROVIDER: &str = "x-flight";

/// How long a peer's credential stays fresh after the peer writes it, in
/// ms.
const LIFETIME: i64 = 1000;

/// How long a fetched credential stays fresh after the fetch, in ms.
const FETCHED_LIFETIME: i64 = 5000;

/// Credential `n`, expiring at `expires`: its access token is `c<n>`.
fn credential(n: u64, expires: i64) -> AuthCredential {
    AuthCredential::Oauth {
        access: format!("c{n}"),
        refresh: None,
        expires,
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
        .expect("a scripted credential is c<n>")
}

fn expiry(credential: &AuthCredential) -> i64 {
    match credential {
        AuthCredential::Oauth { expires, .. } => *expires,
        AuthCredential::ApiKey { .. } | AuthCredential::McpStaticToken { .. } => {
            panic!("a scripted credential is OAuth")
        }
    }
}

/// The scripted document: the stored credential `c<stored>` and its
/// expiry, the clock, the fetches made, and whether the next fetch
/// succeeds. The n-th fetch gives credential `c<n>`, fresh for
/// [`FETCHED_LIFETIME`], or failure `e<n>`. Whether a credential is fresh is the
/// core's judgment of the clock and the expiry.
struct Doc {
    stored: u64,
    expires: i64,
    now: i64,
    fetches: u64,
    fetch_ok: bool,
}

impl Doc {
    /// Credential 0, expired: it expires at the clock.
    fn new() -> Self {
        Doc {
            stored: 0,
            expires: 0,
            now: 0,
            fetches: 0,
            fetch_ok: true,
        }
    }

    fn read(&self) -> Read {
        Read {
            found: Stored::Credential(credential(self.stored, self.expires)),
            at: self.now,
        }
    }
}

impl RefreshIo for Doc {
    fn load(&mut self) -> Read {
        self.read()
    }

    fn check(&mut self) -> Read {
        self.read()
    }

    fn fetch(&mut self) -> Outcome {
        self.fetches += 1;
        if self.fetch_ok {
            Ok(credential(self.fetches, self.now + FETCHED_LIFETIME))
        } else {
            Err(format!("e{}", self.fetches))
        }
    }

    fn store(&mut self, fetched: AuthCredential, stands: &dyn Fn(&Read) -> bool) -> Outcome {
        if !stands(&self.read()) {
            self.stored = number(&fetched);
            self.expires = expiry(&fetched);
        }
        Ok(credential(self.stored, self.expires))
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

/// One document's flights stepped by hand: its book, its scripted
/// document, one leg per caller, and the transcript: after each event the
/// fetches, the stored credential (`+` while the core judges it fresh) and
/// every caller's leg.
struct Run {
    book: FlightBook,
    doc: Doc,
    legs: Vec<Leg>,
    transcript: String,
}

impl Run {
    fn new() -> Self {
        Run {
            book: FlightBook::new(),
            doc: Doc::new(),
            legs: Vec::new(),
            transcript: String::new(),
        }
    }

    fn print(&mut self) {
        let legs = self.legs.iter().map(show_leg).collect::<Vec<_>>().join(",");
        let stored = credential(self.doc.stored, self.doc.expires);
        let ahead = if fresh(&stored, self.doc.now) {
            '+'
        } else {
            '-'
        };
        let _ = writeln!(
            self.transcript,
            "f={} s=c{}{ahead} c={legs}",
            self.doc.fetches, self.doc.stored
        );
    }

    fn arrive(&mut self) {
        self.legs.push(Leg::Load);
        self.print();
    }

    /// Caller `caller` takes its next step, with the dispatch of
    /// [`RefreshFlights::refresh`]: a read, fetch or write on the
    /// document, else a step on the book (a waiting caller that is not
    /// served stays waiting); a fetch at it succeeds when `fetch` says so.
    fn step(&mut self, caller: usize, fetch: Fetch) {
        self.doc.fetch_ok = matches!(fetch, Fetch::Succeeds);
        let leg = std::mem::replace(&mut self.legs[caller], Leg::Load);
        self.legs[caller] = match leg {
            Leg::Load | Leg::Check(_) | Leg::Fetch(_) | Leg::Store(..) => {
                leg.advance(PROVIDER, &mut self.doc)
            }
            Leg::Board | Leg::Land(..) | Leg::Wait(_) | Leg::Done(_) => {
                self.book.advance(PROVIDER, leg)
            }
        };
        self.print();
    }

    /// Callers step in `order`, every fetch succeeding.
    fn steps(&mut self, order: &[usize]) {
        for &caller in order {
            self.step(caller, Fetch::Succeeds);
        }
    }

    /// A peer process stores a newer credential, fresh for [`LIFETIME`].
    fn peer(&mut self) {
        self.doc.stored += 1;
        self.doc.expires = self.doc.now + LIFETIME;
        self.print();
    }

    /// The clock reaches the stored credential's expiry.
    fn expire(&mut self) {
        self.doc.now = self.doc.expires;
        self.print();
    }
}

/// How a fetch at a step ends.
#[derive(Clone, Copy)]
enum Fetch {
    Succeeds,
    Fails,
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
    run.arrive();
    run.arrive();
    run.steps(&[0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1]);
    run.arrive();
    run.steps(&[2]);
    assert_eq!(
        run.transcript,
        "f=0 s=c0- c=L\n\
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
    assert!(
        run.book.landed.is_empty(),
        "the last joiner forgets the outcome"
    );
}

#[test]
fn a_failed_fetch_lands_with_its_joiners_and_the_next_caller_leads_a_new_flight() {
    let mut run = Run::new();
    run.arrive();
    run.arrive();
    run.steps(&[0, 0, 0, 1, 1]);
    run.step(0, Fetch::Fails);
    run.steps(&[0, 1, 1]);
    run.arrive();
    run.steps(&[2, 2, 2]);
    assert_eq!(
        run.transcript,
        "f=0 s=c0- c=L\n\
         f=0 s=c0- c=L,L\n\
         f=0 s=c0- c=B,L\n\
         f=0 s=c0- c=C0,L\n\
         f=0 s=c0- c=F0,L\n\
         f=0 s=c0- c=F0,B\n\
         f=0 s=c0- c=F0,W0\n\
         f=1 s=c0- c=N0:e1,W0\n\
         f=1 s=c0- c=D:e1,W0\n\
         f=1 s=c0- c=D:e1,D:e1\n\
         f=1 s=c0- c=D:e1,D:e1\n\
         f=1 s=c0- c=D:e1,D:e1,L\n\
         f=1 s=c0- c=D:e1,D:e1,B\n\
         f=1 s=c0- c=D:e1,D:e1,C1\n\
         f=1 s=c0- c=D:e1,D:e1,F1\n"
    );
}

#[test]
fn two_joiners_take_the_outcome_and_the_last_forgets_it() {
    let mut run = Run::new();
    run.arrive();
    run.arrive();
    run.arrive();
    run.steps(&[0, 0, 0, 1, 1, 2, 2, 1]);
    run.steps(&[0, 0, 1, 0]);
    assert_eq!(run.book.landed.len(), 1, "two joiners wait on flight 0");
    run.steps(&[1]);
    assert_eq!(run.book.landed.len(), 1, "one joiner still waits");
    run.steps(&[2]);
    assert!(run.book.landed.is_empty(), "the last joiner forgets it");
    assert_eq!(
        run.transcript.lines().last(),
        Some("f=1 s=c1+ c=D:c1,D:c1,D:c1")
    );
}

#[test]
fn a_peer_credential_stored_during_the_fetch_stands() {
    let mut run = Run::new();
    run.arrive();
    run.steps(&[0, 0, 0, 0]);
    run.peer();
    run.steps(&[0, 0]);
    assert_eq!(
        run.transcript,
        "f=0 s=c0- c=L\n\
         f=0 s=c0- c=B\n\
         f=0 s=c0- c=C0\n\
         f=0 s=c0- c=F0\n\
         f=1 s=c0- c=S0:c1\n\
         f=1 s=c1+ c=S0:c1\n\
         f=1 s=c1+ c=N0:c1\n\
         f=1 s=c1+ c=D:c1\n"
    );
    // The peer's credential is c1 too (the store's number plus one), but
    // it is the peer's write that stands and is served: its expiry, not
    // the fetch's.
    assert_eq!(run.doc.expires, LIFETIME);
    assert!(matches!(&run.legs[0], Leg::Done(Ok(served)) if expiry(served) == LIFETIME));
}

#[test]
fn a_peer_credential_that_expired_before_the_store_is_overwritten() {
    let mut run = Run::new();
    run.arrive();
    run.peer();
    run.expire();
    run.steps(&[0, 0, 0, 0]);
    run.peer();
    run.expire();
    run.steps(&[0, 0]);
    assert_eq!(
        run.transcript,
        "f=0 s=c0- c=L\n\
         f=0 s=c1+ c=L\n\
         f=0 s=c1- c=L\n\
         f=0 s=c1- c=B\n\
         f=0 s=c1- c=C0\n\
         f=0 s=c1- c=F0\n\
         f=1 s=c1- c=S0:c1\n\
         f=1 s=c2+ c=S0:c1\n\
         f=1 s=c2- c=S0:c1\n\
         f=1 s=c1+ c=N0:c1\n\
         f=1 s=c1+ c=D:c1\n"
    );
}

#[test]
fn the_leaders_check_lands_on_a_credential_a_flight_stored_after_its_load() {
    let mut run = Run::new();
    run.arrive();
    run.arrive();
    run.steps(&[1, 0, 0, 0, 0, 0, 0, 1, 1]);
    assert_eq!(run.doc.fetches, 1, "the second flight fetches nothing");
    assert_eq!(
        run.transcript.lines().last(),
        Some("f=1 s=c1+ c=D:c1,N1:c1")
    );
    run.steps(&[1]);
    assert_eq!(run.transcript.lines().last(), Some("f=1 s=c1+ c=D:c1,D:c1"));
}

/// A document that holds `found` for every read.
struct Fixed(fn() -> Stored);

impl RefreshIo for Fixed {
    fn load(&mut self) -> Read {
        Read {
            found: (self.0)(),
            at: 5,
        }
    }

    fn check(&mut self) -> Read {
        self.load()
    }

    fn fetch(&mut self) -> Outcome {
        panic!("a refused refresh fetches nothing")
    }

    fn store(&mut self, _: AuthCredential, _: &dyn Fn(&Read) -> bool) -> Outcome {
        panic!("a refused refresh stores nothing")
    }
}

#[test]
fn a_load_that_finds_no_oauth_credential_refuses_to_refresh() {
    let flights = RefreshFlights::default();
    let refused = [
        Fixed(|| Stored::Unreadable("could not read the auth file: gone".to_owned())),
        Fixed(|| Stored::Missing),
        Fixed(|| {
            Stored::Credential(AuthCredential::ApiKey {
                key: "k".to_owned(),
                prime_team: None,
            })
        }),
        Fixed(|| {
            Stored::Credential(AuthCredential::McpStaticToken {
                bearer: "b".to_owned(),
                endpoint: None,
            })
        }),
    ]
    .map(|mut io| flights.refresh(PROVIDER, &mut io));
    assert_eq!(
        refused,
        [
            Err("could not read the auth file: gone".to_owned()),
            Err(format!("no stored credential for {PROVIDER}")),
            Err(format!("the stored credential for {PROVIDER} is not OAuth")),
            Err(format!("the stored credential for {PROVIDER} is not OAuth")),
        ]
    );
    let served = flights.refresh(
        PROVIDER,
        &mut Fixed(|| Stored::Credential(credential(7, 6))),
    );
    assert_eq!(served, Ok(credential(7, 6)));
}

#[test]
fn a_credential_is_fresh_strictly_before_its_expiry_on_every_clock() {
    let oauth = |expires| credential(0, expires);
    let api_key = AuthCredential::ApiKey {
        key: "k".to_owned(),
        prime_team: None,
    };
    let judged = [
        fresh(&oauth(10), 9),
        fresh(&oauth(10), 10),
        fresh(&oauth(10), 11),
        fresh(&oauth(i64::MAX), 1_700_000_000_000),
        fresh(&oauth(i64::MIN), 0),
        fresh(&oauth(1), i64::MAX),
        fresh(&oauth(i64::MAX), i64::MAX),
        fresh(&api_key, 0),
    ];
    assert_eq!(
        judged,
        [true, false, false, true, false, false, false, false]
    );
}
