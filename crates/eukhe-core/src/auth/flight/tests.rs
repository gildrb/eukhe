//! The refresh flights through the compiled core: what a read means
//! (entry `auth_read`) and the document's desk (entry `auth_flight`, its
//! stepper), with the payloads the Rust keeps for each event. Each
//! transcript steps the callers by hand, in the order a scenario picks,
//! through the real dispatch of [`RefreshFlights::refresh`] (an order
//! done, then what it found reported to the desk as a second step), over a
//! scripted document whose clock and expiries the core judges.

use std::fmt::Write as _;
use std::sync::mpsc::{self, Receiver};
use std::sync::Arc;

use super::{fresh, Desk, Found, Next, Order, Outcome, Read, RefreshFlights, RefreshIo, Stored};
use crate::auth::refresh_error::{AuthFileError, OAuthRefreshError, RefreshError};
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
            // The flow's failure displays as its own text: `e<n>`.
            Err(RefreshError::Fetch(Arc::new(OAuthRefreshError::Flow(
                Arc::new(std::io::Error::other(format!("e{}", self.fetches))),
            ))))
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
        Err(cause) => cause.to_string(),
    }
}

/// Where one hand-stepped caller stands.
enum Hand {
    /// It waits on its mailbox for the desk's next order.
    Await,
    /// It holds an order to do.
    Order(Order),
    /// It did its order and holds what it found, to report.
    Found(Found),
    /// Its refresh is over.
    Over(Outcome),
}

fn show_hand(hand: &Hand) -> String {
    match hand {
        Hand::Await | Hand::Order(Order::Wait) => "W".to_owned(),
        Hand::Order(Order::Load) => "L".to_owned(),
        Hand::Order(Order::Check) => "C".to_owned(),
        Hand::Order(Order::Fetch) => "F".to_owned(),
        Hand::Order(Order::Store(credential)) => format!("S:{}", access(credential)),
        Hand::Order(Order::Done(outcome)) | Hand::Over(outcome) => {
            format!("D:{}", show_outcome(outcome))
        }
        Hand::Order(Order::Unlanded(text)) => format!("D:{text}"),
        Hand::Found(Found::LoadFresh(credential)) => format!("l+:{}", access(credential)),
        Hand::Found(Found::LoadExpired) => "l-".to_owned(),
        Hand::Found(Found::LoadFailed(cause)) => format!("l!:{cause}"),
        Hand::Found(Found::CheckFresh(credential)) => format!("c+:{}", access(credential)),
        Hand::Found(Found::CheckExpired) => "c-".to_owned(),
        Hand::Found(Found::FetchOk(credential)) => format!("f:{}", access(credential)),
        Hand::Found(Found::FetchFailed(cause)) => format!("f!:{cause}"),
        Hand::Found(Found::Stored(outcome)) => format!("s:{}", show_outcome(outcome)),
    }
}

/// One caller at the desk, stepped by hand: its number, its mailbox and
/// where it stands.
struct Hands {
    id: u64,
    mailbox: Receiver<Order>,
    hand: Hand,
}

impl Hands {
    /// A caller that waits on its mailbox takes the next order in it, if
    /// the desk sent one.
    fn pull(&mut self) {
        if matches!(self.hand, Hand::Await) {
            if let Ok(order) = self.mailbox.try_recv() {
                self.hand = Hand::Order(order);
            }
        }
    }

    /// The outcome this caller is served, once the desk sent it.
    fn served(&self) -> Option<&Outcome> {
        match &self.hand {
            Hand::Order(Order::Done(outcome)) | Hand::Over(outcome) => Some(outcome),
            Hand::Await | Hand::Order(_) | Hand::Found(_) => None,
        }
    }
}

/// One document's flights stepped by hand: its desk, its scripted
/// document, its callers in the order they arrived, and the transcript:
/// after each event the fetches, the stored credential (`+` while the core
/// judges it fresh) and where every caller stands: its order (`L` load,
/// `C` check, `F` fetch, `S:<c>` store, `W` wait, `D:<outcome>` done) or
/// what it found and has not yet reported (`l+:<c>` / `l-` / `l!:<why>`
/// at the load, `c+:<c>` / `c-` at the check, `f:<c>` / `f!:<why>` at the
/// fetch, `s:<outcome>` at the store).
struct Run {
    desk: Desk,
    doc: Doc,
    callers: Vec<Hands>,
    transcript: String,
}

impl Run {
    fn new() -> Self {
        Run {
            desk: eukhe_bend::expect_core(eukhe_bend::Entry::AuthFlight, Desk::open()),
            doc: Doc::new(),
            callers: Vec::new(),
            transcript: String::new(),
        }
    }

    fn print(&mut self) {
        let hands = self
            .callers
            .iter()
            .map(|caller| show_hand(&caller.hand))
            .collect::<Vec<_>>()
            .join(",");
        let stored = credential(self.doc.stored, self.doc.expires);
        let ahead = if fresh(&stored, self.doc.now) {
            '+'
        } else {
            '-'
        };
        let _ = writeln!(
            self.transcript,
            "f={} s=c{}{ahead} c={hands}",
            self.doc.fetches, self.doc.stored
        );
    }

    /// A caller arrives at the desk and takes its first order.
    fn arrive(&mut self) {
        let (sender, mailbox) = mpsc::channel();
        let id = eukhe_bend::expect_core(
            eukhe_bend::Entry::AuthFlight,
            self.desk.arrive(PROVIDER, sender),
        );
        let mut caller = Hands {
            id,
            mailbox,
            hand: Hand::Await,
        };
        caller.pull();
        self.callers.push(caller);
        self.print();
    }

    /// Caller `caller` takes its next step, with the dispatch of
    /// [`RefreshFlights::refresh`]: it does the order it holds (a read,
    /// judged by the core, a fetch or a write on the document; a wait
    /// leaves it waiting on its mailbox), or reports what it found to the
    /// desk; then, waiting on its mailbox, it takes the desk's next order
    /// if one came. A fetch at it succeeds when `fetch` says so.
    fn step(&mut self, caller: usize, fetch: Fetch) {
        self.doc.fetch_ok = matches!(fetch, Fetch::Succeeds);
        let hand = std::mem::replace(&mut self.callers[caller].hand, Hand::Await);
        self.callers[caller].hand = match hand {
            Hand::Order(order) => match order.take(PROVIDER, &mut self.doc) {
                Next::Report(found) => Hand::Found(found),
                Next::Wait => Hand::Await,
                Next::Over(outcome) => Hand::Over(outcome),
            },
            Hand::Found(found) => {
                let id = self.callers[caller].id;
                eukhe_bend::expect_core(eukhe_bend::Entry::AuthFlight, self.desk.found(id, found));
                Hand::Await
            }
            Hand::Await => Hand::Await,
            Hand::Over(outcome) => Hand::Over(outcome),
        };
        self.callers[caller].pull();
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

    /// The callers that wait for an outcome the desk has not handed them
    /// or they have not taken yet.
    fn waiting(&self) -> usize {
        self.callers
            .iter()
            .filter(|caller| matches!(caller.hand, Hand::Await | Hand::Order(Order::Wait)))
            .count()
    }

    /// The desk keeps nothing of a flight that landed: the provider has
    /// no flight in flight and no caller's mailbox is left at the desk.
    fn desk_forgot(&mut self) -> bool {
        let joiners =
            eukhe_bend::expect_core(eukhe_bend::Entry::AuthFlight, self.desk.joiners(PROVIDER));
        joiners.is_none() && self.desk.mailboxes.is_empty()
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
    // (reports it) after the fetch, before the flight ends. The flight
    // stays in flight until its credential is stored, so the second caller
    // joins it and never fetches; a third caller after the end loads the
    // stored credential.
    let mut run = Run::new();
    run.arrive();
    run.arrive();
    run.steps(&[0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1]);
    run.arrive();
    run.steps(&[2, 2]);
    assert_eq!(
        run.transcript,
        "f=0 s=c0- c=L\n\
         f=0 s=c0- c=L,L\n\
         f=0 s=c0- c=l-,L\n\
         f=0 s=c0- c=C,L\n\
         f=0 s=c0- c=c-,L\n\
         f=0 s=c0- c=F,L\n\
         f=1 s=c0- c=f:c1,L\n\
         f=1 s=c0- c=S:c1,L\n\
         f=1 s=c0- c=S:c1,l-\n\
         f=1 s=c1+ c=s:c1,l-\n\
         f=1 s=c1+ c=s:c1,W\n\
         f=1 s=c1+ c=s:c1,W\n\
         f=1 s=c1+ c=D:c1,W\n\
         f=1 s=c1+ c=D:c1,D:c1\n\
         f=1 s=c1+ c=D:c1,D:c1,L\n\
         f=1 s=c1+ c=D:c1,D:c1,l+:c1\n\
         f=1 s=c1+ c=D:c1,D:c1,D:c1\n"
    );
    assert!(run.desk_forgot(), "the last joiner forgets the outcome");
}

#[test]
fn a_failed_fetch_lands_with_its_joiners_and_the_next_caller_leads_a_new_flight() {
    let mut run = Run::new();
    run.arrive();
    run.arrive();
    run.steps(&[0, 0, 0, 0, 1, 1]);
    run.step(0, Fetch::Fails);
    run.steps(&[0, 1, 1]);
    run.arrive();
    run.steps(&[2, 2, 2, 2]);
    assert_eq!(
        run.transcript,
        "f=0 s=c0- c=L\n\
         f=0 s=c0- c=L,L\n\
         f=0 s=c0- c=l-,L\n\
         f=0 s=c0- c=C,L\n\
         f=0 s=c0- c=c-,L\n\
         f=0 s=c0- c=F,L\n\
         f=0 s=c0- c=F,l-\n\
         f=0 s=c0- c=F,W\n\
         f=1 s=c0- c=f!:e1,W\n\
         f=1 s=c0- c=D:e1,W\n\
         f=1 s=c0- c=D:e1,D:e1\n\
         f=1 s=c0- c=D:e1,D:e1\n\
         f=1 s=c0- c=D:e1,D:e1,L\n\
         f=1 s=c0- c=D:e1,D:e1,l-\n\
         f=1 s=c0- c=D:e1,D:e1,C\n\
         f=1 s=c0- c=D:e1,D:e1,c-\n\
         f=1 s=c0- c=D:e1,D:e1,F\n"
    );
}

#[test]
fn two_joiners_take_the_outcome_and_the_last_forgets_it() {
    let mut run = Run::new();
    run.arrive();
    run.arrive();
    run.arrive();
    run.steps(&[0, 0, 0, 0, 1, 1, 2, 2, 1]);
    run.steps(&[0, 0, 0, 1, 0]);
    assert_eq!(run.waiting(), 2, "two joiners wait on the flight");
    assert!(
        run.desk_forgot(),
        "the landed outcome is in the joiners' mailboxes, not at the desk"
    );
    run.steps(&[1]);
    assert_eq!(run.waiting(), 1, "one joiner still waits");
    run.steps(&[2]);
    assert_eq!(run.waiting(), 0, "the last joiner takes it");
    assert!(run.desk_forgot(), "the last joiner forgets it");
    assert_eq!(
        run.transcript.lines().last(),
        Some("f=1 s=c1+ c=D:c1,D:c1,D:c1")
    );
}

#[test]
fn a_peer_credential_stored_during_the_fetch_stands() {
    let mut run = Run::new();
    run.arrive();
    run.steps(&[0, 0, 0, 0, 0, 0]);
    run.peer();
    run.steps(&[0, 0]);
    assert_eq!(
        run.transcript,
        "f=0 s=c0- c=L\n\
         f=0 s=c0- c=l-\n\
         f=0 s=c0- c=C\n\
         f=0 s=c0- c=c-\n\
         f=0 s=c0- c=F\n\
         f=1 s=c0- c=f:c1\n\
         f=1 s=c0- c=S:c1\n\
         f=1 s=c1+ c=S:c1\n\
         f=1 s=c1+ c=s:c1\n\
         f=1 s=c1+ c=D:c1\n"
    );
    // The peer's credential is c1 too (the store's number plus one), but
    // it is the peer's write that stands and is served: its expiry, not
    // the fetch's.
    assert_eq!(run.doc.expires, LIFETIME);
    assert!(matches!(run.callers[0].served(), Some(Ok(served)) if expiry(served) == LIFETIME));
}

#[test]
fn a_peer_credential_that_expired_before_the_store_is_overwritten() {
    let mut run = Run::new();
    run.arrive();
    run.peer();
    run.expire();
    run.steps(&[0, 0, 0, 0, 0, 0]);
    run.peer();
    run.expire();
    run.steps(&[0, 0]);
    assert_eq!(
        run.transcript,
        "f=0 s=c0- c=L\n\
         f=0 s=c1+ c=L\n\
         f=0 s=c1- c=L\n\
         f=0 s=c1- c=l-\n\
         f=0 s=c1- c=C\n\
         f=0 s=c1- c=c-\n\
         f=0 s=c1- c=F\n\
         f=1 s=c1- c=f:c1\n\
         f=1 s=c1- c=S:c1\n\
         f=1 s=c2+ c=S:c1\n\
         f=1 s=c2- c=S:c1\n\
         f=1 s=c1+ c=s:c1\n\
         f=1 s=c1+ c=D:c1\n"
    );
}

#[test]
fn the_leaders_check_lands_on_a_credential_a_flight_stored_after_its_load() {
    let mut run = Run::new();
    run.arrive();
    run.arrive();
    run.steps(&[1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]);
    assert_eq!(run.doc.fetches, 1, "the second flight fetches nothing");
    assert_eq!(
        run.transcript.lines().last(),
        Some("f=1 s=c1+ c=D:c1,c+:c1")
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
        Fixed(|| Stored::Unreadable(AuthFileError::Read(Arc::new(anyhow::anyhow!("gone"))))),
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
    .map(|mut io| {
        flights
            .refresh(PROVIDER, &mut io)
            .map_err(|error| error.to_string())
    });
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
    assert_eq!(
        served.map_err(|error| error.to_string()),
        Ok(credential(7, 6))
    );
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
