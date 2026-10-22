//! The bridge between the Rust admission controller and its Bend model
//! (`bend/admission.bend`, whose laws `PROOF.bend` proves, rule H3 of
//! `docs/harness.md`): both run the same scenarios and must print the same
//! transcript, byte for byte.
//!
//! A scenario is a list of ops (`bend/bridge_admission.bend` documents the
//! format): new controllers, admits of either class, polls of waiters,
//! drops of permits and of waiters, and new limits. The Rust side drives an
//! [`AdmissionController`] with them and prints, after each op, its
//! outcome, the snapshot, both queues, the background slots held, the
//! granted waiters not collected yet, and the preempted permits; the Bend
//! side builds `bend/bridge_admission.bend` into a native binary and prints
//! the same from the model.
//!
//! [`compare`] runs it (and skips without `bend`, unless
//! `EUKHE_REQUIRE_BEND` is set).

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::future::Future;
use std::pin::Pin;
use std::sync::Arc;
use std::task::{Context, Poll, Waker};

use eukhe_durable::testing::bridge::{compare, Rng, Scenario};
use eukhe_types::daemon::AdmissionPriority;

use super::live::{Status, Ticket};
use super::{Admission, AdmissionController, AdmissionLimits, ProviderPermit, QueuedPermit};

/// What the scenario holds of one ticket.
enum Hand {
    Waiting(QueuedPermit),
    Holding(ProviderPermit),
    Gone,
}

fn limits(limit: u32, queue: u32) -> AdmissionLimits {
    AdmissionLimits::new(
        Some(&BTreeMap::from([("p".to_owned(), limit)])),
        Some(queue),
    )
}

fn join(tickets: impl Iterator<Item = u64>) -> String {
    tickets
        .map(|ticket| ticket.to_string())
        .collect::<Vec<_>>()
        .join(",")
}

/// One scenario file as it runs on the Rust controller: its ops, for the
/// model, and the transcript the controller printed.
struct Run {
    controller: Arc<AdmissionController>,
    hands: Vec<Hand>,
    events: String,
    transcript: String,
}

impl Run {
    fn new() -> Run {
        Run {
            controller: AdmissionController::new("p", &limits(0, 0)),
            hands: Vec::new(),
            events: String::new(),
            transcript: String::new(),
        }
    }

    fn state(&mut self, outcome: &str) {
        let snapshot = self.controller.snapshot();
        let state = self.controller.lock();
        let numbers = |pick: fn(&Ticket) -> bool| {
            state
                .live
                .tickets
                .iter()
                .filter(|ticket| pick(ticket))
                .map(|ticket| ticket.number)
                .collect::<Vec<u64>>()
        };
        let interactive_queue = numbers(|ticket| {
            ticket.class == AdmissionPriority::Interactive && ticket.status == Status::Queued
        });
        let background = numbers(|ticket| {
            ticket.class == AdmissionPriority::Background
                && matches!(ticket.status, Status::Granted | Status::Held)
        });
        let background_queue = numbers(|ticket| {
            ticket.class == AdmissionPriority::Background && ticket.status == Status::Queued
        });
        let granted = numbers(|ticket| ticket.status == Status::Granted);
        let preempted = self
            .hands
            .iter()
            .zip(0..)
            .filter_map(|(hand, ticket)| match hand {
                Hand::Holding(permit) => permit.preempted.is_cancelled().then_some(ticket),
                Hand::Waiting(_) | Hand::Gone => None,
            });
        let _ = writeln!(
            self.transcript,
            "{outcome} n={},{},{},{} iq={} b={} bq={} g={} x={}",
            snapshot.active,
            snapshot.waiting,
            snapshot.background_active,
            snapshot.background_waiting,
            join(interactive_queue.into_iter()),
            join(background.into_iter()),
            join(background_queue.into_iter()),
            join(granted.into_iter()),
            join(preempted),
        );
    }

    fn reset(&mut self, limit: u32, queue: u32) {
        let _ = writeln!(self.events, "9 {limit} {queue}");
        let _ = writeln!(self.transcript, "new {limit} {queue}");
        self.hands.clear();
        self.controller = AdmissionController::new("p", &limits(limit, queue));
    }

    fn admit(&mut self, priority: AdmissionPriority) {
        let class = match priority {
            AdmissionPriority::Interactive => 0,
            AdmissionPriority::Background => 1,
        };
        let _ = writeln!(self.events, "0 {class}");
        let (hand, outcome) = match self.controller.admit(priority) {
            Ok(Admission::Granted(permit)) => (Hand::Holding(permit), "g"),
            Ok(Admission::Queued(waiting)) => (Hand::Waiting(waiting), "q"),
            Err(_) => (Hand::Gone, "r"),
        };
        self.hands.push(hand);
        self.state(outcome);
    }

    fn collect(&mut self, ticket: usize) {
        let _ = writeln!(self.events, "1 {ticket}");
        let mut outcome = "0";
        if let Some(hand) = self.hands.get_mut(ticket) {
            if let Hand::Waiting(waiting) = hand {
                let mut cx = Context::from_waker(Waker::noop());
                if let Poll::Ready(permit) = Pin::new(waiting).poll(&mut cx) {
                    *hand = Hand::Holding(permit);
                    outcome = "1";
                }
            }
        }
        self.state(outcome);
    }

    /// Drop ticket `ticket`'s permit (op 2) or waiter (op 3).
    fn drop_hand(&mut self, op: u8, ticket: usize) {
        let _ = writeln!(self.events, "{op} {ticket}");
        if let Some(hand) = self.hands.get_mut(ticket) {
            *hand = Hand::Gone;
        }
        self.state("-");
    }

    fn set_limits(&mut self, limit: u32, queue: u32) {
        let _ = writeln!(self.events, "4 {limit} {queue}");
        self.controller.set_limits(&limits(limit, queue));
        self.state("-");
    }

    /// The tickets whose hand `is` picks.
    fn tickets(&self, is: fn(&Hand) -> bool) -> Vec<usize> {
        self.hands
            .iter()
            .enumerate()
            .filter(|(_, hand)| is(hand))
            .map(|(ticket, _)| ticket)
            .collect()
    }
}

fn waiting(hand: &Hand) -> bool {
    matches!(hand, Hand::Waiting(_))
}

fn holding(hand: &Hand) -> bool {
    matches!(hand, Hand::Holding(_))
}

/// A limit of 0 (unlimited) to 3, a queue limit of 0 to 3.
fn some_limits(rng: &mut Rng) -> (u32, u32) {
    let limit = u32::try_from(rng.below(4)).unwrap_or(0);
    let queue = u32::try_from(rng.below(4)).unwrap_or(0);
    (limit, queue)
}

/// One controller under random traffic: admits of either class, waiters
/// that poll late or give up, permits dropped in any order (preempted or
/// not), and limits raised and lowered while slots are held.
fn scenario(run: &mut Run, rng: &mut Rng, ops: u64) {
    let (limit, queue) = some_limits(rng);
    run.reset(limit, queue);
    for _ in 0..ops {
        let roll = rng.below(100);
        let target = match roll {
            30..=49 => rng.pick(&run.tickets(waiting)).map(|ticket| (1, ticket)),
            50..=69 => rng.pick(&run.tickets(holding)).map(|ticket| (2, ticket)),
            70..=84 => rng.pick(&run.tickets(waiting)).map(|ticket| (3, ticket)),
            _ => None,
        };
        match (roll, target) {
            (_, Some((1, ticket))) => run.collect(ticket),
            (_, Some((op, ticket))) => run.drop_hand(op, ticket),
            (85..=89, None) => {
                let (limit, queue) = some_limits(rng);
                run.set_limits(limit, queue);
            }
            (_, None) => run.admit(if rng.below(5) < 2 {
                AdmissionPriority::Interactive
            } else {
                AdmissionPriority::Background
            }),
        }
    }
}

/// Every scenario, in one file: each starts a new controller.
fn scenarios() -> Run {
    let mut run = Run::new();
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    for _ in 0..400 {
        let ops = 20 + rng.below(180);
        scenario(&mut run, &mut rng, ops);
    }
    run
}

#[test]
fn the_rust_controller_equals_the_bend_model() {
    let run = scenarios();
    compare(
        "bend/bridge_admission.bend",
        [Scenario {
            name: "every scenario".to_owned(),
            events: run.events,
            transcript: run.transcript,
        }],
    );
}
