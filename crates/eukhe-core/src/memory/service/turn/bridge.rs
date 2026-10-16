//! The bridge between the harness's waits and their Bend models
//! (`bend/wait.bend`, `bend/lease.bend`, whose laws `PROOF.bend` proves):
//! the Rust code and the models run the same scenarios and must print the
//! same transcript, byte for byte (`bend/bridge_wait.bend` documents the
//! format).
//!
//! - The wait: [`race`] on paused tokio time, against an event (a oneshot),
//!   a deadline of whole ticks, and a cancel signal, polled once after
//!   each signal of the scenario.
//! - The lease: [`Turns`] taking asks, releases, stops (the waiter's reply
//!   receiver dropped) and crashes (its connection closed).

use std::collections::HashMap;
use std::fmt::Write as _;
use std::task::Poll;
use std::time::Duration;

use eukhe_chord::context::{race, AbortController, Exits, Raced};
use eukhe_durable::testing::bridge::{compare, Rng, Scenario};
use tokio::sync::oneshot;

use super::{Origin, Turns};
use crate::memory::service::Outcome;

/// One tick of the wait model.
const TICK: Duration = Duration::from_millis(10);

#[derive(Clone, Copy)]
enum Signal {
    Arrive,
    Tick,
    Cancel,
}

/// A wait with `deadline` ticks (`None`: none) that sees `signals`.
fn wait_scenario(
    runtime: &tokio::runtime::Runtime,
    name: String,
    deadline: Option<u64>,
    signals: &[Signal],
) -> Scenario {
    let mut events = match deadline {
        Some(ticks) => format!("w {ticks}"),
        None => "w -".to_owned(),
    };
    for signal in signals {
        events.push_str(match signal {
            Signal::Arrive => "\na",
            Signal::Tick => "\nt",
            Signal::Cancel => "\nc",
        });
    }
    let transcript = runtime.block_on(async {
        let (event, arrived) = oneshot::channel::<()>();
        let mut event = Some(event);
        let cancel = AbortController::new();
        let start = tokio::time::Instant::now();
        let exits = Exits {
            deadline: deadline.map(|ticks| start + TICK * u32::try_from(ticks).unwrap()),
            signal: Some(cancel.signal()),
        };
        let mut wait = Box::pin(race(arrived, exits));
        let mut ended = false;
        let mut transcript = String::new();
        for (at, signal) in std::iter::once(None)
            .chain(signals.iter().copied().map(Some))
            .enumerate()
        {
            match signal {
                None => {}
                Some(Signal::Arrive) => {
                    if let Some(event) = event.take() {
                        // After the end the receiver is gone: nothing to tell.
                        let _late = event.send(());
                    }
                }
                Some(Signal::Tick) => tokio::time::advance(TICK).await,
                Some(Signal::Cancel) => cancel.abort(None),
            }
            if ended {
                continue;
            }
            if let Poll::Ready(raced) = futures::poll!(wait.as_mut()) {
                ended = true;
                let end = match raced {
                    Raced::Done(Ok(())) => "arrived",
                    Raced::Done(Err(_)) => "dropped",
                    Raced::Expired => "expired",
                    Raced::Cancelled(_) => "cancelled",
                };
                writeln!(transcript, "{at} {end}").unwrap();
            }
        }
        transcript
    });
    Scenario {
        name,
        events,
        transcript,
    }
}

#[derive(Clone, Copy)]
enum LeaseEvent {
    Ask(u64),
    Release(u64),
    Stop(u64),
    Crash(u64),
}

fn lease_scenario(name: String, script: &[LeaseEvent]) -> Scenario {
    let mut turns = Turns::default();
    let mut origins: Vec<u64> = Vec::new();
    let mut replies: HashMap<u64, oneshot::Receiver<Outcome>> = HashMap::new();
    let mut events = "l".to_owned();
    let mut transcript = String::new();
    for event in script {
        match *event {
            LeaseEvent::Ask(origin) => {
                write!(events, "\na {origin}").unwrap();
                let key = u64::try_from(origins.len()).unwrap();
                let (reply, receiver) = oneshot::channel();
                origins.push(origin);
                replies.insert(key, receiver);
                turns.acquire(Origin::Connection(origin), key, reply);
            }
            LeaseEvent::Release(key) => {
                write!(events, "\nr {key}").unwrap();
                let origin = usize::try_from(key)
                    .ok()
                    .and_then(|at| origins.get(at).copied())
                    .unwrap_or(0);
                turns.release(Origin::Connection(origin), key);
            }
            LeaseEvent::Stop(key) => {
                write!(events, "\ns {key}").unwrap();
                replies.remove(&key);
            }
            LeaseEvent::Crash(origin) => {
                write!(events, "\nc {origin}").unwrap();
                turns.closed(origin);
            }
        }
        let holder = turns
            .holder
            .map_or_else(|| "-".to_owned(), |holder| holder.lease.to_string());
        let queue: Vec<String> = turns
            .waiting
            .iter()
            .map(|(key, reply)| {
                if reply.is_closed() {
                    format!("{}!", key.lease)
                } else {
                    key.lease.to_string()
                }
            })
            .collect();
        writeln!(transcript, "h={holder} q={}", queue.join(",")).unwrap();
    }
    Scenario {
        name,
        events,
        transcript,
    }
}

fn scenarios() -> Vec<Scenario> {
    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_time()
        .start_paused(true)
        .build()
        .unwrap();
    let mut scenarios = vec![
        wait_scenario(
            &runtime,
            "deadline 0".to_owned(),
            Some(0),
            &[Signal::Arrive],
        ),
        wait_scenario(
            &runtime,
            "the event before the deadline".to_owned(),
            Some(2),
            &[Signal::Tick, Signal::Arrive, Signal::Tick, Signal::Cancel],
        ),
        wait_scenario(
            &runtime,
            "no deadline, cancelled".to_owned(),
            None,
            &[Signal::Tick, Signal::Tick, Signal::Cancel, Signal::Arrive],
        ),
        wait_scenario(
            &runtime,
            "nothing comes".to_owned(),
            None,
            &[Signal::Tick, Signal::Tick, Signal::Tick],
        ),
    ];
    let mut rng = Rng(0x6b3a_9f1d_22c4_7e05);
    for at in 0..300 {
        let deadline = (!rng.chance(20)).then(|| rng.range(0, 6));
        let length = rng.range(0, 9);
        let signals: Vec<Signal> = (0..length)
            .map(|_| match rng.range(0, 99) {
                0..=14 => Signal::Arrive,
                15..=29 => Signal::Cancel,
                _ => Signal::Tick,
            })
            .collect();
        scenarios.push(wait_scenario(
            &runtime,
            format!("wait {at}"),
            deadline,
            &signals,
        ));
    }
    for at in 0..200 {
        let mut asked = 0;
        let script: Vec<LeaseEvent> = (0..30)
            .map(|_| match rng.range(0, 9) {
                0..=3 => {
                    asked += 1;
                    LeaseEvent::Ask(rng.range(0, 3))
                }
                4..=5 => LeaseEvent::Release(rng.range(0, asked + 1)),
                6..=7 => LeaseEvent::Stop(rng.range(0, asked + 1)),
                _ => LeaseEvent::Crash(rng.range(0, 3)),
            })
            .collect();
        scenarios.push(lease_scenario(format!("lease {at}"), &script));
    }
    scenarios
}

#[test]
fn the_waits_equal_their_bend_models() {
    compare("bend/bridge_wait.bend", scenarios());
}
