//! The bridge between [`race`]'s interleaving and the wait model
//! (`bend/wait.bend` `run`, whose laws `PROOF.bend` proves): the race on
//! paused tokio time and the model run the same scenarios and must print
//! the same transcript, byte for byte (`bridge/bridge_wait.bend` documents
//! the format).
//!
//! Each poll's end is the compiled core's (`wait_poll_refines`); what this
//! checks is the rest, which is no decision: how an event (a oneshot), a
//! deadline of whole ticks and a cancel signal wake the race, and that a
//! race polled once after each signal of a scenario ends exactly when and
//! how the model's wait ends.

use std::fmt::Write as _;
use std::task::Poll;
use std::time::Duration;

use eukhe_chord::context::AbortController;
use eukhe_durable::testing::bridge::{compare, Rng, Scenario};
use tokio::sync::oneshot;

use super::{race, Exits, Raced};

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
    scenarios
}

#[test]
fn the_race_equals_the_wait_model() {
    compare("bridge/bridge_wait.bend", scenarios());
}
