//! The bridge between the watch's verdict ([`Vigil::judge`]) and its Bend
//! model (`look` in `bend/child.bend`, whose laws `PROOF.bend` proves):
//! both run the same scenarios and must print the same transcript, byte for
//! byte. `bend/bridge_child.bend` documents the scenario format: polls that
//! read the child unsettled (with or without a token) or fail, each some ms
//! after the last; after each, the verdict and the clock.
//!
//! [`compare`] runs it (and skips without `bend`, unless
//! `EUKHE_REQUIRE_BEND` is set).

use std::fmt::Write as _;

use eukhe_durable::testing::bridge::{compare, Rng, Scenario};

use super::{Poll, Verdict, Vigil, CHILD_POLL_FAILURES};

/// One scenario: its events, for the model, and what the Rust verdict
/// printed. `failing` is the percentage of failed polls.
fn scenario(seed: u64, polls: usize, failing: u64) -> (String, String) {
    let mut rng = Rng(seed);
    let stall = rng.range(3, 80);
    let mut events = format!("9 {stall} {CHILD_POLL_FAILURES}\n");
    let mut transcript = String::new();
    let mut vigil = Vigil::default();
    for _ in 0..polls {
        let dt = rng.range(0, 9);
        let poll = if rng.range(1, 100) <= failing {
            writeln!(events, "1 {dt}").unwrap();
            Poll::Failed
        } else {
            let progress = match rng.range(0, 6) {
                0 => None,
                token => Some(token.min(3)),
            };
            let shown = progress.map_or_else(|| "-".to_owned(), |token| token.to_string());
            writeln!(events, "0 {dt} {shown}").unwrap();
            Poll::Unsettled { progress }
        };
        let elapsed = f64::from(u32::try_from(dt + 1).unwrap());
        let stall_ms = f64::from(u32::try_from(stall).unwrap());
        vigil = match vigil.judge(poll, elapsed, stall_ms) {
            Verdict::Watch(next) => {
                let token = next
                    .progress
                    .map_or_else(|| "-".to_owned(), |token| token.to_string());
                writeln!(
                    transcript,
                    "W q={} f={} t={token}",
                    next.quiet_ms, next.failures
                )
                .unwrap();
                next
            }
            Verdict::Stalled => {
                transcript.push_str("S\n");
                Vigil::default()
            }
            Verdict::Unreachable => {
                transcript.push_str("U\n");
                Vigil::default()
            }
        };
    }
    (events, transcript)
}

#[test]
fn the_rust_watch_equals_the_bend_model() {
    // Mostly answering children, then flaky ones, then mostly unreachable.
    let scenarios = (1..=40).map(|seed| {
        let failing = [10, 30, 70][usize::try_from(seed % 3).unwrap()];
        let (events, transcript) = scenario(seed, 300, failing);
        Scenario {
            name: seed.to_string(),
            events,
            transcript,
        }
    });
    compare("bend/bridge_child.bend", scenarios);
}
