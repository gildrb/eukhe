//! The bridge between the inference layer (docs/inference.md S6) and its
//! Bend model (`bend/infer.bend`, whose laws `PROOF.bend` proves): both
//! run the same scenarios and must print the same transcript, byte for
//! byte. (The quirks rulebook of section 1 runs as its compiled model,
//! `bend/ffi_quirks.bend`: no bridge.)
//!
//! - `bridge/bridge_infer.bend` documents the problems: the forced
//!   call ([`ForceEscalation`], model `force`), the repetition guard
//!   ([`RepetitionGuard`], model `guard`: chunk id `x` is the line `c<x>`,
//!   fed in deltas cut at random points; the chunks are random, a cycle of
//!   1 to 4 chunks, the same with one chunk changed, or the observed
//!   thinking loop of [`OBSERVED_CYCLE`]), and early compaction
//!   ([`threshold_for`], model `first_at`). For compaction the limit is
//!   the blocking threshold `L = window - reserve` and the margin `m` a
//!   whole number of tokens; the code compares strictly (`tokens > L - m`,
//!   `tokens > L`), so for whole token counts the model's thresholds are
//!   `T = L - m + 1` and `L + 1`.
//!
//! [`compare`] runs them (and skips without `bend`, unless
//! `EUKHE_REQUIRE_BEND` is set).

use std::fmt::Write as _;

use eukhe_ai::utils::stream_repeat::RepetitionGuard;

use super::decide::{threshold_for, Threshold};
use super::force::{ForceEscalation, ForceReply, ForceStep};
use crate::harness::types::{BackgroundMargin, CompactionPolicy, ThresholdTokens};
use crate::testing::bridge::{compare, Rng, Scenario};

// The forced call, the guard, early compaction
// ----------------------------------------------------------------

fn bit(flag: bool) -> u8 {
    u8::from(flag)
}

fn force_problem(rng: &mut Rng, events: &mut String, transcript: &mut String) {
    let retries = u32::try_from(rng.below(4)).unwrap();
    let (native, free) = (rng.chance(50), rng.chance(50));
    let replies: Vec<bool> = (0..=u64::from(retries) + rng.below(2))
        .map(|_| rng.chance(30))
        .collect();
    write!(events, "f {retries} {} {}", bit(native), bit(free)).unwrap();
    for called in &replies {
        write!(events, " {}", bit(*called)).unwrap();
    }
    events.push('\n');
    let escalation = ForceEscalation {
        retries,
        native,
        free,
    };
    transcript.push('f');
    let mut attempt = 1;
    loop {
        write!(transcript, " {}", bit(escalation.flag(attempt))).unwrap();
        let reply = if replies[usize::try_from(attempt - 1).unwrap()] {
            ForceReply::Called
        } else {
            ForceReply::Missed
        };
        match escalation.after(attempt, reply) {
            ForceStep::Called => break transcript.push_str(" called\n"),
            ForceStep::Retry => attempt += 1,
            ForceStep::Failed => break transcript.push_str(" missed\n"),
        }
    }
}

/// The observed thinking loop (docs/inference.md S6.5) as chunk ids: 14
/// lines, then this cycle of 7 lines, in which no line comes twice in a row.
const OBSERVED_CYCLE: [u64; 7] = [9, 11, 14, 10, 11, 15, 13];

fn guard_problem(rng: &mut Rng, events: &mut String, transcript: &mut String) {
    let (k, chunks): (u64, Vec<u64>) = match rng.below(4) {
        0 => (
            rng.below(10),
            (0..rng.below(16)).map(|_| rng.below(3)).collect(),
        ),
        kind @ (1 | 2) => {
            let block: Vec<u64> = (0..rng.range(1, 4)).map(|_| rng.below(3)).collect();
            let mut chunks: Vec<u64> = (0..rng.below(4)).map(|_| rng.below(3)).collect();
            let repeated = usize::try_from(rng.range(1, 24)).unwrap();
            chunks.extend(block.iter().copied().cycle().take(repeated));
            if kind == 2 {
                // A near miss: one chunk of the cycle changed.
                let at = usize::try_from(rng.below(u64::try_from(chunks.len()).unwrap())).unwrap();
                chunks[at] = 3;
            }
            (rng.range(2, 16), chunks)
        }
        _ => {
            let length = usize::try_from(rng.range(40, 98)).unwrap();
            let chunks = (0..14)
                .chain(OBSERVED_CYCLE.iter().copied().cycle())
                .take(length)
                .collect();
            (rng.pick(&[27, 28, 32, 64]).unwrap(), chunks)
        }
    };
    let k = u32::try_from(k).unwrap();
    write!(events, "g {k}").unwrap();
    for chunk in &chunks {
        write!(events, " {chunk}").unwrap();
    }
    events.push('\n');
    let mut text = String::new();
    for chunk in &chunks {
        writeln!(text, "c{chunk}").unwrap();
    }
    let mut guard = RepetitionGuard::new(k);
    let mut cut = None;
    let mut rest = text.as_str();
    while cut.is_none() && !rest.is_empty() {
        let mut at = usize::try_from(rng.range(1, 4)).unwrap().min(rest.len());
        while !rest.is_char_boundary(at) {
            at += 1;
        }
        let (delta, after) = rest.split_at(at);
        cut = guard.push(0, delta);
        rest = after;
    }
    match cut {
        Some(cut) => writeln!(transcript, "g cut {}", cut.chunks).unwrap(),
        None => transcript.push_str("g whole\n"),
    }
}

fn first_problem(rng: &mut Rng, events: &mut String, transcript: &mut String) {
    let window = 100 * rng.range(1, 20);
    let reserve = rng.range(0, window / 4);
    let percent = rng.below(30);
    let policy = CompactionPolicy {
        enabled: true,
        reserve_tokens: f64::from(u32::try_from(reserve).unwrap()),
        keep_recent_tokens: 0.0,
        background: BackgroundMargin::WindowPercent(f64::from(u32::try_from(percent).unwrap())),
        token_count: ThresholdTokens::Estimate,
    };
    let limit = window - reserve;
    let margin = window * percent / 100;
    let mut size = 0;
    let sizes: Vec<u64> = (0..rng.range(1, 10))
        .map(|_| {
            size += rng.below(window / 5 + 1);
            size
        })
        .collect();
    write!(events, "t {} {limit}", limit - margin + 1).unwrap();
    for size in &sizes {
        write!(events, " {size}").unwrap();
    }
    events.push('\n');
    let thresholds: Vec<Option<Threshold>> = sizes
        .iter()
        .map(|&size| threshold_for(f64::from(u32::try_from(size).unwrap()), window, &policy))
        .collect();
    let first = |wanted: fn(Option<Threshold>) -> bool| {
        thresholds
            .iter()
            .position(|threshold| wanted(*threshold))
            .map_or_else(|| "none".to_owned(), |at| at.to_string())
    };
    writeln!(
        transcript,
        "t {} {}",
        first(|threshold| threshold.is_some()),
        first(|threshold| threshold == Some(Threshold::Blocking))
    )
    .unwrap();
}

fn infer_scenarios() -> Vec<Scenario> {
    let mut rng = Rng(0x5e6_0002);
    (0..60)
        .map(|at| {
            let (mut events, mut transcript) = (String::new(), String::new());
            for _ in 0..10 {
                force_problem(&mut rng, &mut events, &mut transcript);
                guard_problem(&mut rng, &mut events, &mut transcript);
                first_problem(&mut rng, &mut events, &mut transcript);
            }
            Scenario {
                name: format!("problems {at}"),
                events,
                transcript,
            }
        })
        .collect()
}

#[test]
fn the_rust_inference_units_equal_the_bend_model() {
    compare("bridge/bridge_infer.bend", infer_scenarios());
}
