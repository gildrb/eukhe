//! The bridge from the interface's Rust code to its Bend model
//! (`bend/screen.bend`, docs/interface.md S8): the transcript ledger
//! ([`Ledger`]), the pace ([`crate::pace::Pace`]), the verify decision
//! ([`crate::inline_term::present`] and [`crate::inline_term::resync`])
//! and the vertical stack ([`vstack`]) run generated scenarios, and
//! `bend/bridge_screen.bend` must print the same transcript, byte for
//! byte.
//!
//! A scenario file (no trailing newline) starts with the part it drives:
//!
//! - `t`, then one ledger event a line: `o` (open), `f X` (finish X), `l`
//!   (flush), `r W` (resize to W); the Rust ledger never grows a block. After each
//!   event: `W N|ID:S:LEN ...|ID:LEN ...|F G` -- the width, the number of
//!   blocks, the blocks (S is `a`, `f` or `c`), the scrollback (the
//!   committed prefix), whether the first block not committed is active
//!   (or none is), and whether no committed block follows one that is not.
//! - `p MIN K`, then `c N` (N characters arrive) or `n` (a frame). After
//!   each: `RECV SHOWN`.
//! - `v`, then `F G A B` lines: frames F (diff) and G (full redraw) with
//!   the two check results (1 pass, 0 fail). Each prints `d F 0`, `d G 1`
//!   or `e F`.
//! - `r`, then `F G H A B C` lines: as `v`, with the fresh redraw H and
//!   its check C. Each prints `d F 0`, `d G 1`, `f H` or `k F`.
//! - `s`, then `Y ROWS H1 H2 ...` lines: children of heights H from row Y
//!   in ROWS rows. Each prints `s` and ` Y:H` per placed child.

use std::fmt::Write as _;

use super::ledger::{Event, Ledger, Phase};
use super::stack::vstack;
use crate::inline_term::{present, resync, Check, Painting, Redraw, Shown};
use crate::pace::{Pace, PaceRate};
use crate::testing::{compare, Rng, Scenario};

const MODEL: &str = "bend/bridge_screen.bend";

/// `1` or `0`.
fn bit(value: bool) -> u8 {
    u8::from(value)
}

/// A block's length: the ledger never grows a block (the model's `len`
/// stays 0 on every block the Rust code opens).
fn ledger_line(ledger: &Ledger) -> String {
    let blocks = ledger.blocks();
    let committed = ledger.committed();
    let shown: Vec<String> = blocks
        .iter()
        .enumerate()
        .map(|(id, phase)| {
            let phase = match phase {
                Phase::Active => "a",
                Phase::Final => "f",
                Phase::Committed => "c",
            };
            format!("{id}:{phase}:0")
        })
        .collect();
    let scroll: Vec<String> = (0..committed).map(|id| format!("{id}:0")).collect();
    let flushed = blocks
        .get(committed)
        .is_none_or(|phase| *phase == Phase::Active);
    let gapless = blocks[committed..]
        .iter()
        .all(|phase| *phase != Phase::Committed);
    format!(
        "{} {}|{}|{}|{} {}\n",
        ledger.width(),
        blocks.len(),
        shown.join(" "),
        scroll.join(" "),
        bit(flushed),
        bit(gapless)
    )
}

/// A transcript scenario: opens and finishes of any block (some that do
/// not exist), flushes and resizes, in any order.
fn transcript(rng: &mut Rng, at: usize) -> Scenario {
    let mut ledger = Ledger::default();
    let mut events = vec!["t".to_string()];
    let mut transcript = String::new();
    for _ in 0..rng.range(1, 60) {
        let blocks = ledger.blocks().len() as u64;
        let (event, line) = match rng.below(100) {
            0..=34 => (Event::Open, "o".to_string()),
            35..=69 => {
                let id = rng.below(blocks + 2);
                (Event::Finish(id as usize), format!("f {id}"))
            }
            70..=89 => (Event::Flush, "l".to_string()),
            _ => {
                let width = rng.below(240);
                (Event::Resize(width as usize), format!("r {width}"))
            }
        };
        let _committed = ledger.apply(&[event]);
        events.push(line);
        transcript.push_str(&ledger_line(&ledger));
    }
    Scenario {
        name: format!("transcript-{at}"),
        events: events.join("\n"),
        transcript,
    }
}

/// A pacing scenario: chunks of any size (zero too) and frames, at any
/// minimum and share.
fn pacing(rng: &mut Rng, at: usize) -> Scenario {
    let rate = PaceRate {
        min: rng.below(5) as usize,
        lag: rng.below(6) as usize,
    };
    let mut pace = Pace::default();
    let mut events = vec![format!("p {} {}", rate.min, rate.lag)];
    let mut transcript = String::new();
    for _ in 0..rng.range(1, 80) {
        if rng.below(100) < 35 {
            let n = rng.below(120);
            pace.chunk(n as usize);
            events.push(format!("c {n}"));
        } else {
            pace.frame(rate);
            events.push("n".to_string());
        }
        let _ = writeln!(transcript, "{} {}", pace.recv(), pace.shown());
    }
    Scenario {
        name: format!("pacing-{at}"),
        events: events.join("\n"),
        transcript,
    }
}

/// The check results by their scenario digit: 0 fails, 1 passes.
const CHECKS: [Check; 2] = [Check::Fail, Check::Pass];

/// A verify scenario: every pair of check results, any frames.
fn verify(rng: &mut Rng, at: usize) -> Scenario {
    let mut events = vec!["v".to_string()];
    let mut transcript = String::new();
    for _ in 0..rng.range(1, 12) {
        let (first, full) = (rng.below(1000), rng.below(1000));
        let (ok1, ok2) = (rng.below(2) as usize, rng.below(2) as usize);
        events.push(format!("{first} {full} {ok1} {ok2}"));
        let line = match present(first, CHECKS[ok1], || (full, CHECKS[ok2])) {
            Shown::Drawn {
                frame,
                redraw: Redraw::Diff,
            } => format!("d {frame} 0"),
            Shown::Drawn {
                frame,
                redraw: Redraw::Full,
            } => format!("d {frame} 1"),
            Shown::Error { frame } => format!("e {frame}"),
        };
        transcript.push_str(&line);
        transcript.push('\n');
    }
    Scenario {
        name: format!("verify-{at}"),
        events: events.join("\n"),
        transcript,
    }
}

/// A scenario of the decision after `present`: every triple of check
/// results, any frames.
fn after_verify(rng: &mut Rng, at: usize) -> Scenario {
    let mut events = vec!["r".to_string()];
    let mut transcript = String::new();
    for _ in 0..rng.range(1, 16) {
        let (first, full, fresh) = (rng.below(1000), rng.below(1000), rng.below(1000));
        let (ok1, ok2, ok3) = (
            rng.below(2) as usize,
            rng.below(2) as usize,
            rng.below(2) as usize,
        );
        events.push(format!("{first} {full} {fresh} {ok1} {ok2} {ok3}"));
        let shown = present(first, CHECKS[ok1], || (full, CHECKS[ok2]));
        let line = match resync(shown, || (fresh, CHECKS[ok3])) {
            Painting::Shown {
                frame,
                redraw: Redraw::Diff,
            } => format!("d {frame} 0"),
            Painting::Shown {
                frame,
                redraw: Redraw::Full,
            } => format!("d {frame} 1"),
            Painting::Fresh { frame } => format!("f {frame}"),
            Painting::Kept { frame } => format!("k {frame}"),
        };
        transcript.push_str(&line);
        transcript.push('\n');
    }
    Scenario {
        name: format!("after-verify-{at}"),
        events: events.join("\n"),
        transcript,
    }
}

/// A layout scenario: any child heights (none too), any start row, any
/// viewport, so children fit, overflow, and start below the bottom.
fn layout(rng: &mut Rng, at: usize) -> Scenario {
    let mut events = vec!["s".to_string()];
    let mut transcript = String::new();
    for _ in 0..rng.range(1, 10) {
        let (y, rows) = (rng.below(12) as usize, rng.below(40) as usize);
        let heights: Vec<usize> = (0..rng.below(9)).map(|_| rng.below(12) as usize).collect();
        let mut line = format!("{y} {rows}");
        for height in &heights {
            let _ = write!(line, " {height}");
        }
        events.push(line);
        transcript.push('s');
        for rect in vstack(&heights, y, rows) {
            let _ = write!(transcript, " {}:{}", rect.y, rect.h);
        }
        transcript.push('\n');
    }
    Scenario {
        name: format!("layout-{at}"),
        events: events.join("\n"),
        transcript,
    }
}

/// The ledger, the pace, the verify decisions and the stack make the same
/// steps as the model on 750 generated scenarios: every event of each
/// part, on blocks that exist and that do not, chunks of zero, minimums
/// of zero, all four check pairs and all eight check triples, and
/// children that fit and that do not.
#[test]
fn the_rust_interface_equals_the_bend_model() {
    let mut rng = Rng(0x5c8e_e2a1_d00d_f00d);
    let mut scenarios = Vec::new();
    for at in 0..150 {
        scenarios.push(transcript(&mut rng, at));
        scenarios.push(pacing(&mut rng, at));
        scenarios.push(verify(&mut rng, at));
        scenarios.push(after_verify(&mut rng, at));
        scenarios.push(layout(&mut rng, at));
    }
    compare(MODEL, scenarios);
}
