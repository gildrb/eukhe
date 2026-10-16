//! The bridge between the Rust planner and its Bend model
//! (`bend/optchat.bend`, whose laws `PROOF.bend` proves): both run the
//! same scenarios and must print the same transcript, byte for byte.
//!
//! A scenario is a list of events (`bend/bridge.bend` documents the
//! format): messages, nodes built, calls started and failed, and queries
//! of the view and of a compaction's view. The Rust side drives a [`Chat`]
//! with them and prints, after each event, the view, the compaction view,
//! whether a batch is still shrinking, the batch it ran and the work
//! queue; the Bend side builds `bend/bridge.bend` into a native binary and
//! prints the same from the model, through [`compare`] (which skips without
//! `bend`, unless `EUKHE_REQUIRE_BEND` is set).

use std::fmt::Write as _;

use eukhe_durable::testing::bridge::{compare, Rng, Scenario};

use super::{Budgets, Chat};
use crate::memory::store::MessageMeta;
use crate::memory::view::Part;
use crate::memory::{Kind, PLACEHOLDER};

/// A node's text in the scenarios: a newline (the view shows it as a
/// space), then `size - 1` x's.
fn text(size: u64) -> String {
    let rest = usize::try_from(size.saturating_sub(1)).unwrap_or(0);
    format!("\n{}", "x".repeat(rest))
}

/// `l bits`: a node as a scenario names it, its index in binary, lowest
/// bit first, `-` for 0.
fn node_arg(part: Part) -> String {
    let mut bits = String::new();
    let mut i = part.i;
    while i > 0 {
        bits.push(if i & 1 == 1 { '1' } else { '0' });
        i >>= 1;
    }
    if bits.is_empty() {
        bits.push('-');
    }
    format!("{} {bits}", part.l)
}

fn parts(parts: &[Part]) -> String {
    parts
        .iter()
        .map(|part| format!("{}+{}", part.start(), part.count()))
        .collect::<Vec<_>>()
        .join(",")
}

fn meta() -> MessageMeta {
    MessageMeta {
        kind: Kind::User,
        size: 0,
        date: String::new(),
        file: 0,
        offset: 0,
        len: 0,
    }
}

/// One scenario as it runs on the Rust planner: its events, for the
/// model, and the transcript the planner printed.
struct Run {
    chat: Chat,
    events: String,
    transcript: String,
}

impl Run {
    fn new(budgets: Budgets) -> Run {
        Run {
            chat: Chat {
                budgets,
                ..Chat::default()
            },
            events: format!(
                "9 {} {} {} {} {} {}\n",
                PLACEHOLDER.len(),
                budgets.ceiling,
                budgets.floor,
                budgets.compaction_ceiling,
                budgets.compaction_floor,
                budgets.jobs
            ),
            transcript: String::new(),
        }
    }

    fn state(&mut self, batch: &[Part]) {
        let _ = writeln!(
            self.transcript,
            "v={} c={} s={} b={} q={}",
            parts(self.chat.view.parts()),
            parts(self.chat.compaction.parts()),
            u8::from(self.chat.shrinking),
            parts(batch),
            parts(&self.chat.candidates())
        );
    }

    fn message(&mut self) -> bool {
        self.events.push_str("0\n");
        let (_, batch) = self.chat.push_message(meta());
        let merged = batch.map(|batch| batch.merged).unwrap_or_default();
        self.state(&merged);
        !merged.is_empty()
    }

    fn build(&mut self, part: Part, size: u64) {
        let _ = writeln!(self.events, "1 {} {size}", node_arg(part));
        self.chat.insert_node(part, &text(size));
        self.state(&[]);
    }

    fn start(&mut self, part: Part) {
        let _ = writeln!(self.events, "2 {}", node_arg(part));
        self.chat.mark_busy(part);
        self.state(&[]);
    }

    fn fail(&mut self, part: Part) {
        let _ = writeln!(self.events, "3 {}", node_arg(part));
        self.chat.release(part);
        self.state(&[]);
    }

    fn context(&mut self, part: Part) {
        let _ = writeln!(self.events, "4 {}", node_arg(part));
        let _ = writeln!(self.transcript, "x={}", self.chat.context(part));
    }

    fn render(&mut self) {
        self.events.push_str("5\n");
        let _ = writeln!(self.transcript, "r={}", self.chat.render());
    }
}

/// Every message is summarized at once and every ready merge built: the
/// tree as an always-caught-up compactor grows it.
fn caught_up(seed: u64, messages: u64, budgets: Budgets) -> Run {
    let mut rng = Rng(seed);
    let mut run = Run::new(budgets);
    for _ in 0..messages {
        let batched = run.message();
        if batched {
            run.render();
        }
        while let Some(part) = run.chat.candidates().first().copied() {
            if rng.chance(10) {
                run.context(part);
            }
            let size = if part.l == 0 {
                rng.range(1, 600)
            } else {
                rng.range(200, 520)
            };
            run.build(part, size);
        }
    }
    run.render();
    run
}

/// A compactor that lags, fails and builds in any order: unbuilt parents
/// block merges, so batches stop short of the floor and go on later.
fn lagging(seed: u64, messages: u64, budgets: Budgets) -> Run {
    let mut rng = Rng(seed);
    let mut run = Run::new(budgets);
    let mut busy: Vec<Part> = Vec::new();
    let mut sent = 0;
    while sent < messages {
        let roll = rng.range(0, 99);
        if roll < 35 {
            sent += 1;
            if run.message() || rng.chance(2) {
                run.render();
            }
            continue;
        }
        let candidates = run.chat.candidates();
        if roll < 55 {
            if let Some(part) = rng.pick(&candidates) {
                run.start(part);
                busy.push(part);
            }
        } else if roll < 85 {
            let ready: Vec<Part> = candidates.iter().chain(&busy).copied().collect();
            if let Some(part) = rng.pick(&ready) {
                if rng.chance(15) {
                    run.context(part);
                }
                let size = if rng.chance(10) {
                    rng.range(1, 28)
                } else {
                    rng.range(30, 700)
                };
                run.build(part, size);
                busy.retain(|other| *other != part);
            }
        } else if let Some(part) = rng.pick(&busy) {
            run.fail(part);
            busy.retain(|other| *other != part);
        }
    }
    run.render();
    run
}

fn budgets(ceiling: usize, floor: usize, compaction: (usize, usize), jobs: usize) -> Budgets {
    Budgets {
        ceiling,
        floor,
        compaction_ceiling: compaction.0,
        compaction_floor: compaction.1,
        jobs,
    }
}

fn scenarios() -> Vec<(String, Run)> {
    let mut out = vec![
        (
            "caught up, the gist's sizes".to_string(),
            caught_up(1, 3000, Budgets::default()),
        ),
        (
            "caught up, small sizes".to_string(),
            caught_up(2, 4000, budgets(6000, 3000, (2000, 1000), 8)),
        ),
        (
            "lagging, the gist's sizes".to_string(),
            lagging(3, 1500, Budgets::default()),
        ),
        (
            "lagging, small sizes".to_string(),
            lagging(4, 2500, budgets(6000, 3000, (2000, 1000), 3)),
        ),
    ];
    let mut rng = Rng(5);
    for seed in 6..30 {
        let ceiling = usize::try_from(rng.range(300, 20_000)).unwrap_or(300);
        let floor = ceiling / usize::try_from(rng.range(2, 4)).unwrap_or(2);
        let compaction_ceiling = usize::try_from(rng.range(100, 8000)).unwrap_or(100);
        let compaction_floor = compaction_ceiling / 2;
        let jobs = usize::try_from(rng.range(1, 8)).unwrap_or(1);
        let messages = rng.range(50, 600);
        let sizes = budgets(ceiling, floor, (compaction_ceiling, compaction_floor), jobs);
        out.push((
            format!("random {seed}: {sizes:?}"),
            if seed % 2 == 0 {
                caught_up(seed, messages, sizes)
            } else {
                lagging(seed, messages, sizes)
            },
        ));
    }
    out
}

#[test]
fn the_rust_planner_equals_the_bend_model() {
    compare(
        "bend/bridge.bend",
        scenarios().into_iter().map(|(name, run)| Scenario {
            name,
            events: run.events,
            transcript: run.transcript,
        }),
    );
}
