//! The bridge between the Director stack ([`decide`], [`Loop::tick`], the
//! persisted [`DirectorState`]) and its Bend model (`bend/director.bend`,
//! whose laws `PROOF.bend` proves): both run the same scenarios and must
//! print the same transcript, byte for byte.
//!
//! A scenario (`bend/bridge_director.bend` documents the format) sets a
//! stack cap, then starts loops: a global budget and a stack. Each loop
//! takes ticks and lone decisions on verdict lists, and after each one the
//! driver prints the outcome and the stack. A run line replays every tick
//! of the loop from its start (the model's `run`). An encode line writes
//! the loop's stack as the persisted `eukhe.directors` value, reads it
//! back, and prints it as the model's tree nodes (each layer a kind node
//! under the kind node of the layer below, and its budget node under it)
//! and the stack those nodes decode to.
//!
//! [`compare`] runs it (and skips without `bend`, unless
//! `EUKHE_REQUIRE_BEND` is set).

use std::collections::BTreeSet;
use std::fmt::Write as _;

use eukhe_chord::json::{from_json, to_json};
use eukhe_durable::testing::bridge::{compare, Rng, Scenario};

use super::{decide, DirectorState, End, Layer, LayerKind, Loop, Outcome, RunLoop, Verdict};

/// A case the scenarios must reach, so that the bridge checks every rule
/// of the model.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Case {
    /// A push with room.
    Push,
    /// A push that fits the layers below but not the whole stack.
    PushCountsAbove,
    /// A push with no room.
    PushFull,
    /// Again or a push with no budget.
    Broke,
    /// A layer leaves and the next one decides.
    Leave,
    /// Every layer defers.
    AllDefer,
    /// A continue with no global step left.
    OutOfSteps,
    /// A tick of an ended loop.
    AfterEnd,
    /// A layer that leads leaves with the continuation.
    LeadGoes,
    /// A layer that leads stays when the loop ends.
    LeadStays,
}

/// The cases the scenarios reached.
type Reached = BTreeSet<Case>;

/// The layer of kind number `code` (as the model's encoding numbers kinds).
fn layer(code: u64, budget: u64) -> Layer {
    let kinds = [
        LayerKind::Goal,
        LayerKind::Autonomous,
        LayerKind::Reminder {
            text: "remember".to_owned(),
        },
        LayerKind::ForceTool {
            tool: "lookup".to_owned(),
            tries: 1,
            called: false,
            missed: 0,
        },
    ];
    let kind = kinds[usize::try_from(code).unwrap_or(0) % kinds.len()].clone();
    assert_eq!(kind.code(), code, "the kind numbers count from 0");
    Layer { kind, budget }
}

/// A stack, top first, as the transcript prints it.
fn show_stack(stack: &[Layer]) -> String {
    stack.iter().rev().fold(String::new(), |mut text, layer| {
        let _ = write!(text, " {}:{}", layer.kind.code(), layer.budget);
        text
    })
}

fn show_outcome(outcome: Outcome) -> &'static str {
    match outcome {
        Outcome::Continue => "cont",
        Outcome::Hand => "hand",
        Outcome::Failed => "fail",
    }
}

fn show_loop(head: &str, run: &Loop) -> String {
    let end = match run.end {
        None => "run",
        Some(End::Hand) => "hand",
        Some(End::Failed) => "fail",
    };
    format!("{head} {end} {} |{}\n", run.left, show_stack(&run.stack))
}

/// The model's tree nodes `(key, parent, value)` of a stack (bottom first),
/// in key order: layer `i` from the bottom is its kind node `2i + 1`, under
/// the kind node of the layer below (the root for the bottom layer), and
/// its budget node `2i + 2` under it.
fn encode(stack: &[Layer]) -> Vec<(u64, u64, u64)> {
    let mut nodes = Vec::with_capacity(stack.len() * 2);
    for (index, layer) in (0u64..).zip(stack) {
        let key = 2 * index + 1;
        let parent = index.checked_sub(1).map_or(0, |below| 2 * below + 1);
        nodes.push((key, parent, layer.kind.code()));
        nodes.push((key + 1, key, layer.budget));
    }
    nodes
}

/// The layers `(kind, budget)`, bottom first, of nodes in key order, two
/// nodes a layer.
fn decode(nodes: &[(u64, u64, u64)]) -> Vec<(u64, u64)> {
    nodes
        .as_chunks::<2>()
        .0
        .iter()
        .map(|[kind, budget]| (kind.2, budget.2))
        .collect()
}

/// One scenario as it runs.
struct Run {
    cap: usize,
    start: Loop,
    now: Loop,
    ticks: Vec<Vec<Verdict>>,
    events: String,
    transcript: String,
}

impl Run {
    /// Up to `len + 1` random verdicts.
    fn verdicts(rng: &mut Rng, len: usize) -> Vec<Verdict> {
        let count = rng.below(len as u64 + 2);
        (0..count)
            .map(|_| match rng.below(14) {
                0..=2 => Verdict::Defer,
                3..=5 => Verdict::Again,
                6 => Verdict::Yield,
                7..=8 => Verdict::Stack(layer(rng.below(4), rng.below(3))),
                9..=10 => Verdict::Leave,
                11 => Verdict::Abort,
                12.. => Verdict::Lead,
            })
            .collect()
    }

    fn write_verdicts(&mut self, head: char, verdicts: &[Verdict]) {
        self.events.push(head);
        for verdict in verdicts {
            match verdict {
                Verdict::Defer => self.events.push_str(" d"),
                Verdict::Again => self.events.push_str(" a"),
                Verdict::Yield => self.events.push_str(" y"),
                Verdict::Stack(pushed) => {
                    let _ = write!(self.events, " p:{}:{}", pushed.kind.code(), pushed.budget);
                }
                Verdict::Leave => self.events.push_str(" v"),
                Verdict::Abort => self.events.push_str(" x"),
                Verdict::Lead => self.events.push_str(" r"),
            }
        }
        self.events.push('\n');
    }

    /// Note the rules `verdicts` reach on `stack`.
    fn note(&self, stack: &[Layer], verdicts: &[Verdict], reached: &mut Reached) {
        for (above, top) in stack.iter().rev().enumerate() {
            let below = stack.len() - 1 - above;
            match verdicts.get(above).unwrap_or(&Verdict::Defer) {
                Verdict::Defer => {
                    if above + 1 == stack.len() {
                        reached.insert(Case::AllDefer);
                    }
                    continue;
                }
                Verdict::Leave => {
                    if above + 1 < stack.len() {
                        reached.insert(Case::Leave);
                    }
                    continue;
                }
                Verdict::Lead => continue,
                Verdict::Again | Verdict::Stack(_) if top.budget == 0 => {
                    reached.insert(Case::Broke);
                }
                Verdict::Stack(_) if above + 1 + below < self.cap => {
                    reached.insert(Case::Push);
                }
                Verdict::Stack(_) if 1 + below < self.cap => {
                    reached.insert(Case::PushCountsAbove);
                }
                Verdict::Stack(_) => {
                    reached.insert(Case::PushFull);
                }
                Verdict::Again | Verdict::Yield | Verdict::Abort => {}
            }
            return;
        }
    }

    fn cap(&mut self, rng: &mut Rng) {
        self.cap = usize::try_from(rng.range(1, 5)).unwrap_or(1);
        let _ = writeln!(self.events, "c {}", self.cap);
    }

    fn start(&mut self, rng: &mut Rng) {
        let left = rng.below(4);
        let stack: Vec<Layer> = (0..rng.below(self.cap as u64 + 1))
            .map(|_| layer(rng.below(4), rng.below(3)))
            .collect();
        let _ = writeln!(self.events, "l {left}{}", show_stack(&stack));
        self.start = Loop {
            left,
            stack,
            end: None,
        };
        self.now = self.start.clone();
        self.ticks.clear();
    }

    fn tick(&mut self, rng: &mut Rng, reached: &mut Reached) {
        let verdicts = Self::verdicts(rng, self.now.stack.len());
        self.write_verdicts('t', &verdicts);
        if self.now.end.is_some() {
            reached.insert(Case::AfterEnd);
        } else {
            self.note(&self.now.stack, &verdicts, reached);
            if self.now.left == 0
                && decide(&self.now.stack, &verdicts, self.cap).outcome == Outcome::Continue
            {
                reached.insert(Case::OutOfSteps);
            }
        }
        // A Lead counts when no layer above it decided.
        let leads = self.now.end.is_none()
            && verdicts
                .iter()
                .take(self.now.stack.len())
                .take_while(|verdict| {
                    matches!(verdict, Verdict::Defer | Verdict::Leave | Verdict::Lead)
                })
                .any(|verdict| *verdict == Verdict::Lead);
        self.now = self.now.clone().tick(&verdicts, self.cap);
        if leads {
            reached.insert(if self.now.end.is_some() {
                Case::LeadStays
            } else {
                Case::LeadGoes
            });
        }
        self.transcript.push_str(&show_loop("t", &self.now));
        self.ticks.push(verdicts);
    }

    fn decide(&mut self, rng: &mut Rng, reached: &mut Reached) {
        let verdicts = Self::verdicts(rng, self.now.stack.len());
        self.write_verdicts('d', &verdicts);
        self.note(&self.now.stack, &verdicts, reached);
        let decision = decide(&self.now.stack, &verdicts, self.cap);
        let _ = writeln!(
            self.transcript,
            "d {} |{}",
            show_outcome(decision.outcome),
            show_stack(&decision.stack)
        );
    }

    /// The loop from its start on every tick since (the model's `run`).
    fn replay(&mut self) {
        self.events.push_str("r\n");
        let run = self.ticks.iter().fold(self.start.clone(), |run, verdicts| {
            run.tick(verdicts, self.cap)
        });
        self.transcript.push_str(&show_loop("r", &run));
    }

    /// The loop's stack through its persisted form, then the tree.
    fn encode(&mut self) {
        self.events.push_str("e\n");
        let state = DirectorState {
            stack: self.now.stack.clone(),
            run: Some(RunLoop {
                input: None,
                left: self.now.left,
                end: self.now.end,
            }),
        };
        let read: DirectorState = from_json(&to_json(&state).unwrap()).unwrap();
        assert_eq!(read, state, "the persisted stack reads back exactly");
        let nodes = encode(&read.stack);
        self.transcript.push('e');
        for (key, parent, value) in &nodes {
            let _ = write!(self.transcript, " {key}:{parent}:{value}");
        }
        self.transcript.push_str("\nb");
        for (kind, budget) in decode(&nodes).iter().rev() {
            let _ = write!(self.transcript, " {kind}:{budget}");
        }
        self.transcript.push('\n');
    }
}

/// One scenario: a cap, then 2 to 5 loops of up to 8 ticks and decisions.
fn scenario(rng: &mut Rng, reached: &mut Reached) -> (String, String) {
    let empty = Loop {
        left: 0,
        stack: Vec::new(),
        end: None,
    };
    let mut run = Run {
        cap: 0,
        start: empty.clone(),
        now: empty,
        ticks: Vec::new(),
        events: String::new(),
        transcript: String::new(),
    };
    run.cap(rng);
    for _ in 0..rng.range(2, 5) {
        run.start(rng);
        for _ in 0..rng.range(1, 8) {
            match rng.below(10) {
                0..=5 => run.tick(rng, reached),
                6..=7 => run.decide(rng, reached),
                8.. => run.encode(),
            }
        }
        run.replay();
        run.encode();
    }
    (run.events, run.transcript)
}

#[test]
fn the_rust_director_stack_equals_the_bend_model() {
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    let mut reached = Reached::new();
    let scenarios: Vec<Scenario> = (0..300)
        .map(|at| {
            let (events, transcript) = scenario(&mut rng, &mut reached);
            Scenario {
                name: format!("director {at}"),
                events,
                transcript,
            }
        })
        .collect();
    compare("bend/bridge_director.bend", scenarios);
    // The scenarios reach every rule of the model.
    assert_eq!(
        reached,
        Reached::from([
            Case::Push,
            Case::PushCountsAbove,
            Case::PushFull,
            Case::Broke,
            Case::Leave,
            Case::AllDefer,
            Case::OutOfSteps,
            Case::AfterEnd,
            Case::LeadGoes,
            Case::LeadStays,
        ])
    );
}
