//! The bridge between the run's decisions ([`super::decide`]) and their
//! Bend model (`bend/run.bend`, whose laws `PROOF.bend` proves): both run
//! the same scenarios and must print the same transcript, byte for byte.
//!
//! A scenario is a list of inputs (`bend/bridge_run.bend` documents the
//! format): model replies, finished rounds, compaction results, aborts. The
//! driver below calls, at each phase, the decision that phase calls in
//! production, and keeps the counters its checkpoints carry: a preparation
//! goes through [`before_request`], a resumed one through
//! [`after_compaction`], a reply through [`after_reply`], a finished round
//! through [`Rounds::finish`] and [`RoundEnd::reset`]. An abort ends every
//! phase: the generation's `abort` handler has no other outcome, and
//! `classify` yields to it. After each input both sides print the phase and
//! the counts left.
//!
//! [`compare`] runs it (and skips without `bend`, unless
//! `EUKHE_REQUIRE_BEND` is set).

use std::fmt::Write as _;
use std::num::NonZeroU32;

use super::decide::{
    after_compaction, after_reply, before_request, Compacted, Compaction, Counts, Failure, Limit,
    Limits, Prepared, Reply, RoundEnd, Rounds, Step, Threshold, LOOP_ROUNDS, MAX_POLLS,
};
use crate::testing::bridge::{compare, Rng, Scenario};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Phase {
    Prepare,
    Call,
    /// Waiting for a compaction; the preparation it resumes checks it.
    Compact(Compaction),
    Tools,
    Ended,
}

/// How a finished round ends, as `finish_tool_round` sees it.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Fin {
    /// No control ends the run and no reset is queued.
    Goes,
    /// A control ends the run: every call terminates, or one hands off.
    Stops,
    /// A queued reset applies at the post-tools boundary.
    Resets,
}

/// One input, as the model reads it: an abort, or what the world answers
/// in the run's phase. A phase reads its own part of a `Go`: preparation
/// and a call the reply (at preparation an overflow with a cut is a
/// context over the blocking threshold), a compaction `got`, a round
/// `hash` and `fin`.
#[derive(Clone, Copy)]
enum Input {
    Abort,
    Go {
        reply: Reply<()>,
        hash: u64,
        fin: Fin,
        got: Compacted,
    },
}

impl Input {
    fn reply(reply: Reply<()>) -> Self {
        Self::Go {
            reply,
            hash: 0,
            fin: Fin::Goes,
            got: Compacted::Entry,
        }
    }

    fn write(self, events: &mut String) {
        let Self::Go {
            reply,
            hash,
            fin,
            got,
        } = self
        else {
            events.push_str("a\n");
            return;
        };
        let (kind, flag) = match reply {
            Reply::Text => ('t', false),
            Reply::Calls => ('c', false),
            Reply::Deferred(()) => ('d', false),
            Reply::Error { retryable } => ('e', retryable),
            Reply::Overflow { cut } => ('o', cut),
        };
        let flag = u8::from(flag);
        let fin = match fin {
            Fin::Goes => 0,
            Fin::Stops => 1,
            Fin::Resets => 2,
        };
        let got = match got {
            Compacted::Entry => 0,
            Compacted::Nothing => 1,
            Compacted::Failed => 2,
        };
        let _ = writeln!(events, "g {kind} {flag} {hash} {fin} {got}");
    }
}

/// The run as the generation's phases drive the decisions.
struct Run {
    limits: Limits,
    phase: Phase,
    at: Counts,
    rounds: Rounds,
    out: String,
}

/// A generation's first request.
const FRESH: Counts = Counts {
    attempt: 1,
    polls: 0,
    compacted: false,
};

impl Run {
    fn end(&mut self, how: &str) {
        self.phase = Phase::Ended;
        self.out.push_str(how);
        self.out.push('\n');
    }

    fn input(&mut self, input: Input) {
        if self.phase == Phase::Ended {
            return;
        }
        let Input::Go {
            reply,
            hash,
            fin,
            got,
        } = input
        else {
            return self.end("aborted");
        };
        let at = self.at;
        match self.phase {
            Phase::Ended => return,
            // `prepare`: the context is over the blocking threshold, with a
            // cut, when the reply is an overflow with one.
            Phase::Prepare => {
                let over = (reply == Reply::Overflow { cut: true }).then_some(Threshold::Blocking);
                match before_request(at, || over) {
                    Prepared::Compact => {
                        self.phase = Phase::Compact(Compaction::Threshold);
                        self.at.compacted = true;
                    }
                    // `request` sends it, its reply counted as fetch 0.
                    Prepared::Request { .. } => {
                        self.phase = Phase::Call;
                        self.at.polls = 0;
                    }
                }
            }
            // `request` and `poll` end in `classify`.
            Phase::Call => match after_reply(at, reply, &self.limits) {
                Step::Answer => return self.end("answered"),
                Step::Tools => self.phase = Phase::Tools,
                Step::Poll((), polls) => self.at.polls = polls,
                // The `retry` phase prepares the next attempt.
                Step::Retry => {
                    self.phase = Phase::Prepare;
                    self.at.attempt = at.attempt + 1;
                }
                Step::Compact => {
                    self.phase = Phase::Compact(Compaction::Overflow);
                    self.at.compacted = true;
                }
                Step::Fail(Failure::Model) => return self.end("failed model"),
                Step::Fail(Failure::Polls) => return self.end("failed polls"),
            },
            // `prepare` resumed after the compaction.
            Phase::Compact(compaction) => match after_compaction(compaction, got) {
                Ok(()) => self.phase = Phase::Prepare,
                Err(Failure::Model) => return self.end("failed model"),
                Err(Failure::Polls) => return self.end("failed polls"),
            },
            // `finish_tool_round`.
            Phase::Tools => {
                let end = match fin {
                    Fin::Stops => RoundEnd::Stop,
                    Fin::Goes => self.rounds.finish(hash, &self.limits),
                    Fin::Resets => self.rounds.finish(hash, &self.limits).reset(),
                };
                match end {
                    RoundEnd::Stop | RoundEnd::Reset => return self.end("answered"),
                    RoundEnd::Fail(Limit::Loop) => return self.end("failed loop"),
                    RoundEnd::Fail(Limit::Rounds) => return self.end("failed rounds"),
                    RoundEnd::Next(next) => {
                        self.phase = Phase::Prepare;
                        self.rounds = next;
                        self.at = FRESH;
                    }
                }
            }
        }
        self.show();
    }

    /// The run with the counts left, as the model keeps them.
    fn show(&mut self) {
        let Counts {
            attempt,
            polls,
            compacted,
        } = self.at;
        let retries = u64::from(self.limits.max_retries) + 1 - attempt;
        let polls = self.limits.max_polls - polls;
        let compactions = u8::from(!compacted);
        let rounds = self.limits.max_rounds.get() - 1 - self.rounds.count;
        let same = self.rounds.same;
        let counts = format!("a={retries} c={compactions} r={rounds} s={same}");
        let _ = match self.phase {
            Phase::Prepare => writeln!(self.out, "prepare {counts}"),
            Phase::Call => writeln!(
                self.out,
                "call a={retries} p={polls} c={compactions} r={rounds} s={same}"
            ),
            Phase::Compact(Compaction::Overflow) => writeln!(self.out, "compact overflow {counts}"),
            Phase::Compact(Compaction::Threshold) => {
                writeln!(self.out, "compact threshold {counts}")
            }
            Phase::Tools => writeln!(self.out, "tools {counts}"),
            Phase::Ended => Ok(()),
        };
    }
}

/// An input the adversary may send in `phase`.
fn pick(rng: &mut Rng, phase: Phase, last_hash: &mut u64) -> Input {
    if rng.chance(3) {
        return Input::Abort;
    }
    match phase {
        Phase::Prepare => Input::reply(if rng.chance(20) {
            Reply::Overflow {
                cut: rng.chance(70),
            }
        } else {
            Reply::Text
        }),
        Phase::Call => Input::reply(match rng.below(100) {
            0..10 => Reply::Text,
            10..45 => Reply::Calls,
            45..65 => Reply::Deferred(()),
            65..85 => Reply::Error {
                retryable: rng.chance(70),
            },
            _ => Reply::Overflow {
                cut: rng.chance(60),
            },
        }),
        Phase::Compact(_) => Input::Go {
            reply: Reply::Text,
            hash: 0,
            fin: Fin::Goes,
            got: match rng.below(100) {
                0..70 => Compacted::Entry,
                70..85 => Compacted::Nothing,
                _ => Compacted::Failed,
            },
        },
        Phase::Tools | Phase::Ended => {
            if !rng.chance(60) {
                *last_hash = rng.below(3);
            }
            Input::Go {
                reply: Reply::Text,
                hash: *last_hash,
                fin: match rng.below(100) {
                    0..5 => Fin::Stops,
                    5..10 => Fin::Resets,
                    _ => Fin::Goes,
                },
                got: Compacted::Entry,
            }
        }
    }
}

/// One scenario: its limits, then inputs until the run ends.
fn scenario(rng: &mut Rng, limits: Limits, events: &mut String, transcript: &mut String) {
    let _ = writeln!(
        events,
        "9 {} {} {} {}",
        limits.max_rounds, limits.max_polls, limits.max_retries, limits.loop_rounds
    );
    let mut run = Run {
        limits,
        phase: Phase::Prepare,
        at: FRESH,
        rounds: Rounds::default(),
        out: String::new(),
    };
    let mut last_hash = 0;
    while run.phase != Phase::Ended {
        let input = pick(rng, run.phase, &mut last_hash);
        input.write(events);
        run.input(input);
    }
    transcript.push_str(&run.out);
}

fn limits(max_rounds: u32, max_polls: u32, max_retries: u32, loop_rounds: u32) -> Limits {
    Limits {
        max_rounds: NonZeroU32::new(max_rounds).unwrap_or(NonZeroU32::MIN),
        max_polls,
        max_retries,
        loop_rounds,
    }
}

#[test]
fn the_rust_decisions_equal_the_bend_model() {
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    let (mut events, mut transcript) = (String::new(), String::new());
    // The production limits, then small ones, so that every cap is reached.
    scenario(
        &mut rng,
        limits(250, MAX_POLLS, 3, LOOP_ROUNDS),
        &mut events,
        &mut transcript,
    );
    for _ in 0..400 {
        let small = limits(
            u32::try_from(rng.below(8)).unwrap_or(0) + 1,
            u32::try_from(rng.below(5)).unwrap_or(0),
            u32::try_from(rng.below(4)).unwrap_or(0),
            u32::try_from(rng.below(6)).unwrap_or(0),
        );
        scenario(&mut rng, small, &mut events, &mut transcript);
    }
    compare(
        "bend/bridge_run.bend",
        [Scenario {
            name: "every scenario".to_owned(),
            events,
            transcript,
        }],
    );
}
