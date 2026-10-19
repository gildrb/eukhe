//! The bridge between the run's decisions ([`super::decide`]) and their
//! Bend model (`bend/run.bend`, whose laws `PROOF.bend` proves): both run
//! the same scenarios and must print the same transcript, byte for byte.
//!
//! A scenario is a list of inputs (`bend/bridge_run.bend` documents the
//! format): model replies, messages that end the model's turn (which
//! [`Ended::reply`] reads, as `classify` does), finished rounds, compaction
//! results, aborts. The driver below calls, at each phase, the decision
//! that phase calls in production, and keeps the counters its checkpoints
//! carry: a preparation goes through [`before_request`], a resumed one
//! through [`after_compaction`], a reply through [`after_reply`] and a
//! retry's note through [`retry_note`], a finished round through
//! [`Rounds::finish`] and [`RoundEnd::reset`]. An abort ends every phase:
//! the generation's `abort` handler has no other outcome, and `classify`
//! yields to it. After each input both sides print the request it sent or
//! cut, as the model's requests (`R.Reqs`) name it: the version of the
//! logged context (one more for each compaction entry and each round that
//! goes on) and the attempt its note names, 0 for none. Then they print
//! the phase and the counts left.
//!
//! [`compare`] runs it (and skips without `bend`, unless
//! `EUKHE_REQUIRE_BEND` is set).

use std::fmt::Write as _;
use std::num::NonZeroU32;

use super::decide::{
    after_compaction, after_reply, before_request, retry_note, Compacted, Compaction, Counts,
    Ended, Failure, Limit, Limits, Prepared, Reply, RoundEnd, Rounds, Step, Threshold, LOOP_ROUNDS,
    MAX_POLLS,
};
use super::note::{NoteCause, RetryNote};
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

/// What the model answers: a reply as `classify` decides it, or a message
/// that ends the model's turn, which [`Ended::reply`] reads.
#[derive(Clone, Copy)]
enum Answer {
    Reply(Reply<()>),
    Ended(Ended),
}

/// One input, as the model reads it: an abort, or what the world answers
/// in the run's phase. A phase reads its own part of a `Go`: preparation
/// and a call the answer (at preparation an overflow with a cut is a
/// context over the blocking threshold), a compaction `got`, a round
/// `hash` and `fin`.
#[derive(Clone, Copy)]
enum Input {
    Abort,
    Go {
        answer: Answer,
        hash: u64,
        fin: Fin,
        got: Compacted,
    },
}

impl Input {
    fn answer(answer: Answer) -> Self {
        Self::Go {
            answer,
            hash: 0,
            fin: Fin::Goes,
            got: Compacted::Entry,
        }
    }

    fn write(self, events: &mut String) {
        let Self::Go {
            answer,
            hash,
            fin,
            got,
        } = self
        else {
            events.push_str("a\n");
            return;
        };
        let (kind, flag, held) = match answer {
            Answer::Reply(Reply::Text) => ('t', false, String::new()),
            Answer::Reply(Reply::Calls) => ('c', false, String::new()),
            Answer::Reply(Reply::Deferred(())) => ('d', false, String::new()),
            Answer::Reply(Reply::Error { retryable, noted }) => {
                ('e', retryable, format!(" {}", u8::from(noted)))
            }
            Answer::Reply(Reply::Overflow { cut }) => ('o', cut, String::new()),
            Answer::Ended(Ended {
                tool_use,
                text,
                calls,
                retrying,
            }) => (
                'm',
                retrying,
                format!(
                    " {} {} {}",
                    u8::from(tool_use),
                    u8::from(text),
                    u8::from(calls)
                ),
            ),
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
        let _ = writeln!(events, "g {kind} {flag} {hash} {fin} {got}{held}");
    }
}

/// The run as the generation's phases drive the decisions.
struct Run {
    limits: Limits,
    phase: Phase,
    at: Counts,
    rounds: Rounds,
    /// The version of the logged context the next request sends.
    ctx: u64,
    /// The note the next request ends with.
    note: Option<RetryNote>,
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

    /// The request the run sends next: `sent` or `cut`, its context and
    /// the attempt its note names.
    fn request(&mut self, what: &str) {
        let note = self.note.as_ref().map_or(0, |note| note.attempt);
        let _ = writeln!(self.out, "{what} {}.{note}", self.ctx);
    }

    fn input(&mut self, input: Input) {
        if self.phase == Phase::Ended {
            return;
        }
        let Input::Go {
            answer,
            hash,
            fin,
            got,
        } = input
        else {
            return self.end("aborted");
        };
        // `classify`: a message that ends the model's turn makes its reply.
        let reply = match answer {
            Answer::Reply(reply) => reply,
            Answer::Ended(ended) => ended.reply(),
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
                        self.request("sent");
                    }
                }
            }
            // `request` and `poll` end in `classify`: a noted reply cuts the
            // request; the bridge's noted replies are no answers.
            Phase::Call => {
                let cause = match reply {
                    Reply::Error { noted: true, .. } => {
                        self.request("cut");
                        Some(NoteCause::NoAnswer)
                    }
                    Reply::Text
                    | Reply::Calls
                    | Reply::Deferred(())
                    | Reply::Error { noted: false, .. }
                    | Reply::Overflow { .. } => None,
                };
                match after_reply(at, reply, &self.limits) {
                    Step::Answer => return self.end("answered"),
                    Step::Tools => self.phase = Phase::Tools,
                    Step::Poll((), polls) => self.at.polls = polls,
                    // The `retry` phase prepares the next attempt.
                    Step::Retry => {
                        self.phase = Phase::Prepare;
                        self.at.attempt = at.attempt + 1;
                        self.note = retry_note(at, cause, self.note.take());
                    }
                    Step::Compact => {
                        self.phase = Phase::Compact(Compaction::Overflow);
                        self.at.compacted = true;
                    }
                    Step::Fail(Failure::Model) => return self.end("failed model"),
                    Step::Fail(Failure::Polls) => return self.end("failed polls"),
                }
            }
            // `prepare` resumed after the compaction; its entry grows the
            // context.
            Phase::Compact(compaction) => match after_compaction(compaction, got) {
                Ok(()) => {
                    self.phase = Phase::Prepare;
                    match got {
                        Compacted::Entry => self.ctx += 1,
                        Compacted::Nothing | Compacted::Failed => {}
                    }
                }
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
                        self.ctx += 1;
                        self.note = None;
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
        Phase::Prepare => Input::answer(Answer::Reply(if rng.chance(20) {
            Reply::Overflow {
                cut: rng.chance(70),
            }
        } else {
            Reply::Text
        })),
        Phase::Call => Input::answer(match rng.below(100) {
            0..10 => Answer::Reply(Reply::Text),
            10..40 => Answer::Reply(Reply::Calls),
            40..55 => Answer::Reply(Reply::Deferred(())),
            55..70 => Answer::Reply(Reply::Error {
                retryable: rng.chance(70),
                noted: rng.chance(50),
            }),
            // Half of these hold no text and no tool call.
            70..85 => Answer::Ended(Ended {
                tool_use: rng.chance(50),
                text: rng.chance(30),
                calls: rng.chance(30),
                retrying: rng.chance(70),
            }),
            _ => Answer::Reply(Reply::Overflow {
                cut: rng.chance(60),
            }),
        }),
        Phase::Compact(_) => Input::Go {
            answer: Answer::Reply(Reply::Text),
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
                answer: Answer::Reply(Reply::Text),
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
        ctx: 0,
        note: None,
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

/// One scenario of cuts: after a round, every reply is `cut` (a noted
/// error or a message with no answer) until the retries run out.
fn repeated_cuts(limits: Limits, cut: Answer, events: &mut String, transcript: &mut String) {
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
        ctx: 0,
        note: None,
        out: String::new(),
    };
    let round = [
        Input::answer(Answer::Reply(Reply::Text)),
        Input::answer(Answer::Reply(Reply::Calls)),
        Input::Go {
            answer: Answer::Reply(Reply::Text),
            hash: 1,
            fin: Fin::Goes,
            got: Compacted::Entry,
        },
    ];
    for input in round {
        input.write(events);
        run.input(input);
    }
    while run.phase != Phase::Ended {
        let input = match run.phase {
            Phase::Call => Input::answer(cut),
            Phase::Prepare | Phase::Compact(_) | Phase::Tools | Phase::Ended => {
                Input::answer(Answer::Reply(Reply::Text))
            }
        };
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
    // Cut after cut until the retries run out: each retry sends a request
    // with a new note.
    for max_retries in 0..4 {
        let cuts = [
            Answer::Reply(Reply::Error {
                retryable: true,
                noted: true,
            }),
            Answer::Ended(Ended {
                tool_use: false,
                text: false,
                calls: false,
                retrying: true,
            }),
        ];
        for cut in cuts {
            repeated_cuts(
                limits(3, 1, max_retries, LOOP_ROUNDS),
                cut,
                &mut events,
                &mut transcript,
            );
        }
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
