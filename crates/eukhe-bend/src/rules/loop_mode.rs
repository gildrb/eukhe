//! The decisions of `/loop`: the model `bend/loop.bend`, entry
//! `bend/ffi_loop.bend`, laws `laws/loop/`.
//!
//! The caller keeps the [`LoopState`] (in the session's durable storage)
//! and sends it with each [`LoopEvent`]; the core answers the next state
//! and the one [`LoopAct`] to carry out. The caller gathers the facts (the
//! clock, the condition command's exit status, whether the session is
//! idle, whether the budget funds a turn) and decides nothing.

use eukhe_types::loop_mode::{
    LoopCheck, LoopCondition, LoopEnd, LoopEvidence, LoopLimit, LoopPhase, LoopState, LoopVerdict,
};

use crate::wire::{Reader, WireError, Writer};
use crate::{call, Entry, Error};

/// How a turn of the loop settled.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TurnOutcome {
    /// It ran to its end (a final answer).
    Ran,
    /// It failed.
    Errored,
    /// It did not run to its end: refused, consumed locally, or
    /// interrupted by the user.
    Halted,
}

/// What happened to the loop.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LoopEvent {
    /// `/loop` with its bound, its condition, its inline prompt and the
    /// clock: it starts a loop, or ends the one that is on.
    Enter {
        limit: Option<LoopLimit>,
        condition: Option<LoopCondition>,
        prompt: Option<String>,
        now_ms: u64,
    },
    /// `/loop --stop`.
    Stop,
    /// The user's interrupt.
    Abort,
    /// The user sent a prompt that starts a turn.
    Prompt { text: String },
    /// Iteration `iteration`'s turn settled. `blocked`: the session is
    /// not idle (queued input, unsettled work). `funded`: the budget funds
    /// one more turn.
    Settled {
        iteration: u64,
        outcome: TurnOutcome,
        blocked: bool,
        now_ms: u64,
        funded: bool,
    },
    /// The condition command ran after iteration `iteration`.
    Judged {
        iteration: u64,
        evidence: LoopEvidence,
        blocked: bool,
        now_ms: u64,
        funded: bool,
    },
    /// The pending work is taken up again (a worker that started again
    /// and read the state from storage).
    Restart,
}

/// What the caller does now.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LoopAct {
    /// Nothing.
    Rest,
    /// Start iteration `iteration` with `text`.
    Submit { iteration: u64, text: String },
    /// The user's own prompt is iteration `iteration`.
    Adopt { iteration: u64 },
    /// Run the condition command after iteration `iteration`.
    Judge { iteration: u64 },
    /// Iteration `iteration`'s turn is the one in flight: continue it,
    /// and send `text` only if it never was sent.
    Resume { iteration: u64, text: String },
    /// The loop ended: tell why, once.
    Report(LoopEnd),
    /// Ask again once the session is idle.
    Defer,
}

/// The request tags of the entry.
const STEP: u32 = 0;
const VERDICT: u32 = 1;

/// The state after `event`, and what to do now.
///
/// # Errors
///
/// A number past the wire's bound (99 999 999 999 999), a text past its
/// length bound, or a failed call to the compiled core.
pub fn step(state: &LoopState, event: &LoopEvent) -> Result<(LoopState, LoopAct), Error> {
    let mut w = Writer::new();
    w.tag(STEP);
    put_state(&mut w, state);
    match event {
        LoopEvent::Enter {
            limit,
            condition,
            prompt,
            now_ms,
        } => {
            w.tag(0);
            match limit {
                None => w.tag(0),
                Some(LoopLimit::Iterations { iterations }) => w.tag(1).nat(*iterations),
                Some(LoopLimit::Duration { duration_ms }) => w.tag(2).nat(*duration_ms),
            };
            put_condition(&mut w, condition.as_ref());
            match prompt {
                Some(text) => w.some().str(text),
                None => w.none(),
            };
            w.nat(*now_ms);
        }
        LoopEvent::Stop => {
            w.tag(1);
        }
        LoopEvent::Abort => {
            w.tag(2);
        }
        LoopEvent::Prompt { text } => {
            w.tag(3).str(text);
        }
        LoopEvent::Settled {
            iteration,
            outcome,
            blocked,
            now_ms,
            funded,
        } => {
            w.tag(4)
                .nat(*iteration)
                .tag(match outcome {
                    TurnOutcome::Ran => 0,
                    TurnOutcome::Errored => 1,
                    TurnOutcome::Halted => 2,
                })
                .bool(*blocked)
                .nat(*now_ms)
                .bool(*funded);
        }
        LoopEvent::Judged {
            iteration,
            evidence,
            blocked,
            now_ms,
            funded,
        } => {
            w.tag(5).nat(*iteration);
            put_evidence(&mut w, *evidence);
            w.bool(*blocked).nat(*now_ms).bool(*funded);
        }
        LoopEvent::Restart => {
            w.tag(6);
        }
    }
    let reply = call(Entry::Loop, &w.finish()?)?;
    let mut r = Reader::reply(&reply)?;
    let next = read_state(&mut r)?;
    let act = match r.tag_of(7, "a loop act")? {
        0 => LoopAct::Rest,
        1 => LoopAct::Submit {
            iteration: r.nat()?,
            text: r.str()?.to_owned(),
        },
        2 => LoopAct::Adopt {
            iteration: r.nat()?,
        },
        3 => LoopAct::Judge {
            iteration: r.nat()?,
        },
        4 => LoopAct::Resume {
            iteration: r.nat()?,
            text: r.str()?.to_owned(),
        },
        5 => LoopAct::Report(read_end(&mut r)?),
        // `tag_of` answers a tag below 7: this is 6.
        _ => LoopAct::Defer,
    };
    r.end()?;
    Ok((next, act))
}

/// What `evidence` says of the stop condition of an `--until` (`until`)
/// or a `--while` loop.
///
/// # Errors
///
/// An exit status past the wire's bound, or a failed call to the compiled
/// core.
pub fn verdict(until: bool, evidence: LoopEvidence) -> Result<LoopVerdict, Error> {
    let mut w = Writer::new();
    w.tag(VERDICT).bool(until);
    put_evidence(&mut w, evidence);
    let reply = call(Entry::Loop, &w.finish()?)?;
    let mut r = Reader::reply(&reply)?;
    let verdict = match r.tag_of(4, "a loop verdict")? {
        0 => LoopVerdict::Confirmed,
        1 => LoopVerdict::Refuted,
        2 => LoopVerdict::Broken,
        // `tag_of` answers a tag below 4: this is 3.
        _ => LoopVerdict::Unjudged,
    };
    r.end()?;
    Ok(verdict)
}

fn put_condition(w: &mut Writer, condition: Option<&LoopCondition>) {
    match condition {
        None => w.tag(0),
        Some(LoopCondition {
            command,
            until: true,
        }) => w.tag(1).str(command),
        Some(LoopCondition {
            command,
            until: false,
        }) => w.tag(2).str(command),
    };
}

fn read_condition(r: &mut Reader<'_>) -> Result<Option<LoopCondition>, WireError> {
    Ok(match r.tag_of(3, "a loop condition")? {
        0 => None,
        1 => Some(LoopCondition {
            command: r.str()?.to_owned(),
            until: true,
        }),
        // `tag_of` answers a tag below 3: this is 2.
        _ => Some(LoopCondition {
            command: r.str()?.to_owned(),
            until: false,
        }),
    })
}

fn put_evidence(w: &mut Writer, evidence: LoopEvidence) {
    match evidence {
        LoopEvidence::Exited { code } => w.tag(0).nat(code),
        LoopEvidence::NoStatus => w.tag(1),
        LoopEvidence::TimedOut => w.tag(2),
        LoopEvidence::SpawnFailed => w.tag(3),
        LoopEvidence::Cancelled => w.tag(4),
    };
}

fn read_evidence(r: &mut Reader<'_>) -> Result<LoopEvidence, WireError> {
    Ok(match r.tag_of(5, "loop evidence")? {
        0 => LoopEvidence::Exited { code: r.nat()? },
        1 => LoopEvidence::NoStatus,
        2 => LoopEvidence::TimedOut,
        3 => LoopEvidence::SpawnFailed,
        // `tag_of` answers a tag below 5: this is 4.
        _ => LoopEvidence::Cancelled,
    })
}

fn end_tag(end: LoopEnd) -> u32 {
    match end {
        LoopEnd::Satisfied => 0,
        LoopEnd::CheckBroke => 1,
        LoopEnd::OutOfTurns => 2,
        LoopEnd::OutOfTime => 3,
        LoopEnd::TurnsFailed => 4,
        LoopEnd::OutOfBudget => 5,
        LoopEnd::Stopped => 6,
    }
}

fn read_end(r: &mut Reader<'_>) -> Result<LoopEnd, WireError> {
    Ok(match r.tag_of(7, "a loop end")? {
        0 => LoopEnd::Satisfied,
        1 => LoopEnd::CheckBroke,
        2 => LoopEnd::OutOfTurns,
        3 => LoopEnd::OutOfTime,
        4 => LoopEnd::TurnsFailed,
        5 => LoopEnd::OutOfBudget,
        // `tag_of` answers a tag below 7: this is 6.
        _ => LoopEnd::Stopped,
    })
}

fn put_maybe_nat(w: &mut Writer, value: Option<u64>) {
    match value {
        Some(n) => w.some().nat(n),
        None => w.none(),
    };
}

fn read_maybe_nat(r: &mut Reader<'_>) -> Result<Option<u64>, WireError> {
    Ok(if r.maybe()? { Some(r.nat()?) } else { None })
}

fn put_state(w: &mut Writer, state: &LoopState) {
    match state.phase {
        LoopPhase::Off => w.tag(0),
        LoopPhase::Armed => w.tag(1),
        LoopPhase::Turn => w.tag(2),
        LoopPhase::Judging => w.tag(3),
        LoopPhase::Paused => w.tag(4),
        LoopPhase::Ended { end } => w.tag(5).tag(end_tag(end)),
    };
    w.nat(state.iteration);
    put_maybe_nat(w, state.remaining);
    put_maybe_nat(w, state.deadline_ms);
    put_condition(w, state.condition.as_ref());
    w.str(&state.prompt).nat(state.failures);
    match state.last_check {
        None => w.tag(0),
        Some(LoopCheck {
            iteration,
            evidence,
        }) => {
            w.tag(1).nat(iteration);
            put_evidence(w, evidence);
            w
        }
    };
}

fn read_state(r: &mut Reader<'_>) -> Result<LoopState, WireError> {
    let phase = match r.tag_of(6, "a loop phase")? {
        0 => LoopPhase::Off,
        1 => LoopPhase::Armed,
        2 => LoopPhase::Turn,
        3 => LoopPhase::Judging,
        4 => LoopPhase::Paused,
        // `tag_of` answers a tag below 6: this is 5.
        _ => LoopPhase::Ended { end: read_end(r)? },
    };
    let iteration = r.nat()?;
    let remaining = read_maybe_nat(r)?;
    let deadline_ms = read_maybe_nat(r)?;
    let condition = read_condition(r)?;
    let prompt = r.str()?.to_owned();
    let failures = r.nat()?;
    let last_check = if r.tag_of(2, "a loop check")? == 0 {
        None
    } else {
        Some(LoopCheck {
            iteration: r.nat()?,
            evidence: read_evidence(r)?,
        })
    };
    Ok(LoopState {
        phase,
        iteration,
        remaining,
        deadline_ms,
        condition,
        prompt,
        failures,
        last_check,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn until(command: &str) -> LoopCondition {
        LoopCondition {
            command: command.to_owned(),
            until: true,
        }
    }

    /// The acts of one whole loop, each step through the compiled core
    /// with the state the step before answered (the rule itself is pinned
    /// by `laws/loop/`): start, a refuting check, a restart, a confirming
    /// check, a late event.
    #[test]
    fn a_loop_runs_to_its_confirmed_end_in_the_core() {
        let events = [
            LoopEvent::Enter {
                limit: Some(LoopLimit::Iterations { iterations: 1 }),
                condition: Some(until("test -f done")),
                prompt: Some("fix it".to_owned()),
                now_ms: 5,
            },
            LoopEvent::Settled {
                iteration: 1,
                outcome: TurnOutcome::Ran,
                blocked: false,
                now_ms: 6,
                funded: true,
            },
            LoopEvent::Judged {
                iteration: 1,
                evidence: LoopEvidence::Exited { code: 1 },
                blocked: false,
                now_ms: 7,
                funded: true,
            },
            LoopEvent::Restart,
            LoopEvent::Settled {
                iteration: 2,
                outcome: TurnOutcome::Ran,
                blocked: false,
                now_ms: 8,
                funded: true,
            },
            LoopEvent::Judged {
                iteration: 2,
                evidence: LoopEvidence::Exited { code: 0 },
                blocked: false,
                now_ms: 9,
                funded: true,
            },
            LoopEvent::Settled {
                iteration: 2,
                outcome: TurnOutcome::Ran,
                blocked: false,
                now_ms: 10,
                funded: true,
            },
        ];
        let mut state = LoopState::default();
        let mut acts = Vec::new();
        for event in &events {
            let (next, act) = step(&state, event).expect("a step");
            state = next;
            acts.push(act);
        }
        assert_eq!(
            acts,
            vec![
                LoopAct::Submit {
                    iteration: 1,
                    text: "fix it".to_owned()
                },
                LoopAct::Judge { iteration: 1 },
                LoopAct::Submit {
                    iteration: 2,
                    text: "fix it".to_owned()
                },
                LoopAct::Resume {
                    iteration: 2,
                    text: "fix it".to_owned()
                },
                LoopAct::Judge { iteration: 2 },
                LoopAct::Report(LoopEnd::Satisfied),
                LoopAct::Rest,
            ]
        );
        assert_eq!(
            state,
            LoopState {
                phase: LoopPhase::Ended {
                    end: LoopEnd::Satisfied
                },
                iteration: 2,
                remaining: Some(0),
                deadline_ms: None,
                condition: Some(until("test -f done")),
                prompt: "fix it".to_owned(),
                failures: 0,
                last_check: Some(LoopCheck {
                    iteration: 2,
                    evidence: LoopEvidence::Exited { code: 0 }
                }),
            }
        );
    }

    /// Every state shape survives the wire: the Rust writer and reader
    /// agree with the entry's reader and writer (a restart changes
    /// nothing: `loop_restart_changes_nothing`).
    #[test]
    fn every_state_shape_survives_the_wire() {
        let phases = [
            LoopPhase::Off,
            LoopPhase::Armed,
            LoopPhase::Turn,
            LoopPhase::Judging,
            LoopPhase::Paused,
            LoopPhase::Ended {
                end: LoopEnd::Satisfied,
            },
            LoopPhase::Ended {
                end: LoopEnd::CheckBroke,
            },
            LoopPhase::Ended {
                end: LoopEnd::OutOfTurns,
            },
            LoopPhase::Ended {
                end: LoopEnd::OutOfTime,
            },
            LoopPhase::Ended {
                end: LoopEnd::TurnsFailed,
            },
            LoopPhase::Ended {
                end: LoopEnd::OutOfBudget,
            },
            LoopPhase::Ended {
                end: LoopEnd::Stopped,
            },
        ];
        let evidence = [
            LoopEvidence::Exited { code: 137 },
            LoopEvidence::NoStatus,
            LoopEvidence::TimedOut,
            LoopEvidence::SpawnFailed,
            LoopEvidence::Cancelled,
        ];
        for (index, phase) in phases.into_iter().enumerate() {
            let state = LoopState {
                phase,
                iteration: 9,
                remaining: (index % 2 == 0).then_some(4),
                deadline_ms: (index % 3 == 0).then_some(1_700_000_000_000),
                condition: match index % 3 {
                    0 => None,
                    1 => Some(until("grep -q 'a b' f, é")),
                    _ => Some(LoopCondition {
                        command: "true".to_owned(),
                        until: false,
                    }),
                },
                prompt: "do, the\nthing é".to_owned(),
                failures: 2,
                last_check: (index % 2 == 1).then_some(LoopCheck {
                    iteration: 8,
                    evidence: evidence[index % evidence.len()],
                }),
            };
            let (next, _) = step(&state, &LoopEvent::Restart).expect("a step");
            assert_eq!(next, state);
        }
    }

    /// The verdict table comes from the compiled core
    /// (`loop_verdict_table`).
    #[test]
    fn the_core_reads_exit_status_only() {
        use LoopVerdict::{Broken, Confirmed, Refuted, Unjudged};
        let table: Vec<LoopVerdict> = [true, false]
            .into_iter()
            .flat_map(|until| {
                [
                    LoopEvidence::Exited { code: 0 },
                    LoopEvidence::Exited { code: 1 },
                    LoopEvidence::Exited { code: 2 },
                    LoopEvidence::Exited { code: 126 },
                    LoopEvidence::Exited { code: 127 },
                    LoopEvidence::NoStatus,
                    LoopEvidence::TimedOut,
                    LoopEvidence::SpawnFailed,
                    LoopEvidence::Cancelled,
                ]
                .map(|evidence| verdict(until, evidence).expect("a verdict"))
            })
            .collect();
        assert_eq!(
            table,
            vec![
                Confirmed, Refuted, Refuted, Broken, Broken, Broken, Broken, Broken, Unjudged,
                Refuted, Confirmed, Confirmed, Broken, Broken, Broken, Broken, Broken, Unjudged,
            ]
        );
    }
}
