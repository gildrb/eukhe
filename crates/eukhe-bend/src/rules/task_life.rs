//! The lifecycle rules of a durable task (`bend/task_life.bend`, entry
//! `bend/ffi_task_life.bend`; `laws/task_life.bend`): the transitions the
//! scheduler writes ([`step`]), what a new Harness does to a stored state
//! ([`resume`]), how a waiting task treats the tasks it waits on
//! ([`join`]), and abort marks ([`merge`], [`cascade`]). Each function
//! encodes its request, calls [`Entry::TaskLife`] and decodes the reply.
//!
//! The rules never read a payload (a checkpoint, the result or error of an
//! outcome): the caller names each one by a handle, a number the rules
//! carry from the request into the reply.

use crate::wire::{Reader, Writer};
use crate::{call, Entry, Error};

/// How a waiting task treats the tasks it waits on (`Tl.Policy`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Policy {
    /// Abort the other awaited tasks once one fails.
    FailFast,
    /// Wait for every awaited task.
    AllSettled,
}

/// How an outcome ended a task (`Tl.Res`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Status {
    /// The task produced its result.
    Completed,
    /// The task committed a failure.
    Failed,
    /// The task was aborted.
    Aborted,
    /// No definition can resume the task.
    Orphaned,
    /// The runtime detected a contract failure.
    Faulted,
}

/// An outcome: how it ended, and the handle of its payload (`Tl.Outcome`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Outcome {
    /// How the outcome ended the task.
    pub status: Status,
    /// The caller's handle of the outcome's payload.
    pub payload: u64,
}

/// A task state; `checkpoint` is the caller's handle of a checkpoint
/// (`Tl.St`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum State {
    /// Eligible for scheduling.
    Pending { checkpoint: u64 },
    /// Reserved by one invocation.
    Running { checkpoint: u64 },
    /// Parked until the tasks it waits on allow it to run.
    Waiting { checkpoint: u64, policy: Policy },
    /// Outcome decided, held while ordinary owned work below is live.
    Completing { outcome: Outcome },
    /// Settled for good.
    Terminal { outcome: Outcome },
}

/// The state a running task commits (`Tl.Next`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Next {
    /// Go on from a new checkpoint.
    Running { checkpoint: u64 },
    /// Wait, then resume from a checkpoint.
    Waiting { checkpoint: u64, policy: Policy },
    /// End with an outcome.
    Ended { outcome: Outcome },
}

/// A transition the scheduler writes (`Tl.Ev`). `owned_live`: ordinary
/// owned work below the task is live, so a decided outcome is held.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Event {
    /// Reserve the task for an invocation.
    Reserve,
    /// A running task's commit.
    Commit { next: Next, owned_live: bool },
    /// Hand a running task back to pending (a replacement definition).
    Requeue,
    /// An outcome the scheduler decides (a fault, an orphan).
    Settle { outcome: Outcome, owned_live: bool },
    /// Finalize a held outcome.
    Finalize { owned_live: bool },
}

/// Why a transition does not apply (`Tl.Why`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Refusal {
    /// The task is terminal.
    Ended,
    /// The task holds its outcome (completing) and runs no code.
    Held,
    /// The transition needs a running task.
    NotRunning,
    /// Finalization needs a task that holds an outcome.
    NotHeld,
}

/// A stored state after a restart, and whether its failFast wait is
/// checked again.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Resumed {
    /// The state the new Harness schedules.
    pub state: State,
    /// A failFast wait: check its awaited tasks again.
    pub check_fail_fast: bool,
}

/// One task a waiting task waits on.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Member {
    /// The task is not terminal.
    pub live: bool,
    /// The task holds or ended with an outcome other than completed.
    pub failed: bool,
}

/// The join of a waiting task over its awaited tasks.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Join {
    /// No awaited task is live: the waiting task may run.
    pub ready: bool,
    /// Per awaited task, in order: abort it.
    pub abort: Vec<bool>,
}

/// An abort mark (`Tl.Mark`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mark {
    /// No mark.
    Clear,
    /// The `restart` mark of a task abandoned after a restart.
    Restart,
    /// An abort request.
    Request,
}

/// One task a cascade's walk reached below its owner (`Tl.Row`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Row {
    /// The task is not terminal.
    pub live: bool,
    /// The task is a background task.
    pub background: bool,
    /// The task's mark.
    pub mark: Mark,
}

fn put_policy(request: &mut Writer, policy: Policy) {
    request.tag(match policy {
        Policy::FailFast => 0,
        Policy::AllSettled => 1,
    });
}

fn get_policy(reply: &mut Reader<'_>) -> Result<Policy, Error> {
    Ok(match reply.tag_of(2, "a policy")? {
        0 => Policy::FailFast,
        _ => Policy::AllSettled,
    })
}

fn put_outcome(request: &mut Writer, outcome: Outcome) {
    request
        .tag(match outcome.status {
            Status::Completed => 0,
            Status::Failed => 1,
            Status::Aborted => 2,
            Status::Orphaned => 3,
            Status::Faulted => 4,
        })
        .nat(outcome.payload);
}

fn get_outcome(reply: &mut Reader<'_>) -> Result<Outcome, Error> {
    let status = match reply.tag_of(5, "an outcome")? {
        0 => Status::Completed,
        1 => Status::Failed,
        2 => Status::Aborted,
        3 => Status::Orphaned,
        _ => Status::Faulted,
    };
    Ok(Outcome {
        status,
        payload: reply.nat()?,
    })
}

fn put_state(request: &mut Writer, state: State) {
    match state {
        State::Pending { checkpoint } => {
            request.tag(0).nat(checkpoint);
        }
        State::Running { checkpoint } => {
            request.tag(1).nat(checkpoint);
        }
        State::Waiting { checkpoint, policy } => {
            request.tag(2).nat(checkpoint);
            put_policy(request, policy);
        }
        State::Completing { outcome } => {
            request.tag(3);
            put_outcome(request, outcome);
        }
        State::Terminal { outcome } => {
            request.tag(4);
            put_outcome(request, outcome);
        }
    }
}

fn get_state(reply: &mut Reader<'_>) -> Result<State, Error> {
    Ok(match reply.tag_of(5, "a task state")? {
        0 => State::Pending {
            checkpoint: reply.nat()?,
        },
        1 => State::Running {
            checkpoint: reply.nat()?,
        },
        2 => State::Waiting {
            checkpoint: reply.nat()?,
            policy: get_policy(reply)?,
        },
        3 => State::Completing {
            outcome: get_outcome(reply)?,
        },
        _ => State::Terminal {
            outcome: get_outcome(reply)?,
        },
    })
}

fn put_event(request: &mut Writer, event: Event) {
    match event {
        Event::Reserve => {
            request.tag(0);
        }
        Event::Commit { next, owned_live } => {
            request.tag(1);
            match next {
                Next::Running { checkpoint } => {
                    request.tag(0).nat(checkpoint);
                }
                Next::Waiting { checkpoint, policy } => {
                    request.tag(1).nat(checkpoint);
                    put_policy(request, policy);
                }
                Next::Ended { outcome } => {
                    request.tag(2);
                    put_outcome(request, outcome);
                }
            }
            request.bool(owned_live);
        }
        Event::Requeue => {
            request.tag(2);
        }
        Event::Settle {
            outcome,
            owned_live,
        } => {
            request.tag(3);
            put_outcome(request, outcome);
            request.bool(owned_live);
        }
        Event::Finalize { owned_live } => {
            request.tag(4).bool(owned_live);
        }
    }
}

fn put_mark(request: &mut Writer, mark: Mark) {
    request.tag(match mark {
        Mark::Clear => 0,
        Mark::Restart => 1,
        Mark::Request => 2,
    });
}

fn get_mark(reply: &mut Reader<'_>) -> Result<Mark, Error> {
    Ok(match reply.tag_of(3, "a mark")? {
        0 => Mark::Clear,
        1 => Mark::Restart,
        _ => Mark::Request,
    })
}

fn get_bools(reply: &mut Reader<'_>) -> Result<Vec<bool>, Error> {
    let n = reply.count()?;
    let mut items = Vec::with_capacity(n);
    for _ in 0..n {
        items.push(reply.bool()?);
    }
    Ok(items)
}

/// The state after `event`, or why it does not apply (`Tl.step`): a
/// terminal task refuses everything; a reservation runs a pending,
/// running or waiting task at its checkpoint; only a running task commits
/// or is handed back to pending; a decided outcome holds as completing
/// while owned work is live, else it is terminal; a held outcome is
/// finalized to terminal, the same outcome, once no owned work is live.
///
/// # Errors
///
/// [`Error::Wire`] when a handle is past [`crate::wire::NAT_MAX`]; else
/// only from an inconsistent build (see [`crate::expect_core`]).
pub fn step(state: State, event: Event) -> Result<Result<State, Refusal>, Error> {
    let mut request = Writer::new();
    request.tag(0);
    put_state(&mut request, state);
    put_event(&mut request, event);
    let reply = call(Entry::TaskLife, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let stepped = match reply.tag_of(2, "a step")? {
        0 => Err(match reply.tag_of(4, "a refusal")? {
            0 => Refusal::Ended,
            1 => Refusal::Held,
            2 => Refusal::NotRunning,
            _ => Refusal::NotHeld,
        }),
        _ => Ok(get_state(&mut reply)?),
    };
    reply.end()?;
    Ok(stepped)
}

/// A stored state when a new Harness opens (`Tl.resume`): a running task
/// is pending at its checkpoint; a failFast wait is checked again;
/// nothing else changes.
///
/// # Errors
///
/// As [`step`].
pub fn resume(state: State) -> Result<Resumed, Error> {
    let mut request = Writer::new();
    request.tag(1);
    put_state(&mut request, state);
    let reply = call(Entry::TaskLife, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let resumed = Resumed {
        state: get_state(&mut reply)?,
        check_fail_fast: reply.bool()?,
    };
    reply.end()?;
    Ok(resumed)
}

/// A waiting task over its awaited tasks (`Tl.join`): it may run once
/// none is live; a failFast wait with a failed member aborts each live
/// member that did not fail; an allSettled wait aborts nothing.
///
/// # Errors
///
/// [`Error::Wire`] for more members than the wire counts; else only from
/// an inconsistent build (see [`crate::expect_core`]).
pub fn join(policy: Policy, members: &[Member]) -> Result<Join, Error> {
    let mut request = Writer::new();
    request.tag(2);
    put_policy(&mut request, policy);
    request.count(members.len());
    for member in members {
        request.bool(member.live);
    }
    request.count(members.len());
    for member in members {
        request.bool(member.failed);
    }
    let reply = call(Entry::TaskLife, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let joined = Join {
        ready: reply.bool()?,
        abort: get_bools(&mut reply)?,
    };
    reply.end()?;
    Ok(joined)
}

/// The stronger of two marks (`Tl.merge`): a request over a `restart`
/// mark over none.
///
/// # Errors
///
/// Only from an inconsistent build (see [`crate::expect_core`]).
pub fn merge(mark: Mark, by: Mark) -> Result<Mark, Error> {
    let mut request = Writer::new();
    request.tag(3);
    put_mark(&mut request, mark);
    put_mark(&mut request, by);
    let reply = call(Entry::TaskLife, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let merged = get_mark(&mut reply)?;
    reply.end()?;
    Ok(merged)
}

/// The mark of each task a cascade's walk reached below an owner in
/// `state` with `mark` (`Tl.cascade`): below a live owner with intent (a
/// mark, or a held outcome other than completed), a live foreground task
/// takes the owner's reason (`restart` from an abandoned owner that did not
/// fail, else a request) merged into its mark; every other task keeps its
/// mark.
///
/// # Errors
///
/// As [`step`], and [`Error::Wire`] for more rows than the wire counts.
pub fn cascade(state: State, mark: Mark, rows: &[Row]) -> Result<Vec<Mark>, Error> {
    let mut request = Writer::new();
    request.tag(4);
    put_state(&mut request, state);
    put_mark(&mut request, mark);
    request.count(rows.len());
    for row in rows {
        request.bool(row.live).bool(row.background);
        put_mark(&mut request, row.mark);
    }
    let reply = call(Entry::TaskLife, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let n = reply.count()?;
    let mut marks = Vec::with_capacity(n);
    for _ in 0..n {
        marks.push(get_mark(&mut reply)?);
    }
    reply.end()?;
    Ok(marks)
}

#[cfg(test)]
mod tests {
    use super::{
        cascade, join, merge, resume, step, Event, Join, Mark, Member, Next, Outcome, Policy,
        Refusal, Resumed, Row, State, Status,
    };

    const DONE: Outcome = Outcome {
        status: Status::Completed,
        payload: 9,
    };

    #[test]
    fn the_codec_carries_each_transition_through_the_core() {
        assert_eq!(
            [
                step(State::Pending { checkpoint: 7 }, Event::Reserve).unwrap(),
                step(
                    State::Running { checkpoint: 7 },
                    Event::Commit {
                        next: Next::Ended { outcome: DONE },
                        owned_live: true
                    }
                )
                .unwrap(),
                step(
                    State::Running { checkpoint: 7 },
                    Event::Commit {
                        next: Next::Waiting {
                            checkpoint: 8,
                            policy: Policy::AllSettled
                        },
                        owned_live: false
                    }
                )
                .unwrap(),
                step(
                    State::Completing { outcome: DONE },
                    Event::Finalize { owned_live: false }
                )
                .unwrap(),
                step(State::Terminal { outcome: DONE }, Event::Requeue).unwrap(),
                step(
                    State::Waiting {
                        checkpoint: 7,
                        policy: Policy::FailFast
                    },
                    Event::Requeue
                )
                .unwrap(),
            ],
            [
                Ok(State::Running { checkpoint: 7 }),
                Ok(State::Completing { outcome: DONE }),
                Ok(State::Waiting {
                    checkpoint: 8,
                    policy: Policy::AllSettled
                }),
                Ok(State::Terminal { outcome: DONE }),
                Err(Refusal::Ended),
                Err(Refusal::NotRunning),
            ]
        );
    }

    #[test]
    fn the_codec_carries_resume_join_and_marks_through_the_core() {
        assert_eq!(
            resume(State::Waiting {
                checkpoint: 3,
                policy: Policy::FailFast
            })
            .unwrap(),
            Resumed {
                state: State::Waiting {
                    checkpoint: 3,
                    policy: Policy::FailFast
                },
                check_fail_fast: true
            }
        );
        let member = |live, failed| Member { live, failed };
        assert_eq!(
            join(
                Policy::FailFast,
                &[member(true, false), member(false, true), member(true, true)]
            )
            .unwrap(),
            Join {
                ready: false,
                abort: vec![true, false, false]
            }
        );
        assert_eq!(merge(Mark::Request, Mark::Restart).unwrap(), Mark::Request);
        let failed = Outcome {
            status: Status::Failed,
            payload: 0,
        };
        let row = |live, background, mark| Row {
            live,
            background,
            mark,
        };
        assert_eq!(
            cascade(
                State::Completing { outcome: failed },
                Mark::Restart,
                &[
                    row(true, false, Mark::Clear),
                    row(false, false, Mark::Clear),
                    row(true, true, Mark::Clear),
                    row(true, false, Mark::Restart),
                ]
            )
            .unwrap(),
            [Mark::Request, Mark::Clear, Mark::Clear, Mark::Request]
        );
    }
}
