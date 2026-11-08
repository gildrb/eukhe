//! One tool call's journal (call 1-3) and its effect gate: the model
//! `bend/tool_call.bend`, entry `bend/ffi_tool_call.bend` (a stepper and a
//! call).
//!
//! The call lives in the compiled core. The Harness opens it where it
//! journals the call's start, sends each report the tool makes and the end
//! of its execute in the order they come, from any thread, and does what
//! each reply says (`tool_call_step_is_model` in `laws/tool_call.bend`):
//! a report is stored only before the end (`stream_settle_carries_all`);
//! the end settles the call once (`stream_settles_once`), as finished,
//! failed or cancelled. The Harness keeps what was reported.
//!
//! The gate (speculation, then effect): each handler of a tool task asks
//! it before anything of the call happens ([`enter`], [`recover`],
//! [`stop`]), with the call a committed entry holds (or none) and the tool
//! offered now (or none). A call runs only when a committed entry holds it
//! (`execute_after_committed`, `uncommitted_drop_inert`), and runs again
//! after a restart only when its policy is safe (`effect_once`); the
//! answers are the spec's (`tool_call_gate_is_spec`).

use crate::wire::{Reader, WireError, Writer};
use crate::{call, expect_core, Entry, Stepper};

/// Which attempt of a call opens.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Attempt {
    /// The call's first run.
    First,
    /// A rerun after a restart.
    Rerun,
}

/// What an open journals in the call's slot.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Begin {
    /// The slot goes running.
    Start,
    /// What the interrupted attempt published is cleared.
    Clear,
}

/// How a call settles, with what its execute returned.
#[derive(Debug)]
pub enum Ending<T, E> {
    /// With the tool's result.
    Finished(T),
    /// With the tool's error: it threw, its signal not aborted.
    Failed(E),
    /// Aborted: the abort handler settles it from the progress board.
    Cancelled(E),
}

/// One tool call, kept in the compiled core.
#[derive(Debug)]
pub struct CallJournal {
    stepper: Stepper,
}

impl CallJournal {
    /// The call of `attempt`, and what its open journals.
    #[must_use]
    pub fn open(attempt: Attempt) -> (Self, Begin) {
        let request = expect_core(
            Entry::ToolCall,
            Writer::new().bool(attempt == Attempt::First).finish(),
        );
        let (stepper, reply) =
            expect_core(Entry::ToolCall, Stepper::open(Entry::ToolCall, &request));
        let begin = expect_core(Entry::ToolCall, read_begin(&reply));
        (CallJournal { stepper }, begin)
    }

    /// The tool reports: whether the report is stored (false once the
    /// call ended).
    pub fn report(&mut self) -> bool {
        let request = expect_core(Entry::ToolCall, Writer::new().tag(0).finish());
        let reply = expect_core(Entry::ToolCall, self.stepper.step(&request));
        expect_core(Entry::ToolCall, read_report(&reply))
    }

    /// The tool's execute returned `executed`, its signal `aborted` or
    /// not: how the call settles, or `None` when it had already ended
    /// (nothing to do).
    pub fn end<T, E>(&mut self, executed: Result<T, E>, aborted: bool) -> Option<Ending<T, E>> {
        let request = expect_core(
            Entry::ToolCall,
            Writer::new()
                .tag(1)
                .bool(executed.is_err())
                .bool(aborted)
                .finish(),
        );
        let reply = expect_core(Entry::ToolCall, self.stepper.step(&request));
        let how = expect_core(Entry::ToolCall, read_end(&reply))?;
        Some(expect_core(Entry::ToolCall, ending(how, executed)))
    }
}

/// How a settle reads: 0 finished, 1 failed, 2 cancelled.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum How {
    Finished,
    Failed,
    Cancelled,
}

fn read_begin(reply: &str) -> Result<Begin, WireError> {
    let mut r = Reader::reply(reply)?;
    let begin = match r.tag_of(2, "an open's record")? {
        0 => Begin::Start,
        // `tag_of` answers a tag below 2: this is 1.
        _ => Begin::Clear,
    };
    r.end()?;
    Ok(begin)
}

fn read_report(reply: &str) -> Result<bool, WireError> {
    let mut r = Reader::reply(reply)?;
    let kept = match r.tag_of(2, "a report's answer: keep or refuse")? {
        0 => true,
        // `tag_of` answers a tag below 2: this is 1.
        _ => false,
    };
    r.end()?;
    Ok(kept)
}

fn read_end(reply: &str) -> Result<Option<How>, WireError> {
    let mut r = Reader::reply(reply)?;
    let how = match r.tag_of(4, "an end's answer")? {
        2 => Some(match r.tag_of(3, "a settle's ending")? {
            0 => How::Finished,
            1 => How::Failed,
            // `tag_of` answers a tag below 3: this is 2.
            _ => How::Cancelled,
        }),
        3 => None,
        // Tags 0 and 1 answer a report.
        _ => {
            return Err(WireError::Malformed {
                at: 0,
                expected: "an end's answer: settle or late",
            })
        }
    };
    r.end()?;
    Ok(how)
}

/// The settle `how` with what the execute returned: a finish carries its
/// result, a failure or a cancel its error.
fn ending<T, E>(how: How, executed: Result<T, E>) -> Result<Ending<T, E>, WireError> {
    match (how, executed) {
        (How::Finished, Ok(result)) => Ok(Ending::Finished(result)),
        (How::Failed, Err(error)) => Ok(Ending::Failed(error)),
        (How::Cancelled, Err(error)) => Ok(Ending::Cancelled(error)),
        (How::Finished, Err(_)) | (How::Failed | How::Cancelled, Ok(_)) => {
            Err(WireError::Malformed {
                at: 0,
                expected:
                    "a settle as the execute ended: finished on a result, else failed or cancelled",
            })
        }
    }
}

/// A tool's replay policy: whether a run a restart interrupted may run
/// again.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Replay {
    /// It may run again.
    Safe,
    /// It may have changed state: it never runs twice.
    Unsafe,
}

/// Why the abort handler runs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AbortCause {
    /// An abort was asked for.
    Requested,
    /// A restart abandoned the task.
    Restart,
}

/// Whether the call's intent was recorded before the abort.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Intent {
    /// Not recorded: the call never started.
    Unrecorded,
    /// Recorded: the call may have run.
    Recorded,
}

/// What the call phase does.
#[derive(Debug, PartialEq, Eq)]
pub enum Enter<C, T> {
    /// Record the intent, then execute.
    Run { call: C, tool: T },
    /// Settle `tool_unavailable`: the tool is no longer offered; nothing ran.
    Unavailable(C),
    /// No committed entry holds the call: nothing runs, nothing settles.
    Missing,
}

/// What the execute phase does after a restart.
#[derive(Debug, PartialEq, Eq)]
pub enum Recover<C, T> {
    /// Execute again.
    Rerun { call: C, tool: T },
    /// Settle `interrupted`: the call may have partially run; it does not
    /// run again. The tool, when still offered, says how it keeps output.
    Interrupted { call: C, tool: Option<T> },
    /// No committed entry holds the call: nothing runs, nothing settles.
    Missing,
}

/// How the abort handler settles.
#[derive(Debug, PartialEq, Eq)]
pub enum Stop<C> {
    /// `aborted`.
    Aborted(C),
    /// `interrupted`: a restart after the intent; the call may have run.
    Interrupted(C),
    /// `abandoned`: a restart before the intent; the call never started.
    Abandoned(C),
    /// No committed entry holds the call: nothing settles.
    Missing,
}

/// The gate's answer: 0 run, 1 missing, 2 unavailable, 3 rerun,
/// 4 interrupted, 5 aborted, 6 abandoned.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Go {
    Run,
    Missing,
    Unavailable,
    Rerun,
    Interrupted,
    Aborted,
    Abandoned,
}

/// The call phase of `call` (the call a committed entry holds, if any),
/// with `tool` (the tool offered now and its policy, if any).
#[must_use]
pub fn enter<C, T>(call: Option<C>, tool: Option<(T, Replay)>) -> Enter<C, T> {
    let mut request = Writer::new();
    request.tag(0).bool(call.is_some());
    put_now(&mut request, tool.as_ref().map(|(_, replay)| *replay));
    let go = ask(&mut request);
    expect_core(
        Entry::ToolCall,
        match (go, call, tool) {
            (Go::Run, Some(call), Some((tool, _))) => Ok(Enter::Run { call, tool }),
            (Go::Unavailable, Some(call), None) => Ok(Enter::Unavailable(call)),
            (Go::Missing, None, _) => Ok(Enter::Missing),
            (
                Go::Run
                | Go::Unavailable
                | Go::Missing
                | Go::Rerun
                | Go::Interrupted
                | Go::Aborted
                | Go::Abandoned,
                _,
                _,
            ) => Err(WireError::Malformed {
                at: 0,
                expected: "an enter's answer: run a found call of an offered tool, \
                           unavailable without the tool, missing without the call",
            }),
        },
    )
}

/// The execute phase of `call` after a restart: its intent recorded
/// `stored`; `tool` is the tool offered now and its policy, if any.
#[must_use]
pub fn recover<C, T>(call: Option<C>, stored: Replay, tool: Option<(T, Replay)>) -> Recover<C, T> {
    let mut request = Writer::new();
    request.tag(1).bool(call.is_some());
    put_replay(&mut request, stored);
    put_now(&mut request, tool.as_ref().map(|(_, replay)| *replay));
    let go = ask(&mut request);
    let tool = tool.map(|(tool, _)| tool);
    expect_core(
        Entry::ToolCall,
        match (go, call, tool) {
            (Go::Rerun, Some(call), Some(tool)) => Ok(Recover::Rerun { call, tool }),
            (Go::Interrupted, Some(call), tool) => Ok(Recover::Interrupted { call, tool }),
            (Go::Missing, None, _) => Ok(Recover::Missing),
            (
                Go::Run
                | Go::Unavailable
                | Go::Missing
                | Go::Rerun
                | Go::Interrupted
                | Go::Aborted
                | Go::Abandoned,
                _,
                _,
            ) => Err(WireError::Malformed {
                at: 0,
                expected: "a recovery's answer: rerun a found call of an offered tool, \
                           interrupted for a found call, missing without the call",
            }),
        },
    )
}

/// The abort handler of `call` (the call a committed entry holds, if any).
#[must_use]
pub fn stop<C>(call: Option<C>, cause: AbortCause, intent: Intent) -> Stop<C> {
    let mut request = Writer::new();
    request
        .tag(2)
        .bool(call.is_some())
        .bool(cause == AbortCause::Restart)
        .bool(intent == Intent::Recorded);
    let go = ask(&mut request);
    expect_core(
        Entry::ToolCall,
        match (go, call) {
            (Go::Aborted, Some(call)) => Ok(Stop::Aborted(call)),
            (Go::Interrupted, Some(call)) => Ok(Stop::Interrupted(call)),
            (Go::Abandoned, Some(call)) => Ok(Stop::Abandoned(call)),
            (Go::Missing, None) => Ok(Stop::Missing),
            (
                Go::Run
                | Go::Unavailable
                | Go::Missing
                | Go::Rerun
                | Go::Interrupted
                | Go::Aborted
                | Go::Abandoned,
                _,
            ) => Err(WireError::Malformed {
                at: 0,
                expected: "an abort's answer: a settle for a found call, missing without it",
            }),
        },
    )
}

fn put_replay(request: &mut Writer, replay: Replay) {
    request.tag(match replay {
        Replay::Safe => 0,
        Replay::Unsafe => 1,
    });
}

/// The tool as resolved now: 0 gone, 1 offered (its policy follows).
fn put_now(request: &mut Writer, tool: Option<Replay>) {
    match tool {
        None => {
            request.tag(0);
        }
        Some(replay) => {
            request.tag(1);
            put_replay(request, replay);
        }
    }
}

/// The gate's answer to the question `request` spells.
fn ask(request: &mut Writer) -> Go {
    let request = expect_core(Entry::ToolCall, request.finish());
    let reply = expect_core(Entry::ToolCall, call(Entry::ToolCall, &request));
    expect_core(Entry::ToolCall, read_go(&reply))
}

fn read_go(reply: &str) -> Result<Go, WireError> {
    let mut r = Reader::reply(reply)?;
    let go = match r.tag_of(7, "a gate's answer")? {
        0 => Go::Run,
        1 => Go::Missing,
        2 => Go::Unavailable,
        3 => Go::Rerun,
        4 => Go::Interrupted,
        5 => Go::Aborted,
        // `tag_of` answers a tag below 7: this is 6.
        _ => Go::Abandoned,
    };
    r.end()?;
    Ok(go)
}

#[cfg(test)]
mod tests {
    use super::{
        enter, recover, stop, AbortCause, Attempt, Begin, CallJournal, Ending, Enter, Intent,
        Recover, Replay, Stop,
    };

    /// The compiled core is reached: opens, reports before and after the
    /// end, each ending, a late end (the rule itself is pinned by
    /// `laws/tool_call.bend`).
    #[test]
    fn the_tool_call_runs_in_the_core() {
        let (mut first, start) = CallJournal::open(Attempt::First);
        let (mut rerun, clear) = CallJournal::open(Attempt::Rerun);
        let (mut aborted, _) = CallJournal::open(Attempt::First);
        let before = first.report();
        let finished = first.end(Ok::<u8, u8>(7), true);
        let after = first.report();
        let late = first.end(Err::<u8, u8>(1), true);
        let failed = rerun.end(Err::<u8, u8>(2), false);
        let cancelled = aborted.end(Err::<u8, u8>(3), true);
        assert_eq!(
            (start, clear, before, after),
            (Begin::Start, Begin::Clear, true, false)
        );
        assert!(matches!(
            (finished, late, failed, cancelled),
            (
                Some(Ending::Finished(7)),
                None,
                Some(Ending::Failed(2)),
                Some(Ending::Cancelled(3))
            )
        ));
    }

    /// The gate is reached in the compiled core, each answer once (the
    /// rule itself is pinned by `laws/tool_call.bend`): the Rust tests'
    /// cases of `tool_call_gate_example`.
    #[test]
    fn the_effect_gate_runs_in_the_core() {
        let entered = [
            enter(Some('c'), Some(('t', Replay::Unsafe))),
            enter(Some('c'), None),
            enter(None, Some(('t', Replay::Safe))),
        ];
        let recovered = [
            recover(Some('c'), Replay::Safe, Some(('t', Replay::Safe))),
            recover(Some('c'), Replay::Safe, Some(('t', Replay::Unsafe))),
            recover(Some('c'), Replay::Unsafe, Some(('t', Replay::Safe))),
            recover(Some('c'), Replay::Safe, None),
            recover(None, Replay::Safe, Some(('t', Replay::Safe))),
        ];
        let stopped = [
            stop(Some('c'), AbortCause::Requested, Intent::Recorded),
            stop(Some('c'), AbortCause::Restart, Intent::Recorded),
            stop(Some('c'), AbortCause::Restart, Intent::Unrecorded),
            stop(None, AbortCause::Requested, Intent::Unrecorded),
        ];
        assert_eq!(
            (entered, recovered, stopped),
            (
                [
                    Enter::Run {
                        call: 'c',
                        tool: 't'
                    },
                    Enter::Unavailable('c'),
                    Enter::Missing
                ],
                [
                    Recover::Rerun {
                        call: 'c',
                        tool: 't'
                    },
                    Recover::Interrupted {
                        call: 'c',
                        tool: Some('t')
                    },
                    Recover::Interrupted {
                        call: 'c',
                        tool: Some('t')
                    },
                    Recover::Interrupted {
                        call: 'c',
                        tool: None
                    },
                    Recover::Missing
                ],
                [
                    Stop::Aborted('c'),
                    Stop::Interrupted('c'),
                    Stop::Abandoned('c'),
                    Stop::Missing
                ]
            )
        );
    }
}
