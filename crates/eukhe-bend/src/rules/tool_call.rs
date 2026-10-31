//! One tool call's journal (call 1-3): the model
//! `bend/tool_call.bend`, stepper entry `bend/ffi_tool_call.bend`.
//!
//! The call lives in the compiled core. The Harness opens it where it
//! journals the call's start, sends each report the tool makes and the end
//! of its execute in the order they come, from any thread, and does what
//! each reply says (`tool_call_step_is_model` in `laws/tool_call.bend`):
//! a report is stored only before the end (`stream_settle_carries_all`);
//! the end settles the call once (`stream_settles_once`), as finished,
//! failed or cancelled. The Harness keeps what was reported.

use crate::wire::{Reader, WireError, Writer};
use crate::{expect_core, Entry, Stepper};

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

#[cfg(test)]
mod tests {
    use super::{Attempt, Begin, CallJournal, Ending};

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
}
