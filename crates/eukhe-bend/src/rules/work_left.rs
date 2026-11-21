//! Whether a run goes on past a final answer that leaves task work undone
//! (`bend/work_left.bend`, entry `bend/ffi_work_left.bend`;
//! `laws/work_left.bend`). Rust gathers the facts at a final answer and
//! acts on the step; the rule runs in the compiled core.

use crate::wire::{Reader, Writer, NAT_MAX};
use crate::{call, Entry, Error};

/// The progress check's verdict at the final answer (`bend/progress.bend`
/// `judge`), with its count of continuations in a row that made no new
/// tool result.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Progress {
    Go {
        stalls: u64,
    },
    /// The count reached `directors.stallSteps`.
    Stop {
        stalls: u64,
    },
}

/// The final-answer judge's reading of the answer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Reading {
    /// Not read yet.
    Unread,
    /// The answer states no work of the task left.
    Finished,
    /// The answer states work of the task left.
    Left,
    /// The judge gave no verdict.
    Unjudged,
}

impl Reading {
    /// The reading's tag on the wire (the work-left and autonomous
    /// requests): 0 not read, 1 no work left, 2 work left, 3 no verdict.
    pub(crate) fn tag(self) -> u32 {
        match self {
            Self::Unread => 0,
            Self::Finished => 1,
            Self::Left => 2,
            Self::Unjudged => 3,
        }
    }
}

/// The facts at a final answer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(clippy::struct_excessive_bools)] // the independent facts of the wire's request
pub struct Facts {
    /// An autonomous run or a loop drives the run.
    pub driven: bool,
    /// Input is queued: user input, or unsettled children or workflow runs.
    pub queued: bool,
    /// The run made a tool call with an effect since the user's last
    /// message.
    pub acted: bool,
    /// The session's budget admits more work.
    pub funded: bool,
    pub progress: Progress,
    /// The steps the Director loop has left.
    pub left: u64,
    pub reading: Reading,
}

/// What the run does at the final answer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Step {
    /// Go on with one continuation; the loop has `left` steps after it.
    Continue { left: u64 },
    /// The final answer stands.
    Yield,
    /// Ask the judge for its reading, then decide again with it.
    Ask,
}

/// The step at a final answer with `facts`: it goes on exactly when
/// nothing drives the run, nothing is queued, it acted, the budget admits
/// work, the progress check goes on, the loop has a step left and the
/// judge read work left; it asks for the reading when only the reading is
/// missing; else it yields. The counts saturate at the wire's
/// [`NAT_MAX`].
///
/// # Errors
///
/// A compiled-core failure or a malformed reply (an inconsistent build).
pub fn step(facts: Facts) -> Result<Step, Error> {
    let mut request = Writer::new();
    request
        .bool(facts.driven)
        .bool(facts.queued)
        .bool(facts.acted)
        .bool(facts.funded);
    match facts.progress {
        Progress::Go { stalls } => request.tag(0).nat(stalls.min(NAT_MAX)),
        Progress::Stop { stalls } => request.tag(1).nat(stalls.min(NAT_MAX)),
    };
    request
        .nat(facts.left.min(NAT_MAX))
        .tag(facts.reading.tag());
    let reply = call(Entry::WorkLeft, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let step = match reader.tag_of(3, "a step")? {
        0 => Step::Continue {
            left: reader.nat()?,
        },
        1 => Step::Yield,
        // `tag_of` answers a tag below 3: this is 2.
        _ => Step::Ask,
    };
    reader.end()?;
    Ok(step)
}

#[cfg(test)]
mod tests {
    use super::*;

    const OPEN: Facts = Facts {
        driven: false,
        queued: false,
        acted: true,
        funded: true,
        progress: Progress::Go { stalls: 1 },
        left: 3,
        reading: Reading::Left,
    };

    /// The facts cross the wire in the order the core reads them: a run
    /// it may judge goes on with one step spent, asks while unread, and
    /// yields for every fact that keeps it.
    #[test]
    fn the_core_reads_each_fact() {
        let steps = [
            OPEN,
            Facts {
                reading: Reading::Unread,
                ..OPEN
            },
            Facts {
                reading: Reading::Finished,
                ..OPEN
            },
            Facts {
                reading: Reading::Unjudged,
                ..OPEN
            },
            Facts {
                driven: true,
                ..OPEN
            },
            Facts {
                queued: true,
                ..OPEN
            },
            Facts {
                acted: false,
                ..OPEN
            },
            Facts {
                funded: false,
                ..OPEN
            },
            Facts {
                progress: Progress::Stop { stalls: 3 },
                ..OPEN
            },
            Facts { left: 0, ..OPEN },
            Facts {
                left: u64::MAX,
                ..OPEN
            },
        ]
        .map(|facts| step(facts).unwrap());
        assert_eq!(
            steps,
            [
                Step::Continue { left: 2 },
                Step::Ask,
                Step::Yield,
                Step::Yield,
                Step::Yield,
                Step::Yield,
                Step::Yield,
                Step::Yield,
                Step::Yield,
                Step::Yield,
                Step::Continue { left: NAT_MAX - 1 },
            ]
        );
    }
}
