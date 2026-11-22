//! The progress check of a chain of continuations: how many of its
//! continuations in a row did no new work (no tool call with a new result:
//! an act fingerprint the session's acts did not hold,
//! `crate::durable::children::WorkLedger`), as the compiled core counts
//! it (`bend/progress.bend`, `laws/progress.bend`). The autonomous run's
//! continuations and the work-left Director's each keep a count; the
//! work-left chain stops where the run is steered.

use eukhe_bend::wire::{Reader, Writer, NAT_MAX};
use eukhe_bend::Entry;

/// The last progress check of the same chain: its count of continuations
/// in a row with no new work, and the session's work then (its
/// [`crate::durable::children::WorkLedger::count`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Prior {
    pub(crate) stalls: u64,
    pub(crate) work: u64,
}

/// The last progress check a chain stored, as the check now sees it:
/// whether it was of the same run (the run's first input), its count of
/// stalls and the work then.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Last {
    pub(crate) same_run: bool,
    pub(crate) stalls: u64,
    pub(crate) work: u64,
}

/// The prior check the progress check compares with (`compared` in
/// `bend/progress.bend`, the call of the compiled core's `work` entry;
/// `laws/work.bend`): the last check, when it was of the same run; else
/// none, and the check starts the count.
pub(crate) fn compared(last: Option<Last>) -> Option<Prior> {
    eukhe_bend::expect_core(Entry::Work, compared_call(last))
}

fn compared_call(last: Option<Last>) -> Result<Option<Prior>, eukhe_bend::Error> {
    let mut request = Writer::new();
    match last {
        None => request.none(),
        Some(last) => request
            .some()
            .bool(last.same_run)
            .nat(last.stalls.min(NAT_MAX))
            .nat(last.work.min(NAT_MAX)),
    };
    let reply = eukhe_bend::call(Entry::Work, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let prior = if reply.maybe()? {
        Some(Prior {
            stalls: reply.nat()?,
            work: reply.nat()?,
        })
    } else {
        None
    };
    reply.end()?;
    Ok(prior)
}

/// The progress check's verdict at one continuation: the count of
/// continuations in a row that did no new work.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Stall {
    /// The chain goes on.
    Go { stalls: u64 },
    /// The count reached twice the cap: the run ends, not done.
    Stop { stalls: u64 },
    /// The count reached the cap: the run goes on, asked once to change
    /// its approach.
    Steer { stalls: u64 },
}

impl Stall {
    /// The count of continuations in a row with no new work.
    pub(crate) fn stalls(self) -> u64 {
        match self {
            Self::Go { stalls } | Self::Stop { stalls } | Self::Steer { stalls } => stalls,
        }
    }
}

/// The progress check (`check` in `bend/progress.bend`, run by the
/// compiled Bend core; `laws/progress.bend`): the first check (no
/// `prior`) starts the count; new work (the count grew) clears it; else it
/// grows by one: at `cap` the run is steered, at twice `cap` it stops.
/// The counts saturate at the wire's [`NAT_MAX`].
pub(crate) fn stall_check(cap: u64, prior: Option<Prior>, work: u64) -> Stall {
    eukhe_bend::expect_core(Entry::Progress, check(cap, prior, work))
}

fn check(cap: u64, prior: Option<Prior>, work: u64) -> Result<Stall, eukhe_bend::Error> {
    let mut request = Writer::new();
    // The bound of the count of stalls: the wire's largest Nat.
    request.nat(NAT_MAX).nat(cap.min(NAT_MAX));
    match prior {
        None => request.none(),
        Some(prior) => request
            .some()
            .nat(prior.stalls.min(NAT_MAX))
            .nat(prior.work.min(NAT_MAX)),
    };
    request.nat(work.min(NAT_MAX));
    let reply = eukhe_bend::call(Entry::Progress, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let stall = match reply.tag_of(3, "a run check")? {
        0 => Stall::Go {
            stalls: reply.nat()?,
        },
        1 => Stall::Stop {
            stalls: reply.nat()?,
        },
        // `tag_of` answers a tag below 3: this is 2.
        _ => Stall::Steer {
            stalls: reply.nat()?,
        },
    };
    reply.end()?;
    Ok(stall)
}
