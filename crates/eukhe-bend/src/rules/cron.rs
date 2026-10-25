//! The per-job decisions of the cron job store (`bend/cron_store.bend`,
//! entry `bend/ffi_cron.bend`; `laws/cron.bend` section D2.2): a claim
//! pass, the verdict on a claim on record, a recovery, the finish step of
//! a run, a cancel and a resume. Each function encodes the facts the store
//! read of one job, calls [`Entry::Cron`] and decodes what the job becomes.
//! Times are ms since the epoch.

use crate::wire::{Reader, Writer, NAT_MAX};
use crate::{call, expect_core, Entry, Error};

/// The largest time the store encodes: half the wire's largest Nat, so
/// that a time plus an interval or a pause still fits the reply. A later
/// time (past the year 3500) is encoded as this one.
const TIME_MAX: u64 = NAT_MAX / 2;

/// A job's status.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Status {
    Active,
    Paused,
    Completed,
    Cancelled,
}

/// A job's schedule as the store keeps it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Plan {
    /// A one-shot.
    Once,
    /// An interval of this many ms (more than 0).
    Every(u64),
    /// A rule the store evaluates: a cron expression, or an interval
    /// schedule with no valid interval.
    Rule,
}

/// What the store read of a job.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fact {
    pub status: Status,
    pub plan: Plan,
    /// The next run, when the record names one the store can read.
    pub next: Option<u64>,
    /// Failed runs in a row.
    pub streak: u32,
}

/// A next run the core answers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Next {
    None,
    At(u64),
    /// The schedule rule's next match after the decision's clock: the
    /// store evaluates the rule.
    Roll,
}

/// A claim pass on one job.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Took {
    /// Not due: nothing changes.
    Keep,
    /// Due with a claim on record: only its next run rolls.
    Roll(Next),
    /// Due with no claim on record: claim it; its next run rolls.
    Claim(Next),
}

/// Whose claim is on record.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Who {
    /// This process's, and whether this process still runs it.
    Mine { running: bool },
    /// Another process's, and whether that process is dead.
    Theirs { dead: bool },
}

/// A recovery of one job.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Back {
    Kept,
    /// The job records the interruption of its run with this status and
    /// next run.
    Interrupted {
        status: Status,
        next: Option<u64>,
    },
}

/// What a job becomes: its status, next run and failures in a row.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Become {
    pub status: Status,
    pub next: Next,
    pub streak: u32,
}

/// The finish step of a run of one job.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Finished {
    /// The job is not active: only its claim goes.
    Untouched,
    /// The job counts a run.
    Ran(Become),
    /// The job counts a skip.
    Skipped(Become),
}

/// A cancel of one job.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cut {
    /// Already cancelled.
    Same,
    Cut {
        status: Status,
        next: Option<u64>,
    },
}

/// A resume of one job.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Again {
    Resumed(Become),
    /// A completed or cancelled job: nothing to resume.
    Ended,
    /// A one-shot.
    NotRecurring,
}

fn time(ms: u64) -> u64 {
    ms.min(TIME_MAX)
}

fn put_fact(request: &mut Writer, fact: &Fact) {
    request.tag(match fact.status {
        Status::Active => 0,
        Status::Paused => 1,
        Status::Completed => 2,
        Status::Cancelled => 3,
    });
    match fact.plan {
        Plan::Once => request.tag(0),
        Plan::Every(ms) => request.tag(1).nat(time(ms)),
        Plan::Rule => request.tag(2),
    };
    match fact.next {
        None => request.none(),
        Some(ms) => request.some().nat(time(ms)),
    };
    request.nat(u64::from(fact.streak));
}

fn get_status(reader: &mut Reader<'_>) -> Result<Status, Error> {
    Ok(match reader.tag_of(4, "a cron job status")? {
        0 => Status::Active,
        1 => Status::Paused,
        2 => Status::Completed,
        // `tag_of` answers a tag below 4: this is 3.
        _ => Status::Cancelled,
    })
}

fn get_time(reader: &mut Reader<'_>) -> Result<Option<u64>, Error> {
    Ok(if reader.maybe()? {
        Some(reader.nat()?)
    } else {
        None
    })
}

fn get_next(reader: &mut Reader<'_>) -> Result<Next, Error> {
    Ok(match reader.tag_of(3, "a cron next run")? {
        0 => Next::None,
        1 => Next::At(reader.nat()?),
        // `tag_of` answers a tag below 3: this is 2.
        _ => Next::Roll,
    })
}

fn get_become(reader: &mut Reader<'_>) -> Result<Become, Error> {
    let status = get_status(reader)?;
    let next = get_next(reader)?;
    let streak = u32::try_from(reader.nat()?).unwrap_or(u32::MAX);
    Ok(Become {
        status,
        next,
        streak,
    })
}

/// Call the core on `request` and decode its reply with `decode`.
fn ask<T>(
    request: &mut Writer,
    decode: impl FnOnce(&mut Reader<'_>) -> Result<T, Error>,
) -> Result<T, Error> {
    let reply = call(Entry::Cron, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let value = decode(&mut reader)?;
    reader.end()?;
    Ok(value)
}

/// A claim pass at `now` over a job due by `due`; `claimed`: a claim of
/// it is on record.
#[must_use]
pub fn take(fact: &Fact, claimed: bool, due: u64, now: u64) -> Took {
    let mut request = Writer::new();
    request.tag(0);
    put_fact(&mut request, fact);
    request.bool(claimed).nat(time(due)).nat(time(now));
    expect_core(
        Entry::Cron,
        ask(&mut request, |reader| {
            Ok(match reader.tag_of(3, "a claim pass")? {
                0 => Took::Keep,
                1 => Took::Roll(get_next(reader)?),
                // `tag_of` answers a tag below 3: this is 2.
                _ => Took::Claim(get_next(reader)?),
            })
        }),
    )
}

/// Whether a recovery clears a claim on record of `who`.
#[must_use]
pub fn clear(who: Who) -> bool {
    let mut request = Writer::new();
    request.tag(1);
    match who {
        Who::Mine { running } => request.tag(0).bool(running),
        Who::Theirs { dead } => request.tag(1).bool(dead),
    };
    expect_core(Entry::Cron, ask(&mut request, |reader| Ok(reader.bool()?)))
}

/// A recovery of a job; `cleared`: a claim of it was cleared.
#[must_use]
pub fn recover(fact: &Fact, cleared: bool) -> Back {
    let mut request = Writer::new();
    request.tag(2);
    put_fact(&mut request, fact);
    request.bool(cleared);
    expect_core(
        Entry::Cron,
        ask(&mut request, |reader| {
            Ok(match reader.tag_of(2, "a recovery")? {
                0 => Back::Kept,
                // `tag_of` answers a tag below 2: this is 1.
                _ => Back::Interrupted {
                    status: get_status(reader)?,
                    next: get_time(reader)?,
                },
            })
        }),
    )
}

/// The finish step at `now` of a run of a job that `ran` (else it was
/// skipped) and `failed` (or not).
#[must_use]
pub fn finish(fact: &Fact, ran: bool, failed: bool, now: u64) -> Finished {
    let mut request = Writer::new();
    request.tag(3);
    put_fact(&mut request, fact);
    request.bool(ran).bool(failed).nat(time(now));
    expect_core(
        Entry::Cron,
        ask(&mut request, |reader| {
            Ok(match reader.tag_of(3, "a finish step")? {
                0 => Finished::Untouched,
                1 => Finished::Ran(get_become(reader)?),
                // `tag_of` answers a tag below 3: this is 2.
                _ => Finished::Skipped(get_become(reader)?),
            })
        }),
    )
}

/// A cancel of a job.
#[must_use]
pub fn cancel(fact: &Fact) -> Cut {
    let mut request = Writer::new();
    request.tag(4);
    put_fact(&mut request, fact);
    expect_core(
        Entry::Cron,
        ask(&mut request, |reader| {
            Ok(match reader.tag_of(2, "a cancel")? {
                0 => Cut::Same,
                // `tag_of` answers a tag below 2: this is 1.
                _ => Cut::Cut {
                    status: get_status(reader)?,
                    next: get_time(reader)?,
                },
            })
        }),
    )
}

/// A resume of a job at `now`.
#[must_use]
pub fn resume(fact: &Fact, now: u64) -> Again {
    let mut request = Writer::new();
    request.tag(5);
    put_fact(&mut request, fact);
    request.nat(time(now));
    expect_core(
        Entry::Cron,
        ask(&mut request, |reader| {
            Ok(match reader.tag_of(3, "a resume")? {
                0 => Again::Resumed(get_become(reader)?),
                1 => Again::Ended,
                // `tag_of` answers a tag below 3: this is 2.
                _ => Again::NotRecurring,
            })
        }),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every decision comes from the compiled core.
    #[test]
    fn the_cron_decisions_come_from_the_compiled_core() {
        let every = Fact {
            status: Status::Active,
            plan: Plan::Every(600_000),
            next: Some(1_000),
            streak: 3,
        };
        assert_eq!(
            (
                take(&every, false, 1_000, 1_000),
                clear(Who::Theirs { dead: false }),
                recover(&every, true),
                finish(&every, true, true, 5_000),
                cancel(&every),
                resume(&every, 9),
            ),
            (
                Took::Claim(Next::At(601_000)),
                false,
                Back::Interrupted {
                    status: Status::Active,
                    next: Some(1_000),
                },
                Finished::Ran(Become {
                    status: Status::Active,
                    next: Next::At(965_000),
                    streak: 4,
                }),
                Cut::Cut {
                    status: Status::Cancelled,
                    next: None,
                },
                Again::Resumed(Become {
                    status: Status::Active,
                    next: Next::At(600_009),
                    streak: 0,
                }),
            )
        );
    }
}
