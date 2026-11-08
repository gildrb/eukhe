//! The decisions of the cron job store. Per job (`bend/cron_store.bend`,
//! entry `bend/ffi_cron.bend`; `laws/cron.bend` section D2.2,
//! `laws/cron_user.bend`): a claim pass, the verdict on a claim on record,
//! a recovery, the finish step of a run, a cancel, a resume, a user's
//! pause, stop or delete, an edit, a new job, and whether a corrupt file is
//! moved aside. Per file (`bend/cron_file.bend`, entry
//! `bend/ffi_cron_file.bend`; `laws/cron_file.bend`): a claim pass, a
//! recovery and the finish step of a dispatch over every record the store
//! read. Each function encodes the facts the store read, calls the entry
//! and decodes what each record becomes. Times are ms since the epoch.

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

/// How the user holds or ends a job.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Halt {
    /// An active or paused job is paused.
    Pause,
    /// An active or paused job is cancelled.
    Stop,
    /// The job is cancelled, whatever its status.
    Delete,
}

/// An edit of one job.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Edit {
    /// A completed or cancelled job takes no edit.
    Locked,
    /// The job keeps this status and takes this next run.
    Edited { status: Status, next: Option<u64> },
}

/// A new job: its status, first run and failures in a row.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Made {
    pub status: Status,
    pub next: u64,
    pub streak: u32,
}

/// What a corrupt jobs file is read for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Reading {
    /// A read that changes nothing.
    Read,
    /// An update, which writes the file.
    Update,
}

/// A job record of a file: its key (equal keys: equal job ids) and facts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Slot {
    pub key: u64,
    pub fact: Fact,
}

/// A claim record of a file, for a recovery.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Hold {
    /// Read: the key of the job record it names (none: no job record read
    /// has its job id), and whose it is.
    Held { key: Option<u64>, who: Who },
    /// One this build cannot read.
    Unheld,
}

/// A claim record of a file, for the finish step of a dispatch.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Pin {
    /// Read: the key of the job record it names, and whether it is the
    /// dispatch being recorded.
    Pinned { key: Option<u64>, hit: bool },
    /// One this build cannot read.
    Unpinned,
}

/// A recovery of a file: whether each claim record stays, and what each
/// job record becomes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Swept {
    pub keep: Vec<bool>,
    pub jobs: Vec<Back>,
}

/// The finish step of a dispatch: whether each claim record stays, and
/// what each job record becomes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Closed {
    pub keep: Vec<bool>,
    pub jobs: Vec<Finished>,
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

/// Call `entry` on `request` and decode its reply with `decode`.
fn ask<T>(
    entry: Entry,
    request: &mut Writer,
    decode: impl FnOnce(&mut Reader<'_>) -> Result<T, Error>,
) -> Result<T, Error> {
    let reply = call(entry, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let value = decode(&mut reader)?;
    reader.end()?;
    Ok(value)
}

fn get_took(reader: &mut Reader<'_>) -> Result<Took, Error> {
    Ok(match reader.tag_of(3, "a claim pass")? {
        0 => Took::Keep,
        1 => Took::Roll(get_next(reader)?),
        // `tag_of` answers a tag below 3: this is 2.
        _ => Took::Claim(get_next(reader)?),
    })
}

fn get_cut(reader: &mut Reader<'_>) -> Result<Cut, Error> {
    Ok(match reader.tag_of(2, "a cancel")? {
        0 => Cut::Same,
        // `tag_of` answers a tag below 2: this is 1.
        _ => Cut::Cut {
            status: get_status(reader)?,
            next: get_time(reader)?,
        },
    })
}

/// A claim pass at `now` over a job due by `due`; `claimed`: a claim of
/// it is on record.
#[must_use]
pub fn take(fact: &Fact, claimed: bool, due: u64, now: u64) -> Took {
    let mut request = Writer::new();
    request.tag(0);
    put_fact(&mut request, fact);
    request.bool(claimed).nat(time(due)).nat(time(now));
    expect_core(Entry::Cron, ask(Entry::Cron, &mut request, get_took))
}

/// A cancel of a job.
#[must_use]
pub fn cancel(fact: &Fact) -> Cut {
    let mut request = Writer::new();
    request.tag(4);
    put_fact(&mut request, fact);
    expect_core(Entry::Cron, ask(Entry::Cron, &mut request, get_cut))
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
        ask(Entry::Cron, &mut request, |reader| {
            Ok(match reader.tag_of(3, "a resume")? {
                0 => Again::Resumed(get_become(reader)?),
                1 => Again::Ended,
                // `tag_of` answers a tag below 3: this is 2.
                _ => Again::NotRecurring,
            })
        }),
    )
}

/// A pause, stop or delete of a job by the user.
#[must_use]
pub fn halt(fact: &Fact, how: Halt) -> Cut {
    let mut request = Writer::new();
    request.tag(6);
    put_fact(&mut request, fact);
    request.tag(match how {
        Halt::Pause => 0,
        Halt::Stop => 1,
        Halt::Delete => 2,
    });
    expect_core(Entry::Cron, ask(Entry::Cron, &mut request, get_cut))
}

/// An edit of a job; `first`: the first run of a new schedule, if any.
#[must_use]
pub fn edit(fact: &Fact, first: Option<u64>) -> Edit {
    let mut request = Writer::new();
    request.tag(7);
    put_fact(&mut request, fact);
    match first {
        None => request.none(),
        Some(ms) => request.some().nat(time(ms)),
    };
    expect_core(
        Entry::Cron,
        ask(Entry::Cron, &mut request, |reader| {
            Ok(match reader.tag_of(2, "an edit")? {
                0 => Edit::Locked,
                // `tag_of` answers a tag below 2: this is 1.
                _ => Edit::Edited {
                    status: get_status(reader)?,
                    next: get_time(reader)?,
                },
            })
        }),
    )
}

/// A new job whose schedule first runs at `first`.
#[must_use]
pub fn make(first: u64) -> Made {
    let mut request = Writer::new();
    request.tag(8).nat(time(first));
    expect_core(
        Entry::Cron,
        ask(Entry::Cron, &mut request, |reader| {
            let status = get_status(reader)?;
            let next = reader.nat()?;
            let streak = u32::try_from(reader.nat()?).unwrap_or(u32::MAX);
            Ok(Made {
                status,
                next,
                streak,
            })
        }),
    )
}

/// Whether a corrupt jobs file read for `reading` is moved aside.
#[must_use]
pub fn moves_aside(reading: Reading) -> bool {
    let mut request = Writer::new();
    request.tag(9).bool(match reading {
        Reading::Read => false,
        Reading::Update => true,
    });
    expect_core(
        Entry::Cron,
        ask(Entry::Cron, &mut request, |reader| Ok(reader.bool()?)),
    )
}

fn put_slots(request: &mut Writer, slots: &[Slot]) {
    request.count(slots.len());
    for slot in slots {
        request.nat(slot.key);
        put_fact(request, &slot.fact);
    }
}

fn put_key(request: &mut Writer, key: Option<u64>) {
    match key {
        None => request.none(),
        Some(key) => request.some().nat(key),
    };
}

fn get_keeps(reader: &mut Reader<'_>) -> Result<Vec<bool>, Error> {
    let n = reader.count()?;
    (0..n).map(|_| Ok(reader.bool()?)).collect()
}

/// A claim pass over a file at `now`, its jobs due by `due`: what each
/// job record becomes. The store adds one claim record of this process
/// for each job claimed.
#[must_use]
pub fn take_all(slots: &[Slot], claims: &[Option<u64>], due: u64, now: u64) -> Vec<Took> {
    let mut request = Writer::new();
    request.tag(0);
    put_slots(&mut request, slots);
    request.count(claims.len());
    for key in claims {
        put_key(&mut request, *key);
    }
    request.nat(time(due)).nat(time(now));
    expect_core(
        Entry::CronFile,
        ask(Entry::CronFile, &mut request, |reader| {
            let n = reader.count()?;
            (0..n).map(|_| get_took(reader)).collect()
        }),
    )
}

/// A recovery of a file: which claim records stay, and what each job
/// record becomes.
#[must_use]
pub fn recover_all(slots: &[Slot], claims: &[Hold]) -> Swept {
    let mut request = Writer::new();
    request.tag(1);
    put_slots(&mut request, slots);
    request.count(claims.len());
    for claim in claims {
        match claim {
            Hold::Held { key, who } => {
                request.tag(0);
                put_key(&mut request, *key);
                match who {
                    Who::Mine { running } => request.tag(0).bool(*running),
                    Who::Theirs { dead } => request.tag(1).bool(*dead),
                };
            }
            Hold::Unheld => {
                request.tag(1);
            }
        }
    }
    expect_core(
        Entry::CronFile,
        ask(Entry::CronFile, &mut request, |reader| {
            let keep = get_keeps(reader)?;
            let n = reader.count()?;
            let jobs = (0..n)
                .map(|_| {
                    Ok(match reader.tag_of(2, "a recovery")? {
                        0 => Back::Kept,
                        // `tag_of` answers a tag below 2: this is 1.
                        _ => Back::Interrupted {
                            status: get_status(reader)?,
                            next: get_time(reader)?,
                        },
                    })
                })
                .collect::<Result<_, Error>>()?;
            Ok(Swept { keep, jobs })
        }),
    )
}

/// The finish step at `now` of a dispatch whose run `ran` (else it was
/// skipped) and `failed` (or not): which claim records stay, and what
/// each job record becomes.
#[must_use]
pub fn finish_all(slots: &[Slot], claims: &[Pin], ran: bool, failed: bool, now: u64) -> Closed {
    let mut request = Writer::new();
    request.tag(2);
    put_slots(&mut request, slots);
    request.count(claims.len());
    for claim in claims {
        match claim {
            Pin::Pinned { key, hit } => {
                request.tag(0);
                put_key(&mut request, *key);
                request.bool(*hit);
            }
            Pin::Unpinned => {
                request.tag(1);
            }
        }
    }
    request.bool(ran).bool(failed).nat(time(now));
    expect_core(
        Entry::CronFile,
        ask(Entry::CronFile, &mut request, |reader| {
            let keep = get_keeps(reader)?;
            let n = reader.count()?;
            let jobs = (0..n)
                .map(|_| {
                    Ok(match reader.tag_of(3, "a finish step")? {
                        0 => Finished::Untouched,
                        1 => Finished::Ran(get_become(reader)?),
                        // `tag_of` answers a tag below 3: this is 2.
                        _ => Finished::Skipped(get_become(reader)?),
                    })
                })
                .collect::<Result<_, Error>>()?;
            Ok(Closed { keep, jobs })
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
        let paused = Fact {
            status: Status::Paused,
            next: None,
            ..every
        };
        let done = Fact {
            status: Status::Completed,
            ..every
        };
        assert_eq!(
            (
                take(&every, false, 1_000, 1_000),
                cancel(&every),
                resume(&every, 9),
                (
                    halt(&every, Halt::Pause),
                    halt(&done, Halt::Stop),
                    halt(&done, Halt::Delete)
                ),
                (edit(&paused, Some(5_000)), edit(&done, None)),
                make(7_000),
                (moves_aside(Reading::Read), moves_aside(Reading::Update)),
            ),
            (
                Took::Claim(Next::At(601_000)),
                Cut::Cut {
                    status: Status::Cancelled,
                    next: None,
                },
                Again::Resumed(Become {
                    status: Status::Active,
                    next: Next::At(600_009),
                    streak: 0,
                }),
                (
                    Cut::Cut {
                        status: Status::Paused,
                        next: None,
                    },
                    Cut::Same,
                    Cut::Cut {
                        status: Status::Cancelled,
                        next: None,
                    },
                ),
                (
                    Edit::Edited {
                        status: Status::Paused,
                        next: None,
                    },
                    Edit::Locked,
                ),
                Made {
                    status: Status::Active,
                    next: 7_000,
                    streak: 0,
                },
                (false, true),
            )
        );
    }

    /// The passes over a file come from the compiled core: a claim pass
    /// rolls the job a claim record names and claims the other; a recovery
    /// clears a dead owner's record, keeps a live one's and one it cannot
    /// read, and interrupts the job it cleared; a finish step drops the
    /// dispatch's record and counts the failed run of the job it names.
    #[test]
    fn the_cron_file_passes_come_from_the_compiled_core() {
        let every = Fact {
            status: Status::Active,
            plan: Plan::Every(600_000),
            next: Some(1_000),
            streak: 3,
        };
        let slots = [
            Slot {
                key: 0,
                fact: every,
            },
            Slot {
                key: 1,
                fact: every,
            },
        ];
        assert_eq!(
            (
                take_all(&slots, &[Some(1)], 1_000, 1_000),
                recover_all(
                    &slots,
                    &[
                        Hold::Held {
                            key: Some(0),
                            who: Who::Theirs { dead: true },
                        },
                        Hold::Held {
                            key: Some(1),
                            who: Who::Theirs { dead: false },
                        },
                        Hold::Unheld,
                    ],
                ),
                finish_all(
                    &slots,
                    &[
                        Pin::Pinned {
                            key: Some(0),
                            hit: false,
                        },
                        Pin::Pinned {
                            key: Some(1),
                            hit: true,
                        },
                    ],
                    true,
                    true,
                    5_000,
                ),
            ),
            (
                vec![
                    Took::Claim(Next::At(601_000)),
                    Took::Roll(Next::At(601_000))
                ],
                Swept {
                    keep: vec![false, true, true],
                    jobs: vec![
                        Back::Interrupted {
                            status: Status::Active,
                            next: Some(1_000),
                        },
                        Back::Kept,
                    ],
                },
                Closed {
                    keep: vec![true, false],
                    jobs: vec![
                        Finished::Untouched,
                        Finished::Ran(Become {
                            status: Status::Active,
                            next: Next::At(965_000),
                            streak: 4,
                        }),
                    ],
                },
            )
        );
    }
}
