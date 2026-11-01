//! The cron job store's updates (`bend/cron_serve.bend`, stepper entry
//! `bend/ffi_cron_serve.bend`; laws `laws/cron_serve/`). The store is an
//! event loop with no policy: under a jobs file's lock it reads the file,
//! numbers what the decisions compare, and asks [`Runs::serve`] what the
//! whole new file is: which records change and how (the per-job decisions
//! of `bend/cron_store.bend`), which claims go and which are made, whether
//! an unreadable file moves aside first and whether anything is written.
//! The stepper's state is the process's runs: the dispatch ids it runs
//! now; a claim adds the dispatches it makes, a finish of its own run or
//! [`Runs::end`] removes one. Times are ms since the epoch.

use crate::wire::{Reader, WireError, Writer, NAT_MAX};
use crate::{call, expect_core, Entry, Stepper};

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
    /// The schedule rule's next match after the update's clock: the store
    /// evaluates the rule.
    Roll,
}

/// A claim pass on one job.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Took {
    /// Not due: nothing changes.
    Keep,
    /// Due with a claim on record: only its next run rolls.
    Roll(Next),
    /// Due with no claim on record: claimed; its next run rolls.
    Claim(Next),
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

/// A job record of the file, in file order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum JobRec {
    /// One this build reads: its id (the store's number for it) and facts.
    Known { id: u64, fact: Fact },
    /// One this build cannot read.
    Raw,
}

/// A claim record of the file, in file order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ClaimRec<'a> {
    /// One this build reads: its dispatch id, its job's id and its owner
    /// (the store's numbers for them).
    Known {
        dispatch: &'a str,
        job: u64,
        owner: u64,
    },
    /// One this build cannot read.
    Raw,
}

/// The jobs file as an update reads it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Disk<'a> {
    Missing,
    /// There, but it cannot be read or parsed.
    Torn,
    Parsed {
        jobs: &'a [JobRec],
        claims: &'a [ClaimRec<'a>],
    },
}

/// An update, with the facts the store gathered for it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Op<'a> {
    /// A claim pass at `now` over the jobs due by `due`; `fresh`: dispatch
    /// ids to use, in order (one per job record is enough).
    Claim {
        due: u64,
        now: u64,
        fresh: &'a [String],
    },
    /// A recovery; `dead`: the claim owners on record that are dead.
    Recover {
        dead: &'a [u64],
    },
    /// The finish of the run of `dispatch`.
    Finish {
        dispatch: &'a str,
        ran: bool,
        failed: bool,
        now: u64,
    },
    Cancel {
        job: u64,
    },
    Resume {
        job: u64,
        now: u64,
    },
    /// A new job record with the fresh id `job`, last in the file.
    Create {
        job: u64,
        fact: Fact,
    },
}

/// What a job record becomes, in file order (a new one last).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum JobOut {
    /// Kept as read.
    Same,
    Took(Took),
    Back(Back),
    Finished(Finished),
    Cut(Cut),
    Again(Again),
    /// The created job.
    New,
}

/// What a claim record becomes, in file order (new ones last).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ClaimOut {
    Keep,
    Drop,
    /// A claim of the job record at position `at`, owned by this process.
    New {
        at: usize,
        dispatch: String,
    },
}

/// The whole new file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Served {
    /// Move the unreadable file aside first.
    pub aside: bool,
    /// Write the records (else leave the file as it is).
    pub write: bool,
    pub jobs: Vec<JobOut>,
    pub claims: Vec<ClaimOut>,
}

/// The runs of one process, kept in the compiled core: the dispatch ids
/// it runs now.
#[derive(Debug)]
pub struct Runs {
    stepper: Stepper,
}

impl Default for Runs {
    fn default() -> Self {
        Self::new()
    }
}

impl Runs {
    /// No runs.
    #[must_use]
    pub fn new() -> Self {
        let (stepper, reply) = expect_core(Entry::CronServe, Stepper::open(Entry::CronServe, ""));
        expect_core(
            Entry::CronServe,
            Reader::reply(&reply).and_then(Reader::end),
        );
        Runs { stepper }
    }

    /// The update `op` of the file `disk` by the process numbered `me`.
    pub fn serve(&mut self, me: u64, disk: &Disk<'_>, op: &Op<'_>) -> Served {
        let mut event = Writer::new();
        event.tag(0).nat(me);
        put_disk(&mut event, disk);
        put_op(&mut event, op);
        let event = expect_core(Entry::CronServe, event.finish());
        let reply = expect_core(Entry::CronServe, self.stepper.step(&event));
        expect_core(Entry::CronServe, read_served(&reply))
    }

    /// The run of `dispatch` ended (its guard dropped).
    pub fn end(&mut self, dispatch: &str) {
        let event = expect_core(
            Entry::CronServe,
            Writer::new().tag(1).str(dispatch).finish(),
        );
        let reply = expect_core(Entry::CronServe, self.stepper.step(&event));
        expect_core(
            Entry::CronServe,
            Reader::reply(&reply).and_then(Reader::end),
        );
    }
}

/// Whether a job is due at `now`: a claim pass at `now` would claim it or
/// roll its next run.
#[must_use]
pub fn due(fact: &Fact, now: u64) -> bool {
    let mut question = Writer::new();
    question.nat(time(now));
    put_fact(&mut question, fact);
    let question = expect_core(Entry::CronServe, question.finish());
    let reply = expect_core(Entry::CronServe, call(Entry::CronServe, &question));
    expect_core(
        Entry::CronServe,
        Reader::reply(&reply).and_then(|mut r| {
            let due = r.bool()?;
            r.end()?;
            Ok(due)
        }),
    )
}

fn time(ms: u64) -> u64 {
    ms.min(TIME_MAX)
}

fn put_fact(w: &mut Writer, fact: &Fact) {
    w.tag(match fact.status {
        Status::Active => 0,
        Status::Paused => 1,
        Status::Completed => 2,
        Status::Cancelled => 3,
    });
    match fact.plan {
        Plan::Once => w.tag(0),
        Plan::Every(ms) => w.tag(1).nat(time(ms)),
        Plan::Rule => w.tag(2),
    };
    match fact.next {
        None => w.none(),
        Some(ms) => w.some().nat(time(ms)),
    };
    w.nat(u64::from(fact.streak));
}

fn put_disk(w: &mut Writer, disk: &Disk<'_>) {
    match disk {
        Disk::Missing => {
            w.tag(0);
        }
        Disk::Torn => {
            w.tag(1);
        }
        Disk::Parsed { jobs, claims } => {
            w.tag(2).count(jobs.len());
            for job in *jobs {
                match job {
                    JobRec::Known { id, fact } => {
                        w.tag(0).nat(*id);
                        put_fact(w, fact);
                    }
                    JobRec::Raw => {
                        w.tag(1);
                    }
                }
            }
            w.count(claims.len());
            for claim in *claims {
                match claim {
                    ClaimRec::Known {
                        dispatch,
                        job,
                        owner,
                    } => {
                        w.tag(0).str(dispatch).nat(*job).nat(*owner);
                    }
                    ClaimRec::Raw => {
                        w.tag(1);
                    }
                }
            }
        }
    }
}

fn put_op(w: &mut Writer, op: &Op<'_>) {
    match op {
        Op::Claim { due, now, fresh } => {
            w.tag(0).nat(time(*due)).nat(time(*now)).count(fresh.len());
            for dispatch in *fresh {
                w.str(dispatch);
            }
        }
        Op::Recover { dead } => {
            w.tag(1).count(dead.len());
            for owner in *dead {
                w.nat(*owner);
            }
        }
        Op::Finish {
            dispatch,
            ran,
            failed,
            now,
        } => {
            w.tag(2)
                .str(dispatch)
                .bool(*ran)
                .bool(*failed)
                .nat(time(*now));
        }
        Op::Cancel { job } => {
            w.tag(3).nat(*job);
        }
        Op::Resume { job, now } => {
            w.tag(4).nat(*job).nat(time(*now));
        }
        Op::Create { job, fact } => {
            w.tag(5).nat(*job);
            put_fact(w, fact);
        }
    }
}

fn get_status(r: &mut Reader<'_>) -> Result<Status, WireError> {
    Ok(match r.tag_of(4, "a cron job status")? {
        0 => Status::Active,
        1 => Status::Paused,
        2 => Status::Completed,
        // `tag_of` answers a tag below 4: this is 3.
        _ => Status::Cancelled,
    })
}

fn get_time(r: &mut Reader<'_>) -> Result<Option<u64>, WireError> {
    Ok(if r.maybe()? { Some(r.nat()?) } else { None })
}

fn get_next(r: &mut Reader<'_>) -> Result<Next, WireError> {
    Ok(match r.tag_of(3, "a cron next run")? {
        0 => Next::None,
        1 => Next::At(r.nat()?),
        // `tag_of` answers a tag below 3: this is 2.
        _ => Next::Roll,
    })
}

fn get_become(r: &mut Reader<'_>) -> Result<Become, WireError> {
    let status = get_status(r)?;
    let next = get_next(r)?;
    let streak = u32::try_from(r.nat()?).unwrap_or(u32::MAX);
    Ok(Become {
        status,
        next,
        streak,
    })
}

fn get_job_out(r: &mut Reader<'_>) -> Result<JobOut, WireError> {
    Ok(match r.tag_of(7, "a job record's answer")? {
        0 => JobOut::Same,
        1 => JobOut::Took(match r.tag_of(3, "a claim pass")? {
            0 => Took::Keep,
            1 => Took::Roll(get_next(r)?),
            // `tag_of` answers a tag below 3: this is 2.
            _ => Took::Claim(get_next(r)?),
        }),
        2 => JobOut::Back(match r.tag_of(2, "a recovery")? {
            0 => Back::Kept,
            // `tag_of` answers a tag below 2: this is 1.
            _ => Back::Interrupted {
                status: get_status(r)?,
                next: get_time(r)?,
            },
        }),
        3 => JobOut::Finished(match r.tag_of(3, "a finish step")? {
            0 => Finished::Untouched,
            1 => Finished::Ran(get_become(r)?),
            // `tag_of` answers a tag below 3: this is 2.
            _ => Finished::Skipped(get_become(r)?),
        }),
        4 => JobOut::Cut(match r.tag_of(2, "a cancel")? {
            0 => Cut::Same,
            // `tag_of` answers a tag below 2: this is 1.
            _ => Cut::Cut {
                status: get_status(r)?,
                next: get_time(r)?,
            },
        }),
        5 => JobOut::Again(match r.tag_of(3, "a resume")? {
            0 => Again::Resumed(get_become(r)?),
            1 => Again::Ended,
            // `tag_of` answers a tag below 3: this is 2.
            _ => Again::NotRecurring,
        }),
        // `tag_of` answers a tag below 7: this is 6.
        _ => JobOut::New,
    })
}

fn get_claim_out(r: &mut Reader<'_>) -> Result<ClaimOut, WireError> {
    Ok(match r.tag_of(3, "a claim record's answer")? {
        0 => ClaimOut::Keep,
        1 => ClaimOut::Drop,
        // `tag_of` answers a tag below 3: this is 2.
        _ => {
            let at = r.count()?;
            ClaimOut::New {
                at,
                dispatch: r.str()?.to_string(),
            }
        }
    })
}

fn read_served(reply: &str) -> Result<Served, WireError> {
    let mut r = Reader::reply(reply)?;
    let aside = r.bool()?;
    let write = r.bool()?;
    let count = r.count()?;
    let mut jobs = Vec::with_capacity(count);
    for _ in 0..count {
        jobs.push(get_job_out(&mut r)?);
    }
    let count = r.count()?;
    let mut claims = Vec::with_capacity(count);
    for _ in 0..count {
        claims.push(get_claim_out(&mut r)?);
    }
    r.end()?;
    Ok(Served {
        aside,
        write,
        jobs,
        claims,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const EVERY: Fact = Fact {
        status: Status::Active,
        plan: Plan::Every(600_000),
        next: Some(1_000),
        streak: 0,
    };

    /// The compiled core is reached: a claim pass claims the due job with
    /// no claim and rolls the one with a claim, keeping the record it
    /// cannot read in place; the finish of the claimed run settles it; a
    /// finish of a dispatch this process does not run changes nothing
    /// (the rule itself is pinned by `laws/cron_serve/`).
    #[test]
    fn the_cron_store_updates_run_in_the_core() {
        let mut runs = Runs::new();
        let jobs = [
            JobRec::Known { id: 0, fact: EVERY },
            JobRec::Raw,
            JobRec::Known { id: 1, fact: EVERY },
        ];
        let claims = [ClaimRec::Known {
            dispatch: "theirs",
            job: 1,
            owner: 1,
        }];
        let fresh = ["mine".to_string(), "spare".to_string()];
        let disk = Disk::Parsed {
            jobs: &jobs,
            claims: &claims,
        };
        let claimed = runs.serve(
            0,
            &disk,
            &Op::Claim {
                due: 1_000,
                now: 1_000,
                fresh: &fresh,
            },
        );
        let after = [ClaimRec::Known {
            dispatch: "mine",
            job: 0,
            owner: 0,
        }];
        let finish = |dispatch| Op::Finish {
            dispatch,
            ran: true,
            failed: false,
            now: 2_000,
        };
        let disk = Disk::Parsed {
            jobs: &jobs[..1],
            claims: &after,
        };
        let stranger = runs.serve(0, &disk, &finish("theirs"));
        let settled = runs.serve(0, &disk, &finish("mine"));
        assert_eq!(
            (claimed, stranger, settled),
            (
                Served {
                    aside: false,
                    write: true,
                    jobs: vec![
                        JobOut::Took(Took::Claim(Next::At(601_000))),
                        JobOut::Same,
                        JobOut::Took(Took::Roll(Next::At(601_000))),
                    ],
                    claims: vec![
                        ClaimOut::Keep,
                        ClaimOut::New {
                            at: 0,
                            dispatch: "mine".to_string(),
                        },
                    ],
                },
                Served {
                    aside: false,
                    write: false,
                    jobs: vec![JobOut::Same],
                    claims: vec![ClaimOut::Keep],
                },
                Served {
                    aside: false,
                    write: true,
                    jobs: vec![JobOut::Finished(Finished::Ran(Become {
                        status: Status::Active,
                        next: Next::At(1_000),
                        streak: 0,
                    }))],
                    claims: vec![ClaimOut::Drop],
                },
            )
        );
    }
}
