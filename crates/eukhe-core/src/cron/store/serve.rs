//! The updates of the jobs files the compiled core decides
//! (`bend/cron_serve.bend`; laws `laws/cron_serve/`): a claim pass, a
//! recovery, the finish of a run, a cancel, a resume, a new job. The store
//! is an event loop with no policy: under the files' locks it reads each
//! file, numbers the job ids and claim owners it holds (by first
//! appearance; this process is owner 0), draws the fresh dispatch ids,
//! probes the other owners on record for a recovery, and asks the core
//! what the whole new file is. Then it does what the answer says: moves an
//! unreadable file aside, renders each record as the answer gives it (in
//! the answer's order: a record it cannot read stays as it is, where it
//! is), and writes the file only when the answer says so.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use anyhow::Context as _;
use eukhe_bend::rules::cron::{
    Again, Back, ClaimOut, ClaimRec, Cut, Disk, Finished, JobOut, JobRec, Op, Took,
};
use eukhe_types::platform::process::ProcessIdentity;
use uuid::Uuid;

use super::facts::{fact_of, job_status, next_text, next_text_at};
use super::state::{move_aside, read_state_file, with_state_locks, write_jobs_state, StateFile};
use super::{
    iso_from_millis, AgentCronDispatch, AgentCronDispatchRecord, AgentCronJob, AgentCronJobStore,
    CronJobsState, DispatchOutcome, DispatchResultOptions, Record,
};

/// What a recovery writes on a job whose run it interrupted.
const INTERRUPTED: &str = "Interrupted before scheduled operation completion";

/// One update of the store, with the times it runs at.
pub(crate) enum Update<'a> {
    /// A claim pass at `now` over the jobs due by `due`.
    Claim {
        due: u64,
        now: u64,
    },
    Recover {
        now: u64,
    },
    /// The finish of this process's run of `dispatch`.
    Finish {
        dispatch: &'a str,
        result: &'a DispatchResultOptions,
        now: u64,
    },
    Cancel {
        id: &'a str,
        now: u64,
    },
    /// A resume of job `id`, after `edit` (when given) made its field edits
    /// on the jobs as read, under the same lock.
    Resume {
        id: &'a str,
        now: u64,
        edit: Option<&'a Edit<'a>>,
    },
    /// A new job, written last in its file.
    Create {
        job: &'a AgentCronJob,
    },
}

/// Field edits made on each job record as read before a resume: `None`
/// leaves the job as it is, an error refuses the whole update (nothing is
/// written).
pub(crate) type Edit<'a> = dyn Fn(&AgentCronJob) -> anyhow::Result<Option<AgentCronJob>> + 'a;

/// A job record the update changed (or answered on), as written.
pub(crate) struct Answered {
    pub(crate) out: JobOut,
    pub(crate) job: AgentCronJob,
}

/// What an update did to the store's files.
#[derive(Default)]
pub(crate) struct Settled {
    /// Every job record the core answered on (not kept as read), in file
    /// order, file after file.
    pub(crate) answered: Vec<Answered>,
    /// The dispatches a claim pass made.
    pub(crate) claimed: Vec<AgentCronDispatch>,
}

/// The numbers the core compares: job ids and claim owners, by first
/// appearance; this process is owner 0.
struct Numbers<'a> {
    ids: HashMap<&'a str, u64>,
    owners: Vec<&'a ProcessIdentity>,
}

impl<'a> Numbers<'a> {
    fn job(&mut self, id: &'a str) -> u64 {
        let next = self.ids.len() as u64;
        *self.ids.entry(id).or_insert(next)
    }

    fn owner(&mut self, owner: &'a ProcessIdentity) -> u64 {
        if let Some(at) = self.owners.iter().position(|known| *known == owner) {
            return at as u64;
        }
        self.owners.push(owner);
        (self.owners.len() - 1) as u64
    }
}

/// What a resume of one job did.
pub(crate) enum Resumed {
    /// The job runs again, as written.
    Job(Box<AgentCronJob>),
    /// A completed or cancelled job: nothing to resume.
    Ended,
    /// A one-shot.
    NotRecurring,
    /// No job has the id.
    Missing,
}

impl AgentCronJobStore {
    /// The files `update` runs on: every file of the store, or the one of
    /// a new job's session.
    fn update_paths(&self, update: &Update<'_>) -> anyhow::Result<Vec<PathBuf>> {
        if !self.session_artifact_mode {
            return Ok(vec![self.require_file_path()]);
        }
        let files = self
            .session_artifact_files
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        Ok(match update {
            Update::Create { job } => {
                vec![files.get(&job.session_id).cloned().with_context(|| {
                    format!(
                        "cron job session artifact not registered: {}",
                        job.session_id
                    )
                })?]
            }
            Update::Claim { .. }
            | Update::Recover { .. }
            | Update::Finish { .. }
            | Update::Cancel { .. }
            | Update::Resume { .. } => files.values().cloned().collect(),
        })
    }

    /// Run `update` on the store's files, under their locks, as the
    /// compiled core decides it.
    ///
    /// # Errors
    ///
    /// Returns an error when a lock is not acquired, an unreadable file
    /// cannot be moved aside, a rule schedule a resume rolls is invalid, or
    /// a write fails.
    pub(crate) fn update(&self, update: &Update<'_>) -> anyhow::Result<Settled> {
        let paths = self.update_paths(update)?;
        let previous_heartbeats = Self::heartbeat_catalog_signature(&self.read_jobs());
        let mut written = false;
        let settled = with_state_locks(&paths, || {
            let mut settled = Settled::default();
            for path in &paths {
                written |= self.update_file(path, update, &mut settled)?;
            }
            Ok::<_, anyhow::Error>(settled)
        })
        .ok_or_else(|| anyhow::anyhow!("cron jobs state lock not acquired; skipped"))??;
        if written && Self::heartbeat_catalog_signature(&self.read_jobs()) != previous_heartbeats {
            self.notify_heartbeat_change();
        }
        Ok(settled)
    }

    /// Resume the job `id` at `now`, as the compiled core decides it: an
    /// active or paused repeating job is active again, its next run its
    /// schedule's after `now`, its failures in a row forgotten.
    ///
    /// # Errors
    ///
    /// Returns an error when a lock is not acquired, the job's rule
    /// schedule is invalid, or a write fails.
    pub(crate) fn resume(&self, id: &str, now: u64) -> anyhow::Result<Resumed> {
        self.resume_with(id, now, None)
    }

    /// Resume the job `id` at `now` after `edit` made its field edits on the
    /// jobs as read, in one update under the file's lock, written once (when
    /// the edits or the resume change it). No job edited: nothing is
    /// resumed. A rule schedule that cannot be evaluated leaves the resumed
    /// job with no next run.
    ///
    /// # Errors
    ///
    /// Returns an error when a lock is not acquired, `edit` refuses, or a
    /// write fails.
    pub(crate) fn resume_edited(
        &self,
        id: &str,
        now: u64,
        edit: &Edit<'_>,
    ) -> anyhow::Result<Resumed> {
        self.resume_with(id, now, Some(edit))
    }

    fn resume_with(&self, id: &str, now: u64, edit: Option<&Edit<'_>>) -> anyhow::Result<Resumed> {
        let settled = self.update(&Update::Resume { id, now, edit })?;
        let again = settled
            .answered
            .into_iter()
            .find_map(|answered| match answered.out {
                JobOut::Again(again) => Some((again, answered.job)),
                JobOut::Same
                | JobOut::Took(_)
                | JobOut::Back(_)
                | JobOut::Finished(_)
                | JobOut::Cut(_)
                | JobOut::New => None,
            });
        Ok(match again {
            Some((Again::Resumed(_), job)) => Resumed::Job(Box::new(job)),
            Some((Again::Ended, _)) => Resumed::Ended,
            Some((Again::NotRecurring, _)) => Resumed::NotRecurring,
            None => Resumed::Missing,
        })
    }

    /// One file: read, served, moved aside and written as the core says;
    /// whether it was written.
    fn update_file(
        &self,
        path: &Path,
        update: &Update<'_>,
        settled: &mut Settled,
    ) -> anyhow::Result<bool> {
        let file = read_state_file(path);
        let empty = CronJobsState::default();
        let (state, torn) = match &file {
            StateFile::Missing => (&empty, None),
            StateFile::Read(state) => (state, None),
            StateFile::Corrupt(reason) => (&empty, Some(reason.as_str())),
        };
        let edited_state;
        let mut edited = false;
        let state = match update {
            Update::Resume {
                edit: Some(edit), ..
            } => {
                let mut next = state.clone();
                for record in &mut next.jobs {
                    if let Record::Read(job) = record {
                        if let Some(changed) = edit(job)? {
                            *job = changed;
                            edited = true;
                        }
                    }
                }
                if !edited {
                    return Ok(false);
                }
                edited_state = next;
                &edited_state
            }
            _ => state,
        };
        let me = self.owner.identity();
        let mut numbers = Numbers {
            ids: HashMap::new(),
            owners: vec![me],
        };
        let jobs: Vec<JobRec> = state
            .jobs
            .iter()
            .map(|record| match record {
                Record::Read(job) => JobRec::Known {
                    id: numbers.job(&job.id),
                    fact: fact_of(job),
                },
                Record::Unread(_) => JobRec::Raw,
            })
            .collect();
        let claims: Vec<ClaimRec<'_>> = state
            .dispatches
            .iter()
            .map(|record| match record {
                Record::Read(claim) => ClaimRec::Known {
                    dispatch: &claim.id,
                    job: numbers.job(&claim.job_id),
                    owner: numbers.owner(&claim.owner),
                },
                Record::Unread(_) => ClaimRec::Raw,
            })
            .collect();
        let disk = match &file {
            StateFile::Missing => Disk::Missing,
            StateFile::Corrupt(_) => Disk::Torn,
            StateFile::Read(_) => Disk::Parsed {
                jobs: &jobs,
                claims: &claims,
            },
        };
        let fresh: Vec<String>;
        let dead: Vec<u64>;
        let op = match *update {
            Update::Claim { due, now } => {
                fresh = jobs.iter().map(|_| Uuid::new_v4().to_string()).collect();
                Op::Claim {
                    due,
                    now,
                    fresh: &fresh,
                }
            }
            Update::Recover { .. } => {
                dead = (1..numbers.owners.len())
                    .filter(|&at| !self.owner.is_alive(numbers.owners[at]))
                    .map(|at| at as u64)
                    .collect();
                Op::Recover { dead: &dead }
            }
            Update::Finish {
                dispatch,
                result,
                now,
            } => Op::Finish {
                dispatch,
                ran: result.outcome == DispatchOutcome::Ran,
                failed: result.error.is_some(),
                now,
            },
            Update::Cancel { id, .. } => Op::Cancel {
                job: numbers.job(id),
            },
            Update::Resume { id, now, .. } => Op::Resume {
                job: numbers.job(id),
                now,
            },
            Update::Create { job } => Op::Create {
                job: numbers.job(&job.id),
                fact: fact_of(job),
            },
        };
        let served = self.owner.serve(0, &disk, &op);
        if served.aside {
            move_aside(path, torn.unwrap_or("is unreadable"))?;
        }
        let next = render(state, &served, update, me, settled)?;
        let write = served.write || edited;
        if write {
            write_jobs_state(path, &next)?;
        }
        Ok(write)
    }
}

/// The new file the core answered, rendered from the file as read.
fn render(
    state: &CronJobsState,
    served: &eukhe_bend::rules::cron::Served,
    update: &Update<'_>,
    me: &ProcessIdentity,
    settled: &mut Settled,
) -> anyhow::Result<CronJobsState> {
    let inconsistent = || anyhow::anyhow!("the compiled core answered another cron jobs file");
    let mut jobs = Vec::with_capacity(served.jobs.len());
    for (at, out) in served.jobs.iter().enumerate() {
        let record = match (out, state.jobs.get(at), update) {
            (JobOut::New, None, Update::Create { job }) => Record::Read((*job).clone()),
            (JobOut::Same, Some(record), _) => record.clone(),
            (out, Some(Record::Read(job)), update) => {
                let job = apply(job, *out, update)?;
                settled.answered.push(Answered {
                    out: *out,
                    job: job.clone(),
                });
                Record::Read(job)
            }
            (_, _, _) => return Err(inconsistent()),
        };
        jobs.push(record);
    }
    if served.jobs.len() < state.jobs.len() {
        return Err(inconsistent());
    }
    let mut dispatches = Vec::with_capacity(served.claims.len());
    for (at, out) in served.claims.iter().enumerate() {
        match (out, state.dispatches.get(at)) {
            (ClaimOut::Keep, Some(record)) => dispatches.push(record.clone()),
            (ClaimOut::Drop, Some(_)) => {}
            (
                ClaimOut::New {
                    at: job_at,
                    dispatch,
                },
                _,
            ) => {
                let (
                    Some(Record::Read(before)),
                    Some(Record::Read(job)),
                    Update::Claim { now, .. },
                ) = (state.jobs.get(*job_at), jobs.get(*job_at), update)
                else {
                    return Err(inconsistent());
                };
                dispatches.push(Record::Read(AgentCronDispatchRecord {
                    id: dispatch.clone(),
                    job_id: job.id.clone(),
                    claimed_at: iso_from_millis(*now),
                    scheduled_for: before.next_run_at.clone().unwrap_or_default(),
                    owner: me.clone(),
                }));
                settled.claimed.push(AgentCronDispatch {
                    id: dispatch.clone(),
                    job: job.clone(),
                });
            }
            (ClaimOut::Keep | ClaimOut::Drop, None) => return Err(inconsistent()),
        }
    }
    if served.claims.len() < state.dispatches.len() {
        return Err(inconsistent());
    }
    Ok(CronJobsState {
        jobs,
        dispatches,
        other_keys: state.other_keys.clone(),
    })
}

/// A job as the answer on it makes it: the fields each answer sets.
fn apply(job: &AgentCronJob, out: JobOut, update: &Update<'_>) -> anyhow::Result<AgentCronJob> {
    let mut job = job.clone();
    match (out, update) {
        (JobOut::Took(took), Update::Claim { now, .. }) => {
            let now_iso = iso_from_millis(*now);
            let (next, claimed) = match took {
                Took::Keep => return Ok(job),
                Took::Roll(next) => (next, false),
                Took::Claim(next) => (next, true),
            };
            job.next_run_at = next_text(&job, next, *now).ok().flatten();
            if !claimed {
                job.last_skipped_at = Some(now_iso.clone());
            }
            job.updated_at = now_iso;
        }
        (JobOut::Back(back), Update::Recover { now }) => {
            let Back::Interrupted { status, next } = back else {
                return Ok(job);
            };
            job.status = job_status(status);
            job.next_run_at = next_text_at(&job, next);
            job.last_error = Some(INTERRUPTED.to_string());
            job.updated_at = iso_from_millis(*now);
        }
        (JobOut::Finished(finished), Update::Finish { result, now, .. }) => {
            let now_iso = iso_from_millis(*now);
            let becomes = match finished {
                Finished::Untouched => return Ok(job),
                Finished::Ran(becomes) => {
                    job.last_run_at = Some(now_iso.clone());
                    job.last_error.clone_from(&result.error);
                    job.run_count += 1;
                    becomes
                }
                Finished::Skipped(becomes) => {
                    job.last_skipped_at = Some(now_iso.clone());
                    becomes
                }
            };
            job.next_run_at = next_text(&job, becomes.next, *now).ok().flatten();
            job.status = job_status(becomes.status);
            job.failure_streak = becomes.streak;
            job.updated_at = now_iso;
        }
        (JobOut::Cut(cut), Update::Cancel { now, .. }) => {
            let Cut::Cut { status, next } = cut else {
                return Ok(job);
            };
            job.status = job_status(status);
            job.next_run_at = next_text_at(&job, next);
            job.updated_at = iso_from_millis(*now);
        }
        (JobOut::Again(again), Update::Resume { now, edit, .. }) => {
            let Again::Resumed(becomes) = again else {
                return Ok(job);
            };
            job.next_run_at = match edit {
                Some(_) => next_text(&job, becomes.next, *now).ok().flatten(),
                None => next_text(&job, becomes.next, *now)?,
            };
            job.status = job_status(becomes.status);
            job.failure_streak = becomes.streak;
            job.updated_at = iso_from_millis(*now);
        }
        (
            JobOut::Same
            | JobOut::New
            | JobOut::Took(_)
            | JobOut::Back(_)
            | JobOut::Finished(_)
            | JobOut::Cut(_)
            | JobOut::Again(_),
            _,
        ) => anyhow::bail!("the compiled core answered another cron update"),
    }
    Ok(job)
}
