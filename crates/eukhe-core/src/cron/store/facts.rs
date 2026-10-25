//! The facts of a job the compiled core decides on
//! ([`eukhe_bend::rules::cron`], `bend/cron_store.bend`), and what a job's
//! fields become from its answers. The store reads the file, gathers these
//! facts per job, and writes back what the core answers: the rule itself
//! (when a job is due, which claims clear, the finish step with its
//! backoff and stop, cancel, resume) runs in the core.

use eukhe_bend::rules::cron::{Fact, Next, Plan, Status};

use super::iso_from_millis;
use crate::cron::{
    next_run_at_for_schedule, parse_iso_millis, AgentCronJob, JobStatus, ScheduleKind,
};

fn status_fact(status: JobStatus) -> Status {
    match status {
        JobStatus::Active => Status::Active,
        JobStatus::Paused => Status::Paused,
        JobStatus::Completed => Status::Completed,
        JobStatus::Cancelled => Status::Cancelled,
    }
}

/// The job status the core answered.
pub(crate) fn job_status(status: Status) -> JobStatus {
    match status {
        Status::Active => JobStatus::Active,
        Status::Paused => JobStatus::Paused,
        Status::Completed => JobStatus::Completed,
        Status::Cancelled => JobStatus::Cancelled,
    }
}

fn stored_next(job: &AgentCronJob) -> Option<u64> {
    job.next_run_at.as_deref().and_then(parse_iso_millis)
}

/// What the core reads of a job: an interval schedule with no valid
/// interval is a rule, which the store evaluates (and which fails).
pub(crate) fn fact_of(job: &AgentCronJob) -> Fact {
    let plan = match (job.schedule.kind, job.schedule.interval_ms) {
        (ScheduleKind::Once, _) => Plan::Once,
        (ScheduleKind::Interval, Some(ms)) if ms > 0 => Plan::Every(ms),
        (ScheduleKind::Interval | ScheduleKind::Cron, _) => Plan::Rule,
    };
    Fact {
        status: status_fact(job.status),
        plan,
        next: stored_next(job),
        streak: job.failure_streak,
    }
}

/// A stored next run from a time the core answered: the stored text when
/// the time is the one the store read (its text kept as it is).
pub(crate) fn next_text_at(job: &AgentCronJob, next: Option<u64>) -> Option<String> {
    match next {
        None => None,
        Some(ms) if Some(ms) == stored_next(job) => job.next_run_at.clone(),
        Some(ms) => Some(iso_from_millis(ms)),
    }
}

/// A stored next run from the next run the core answered at `at`; a roll
/// evaluates the job's schedule rule after `at`.
///
/// # Errors
///
/// Returns an error when the rule is invalid (an interval schedule with
/// no interval, a cron expression that does not parse or match).
pub(crate) fn next_text(job: &AgentCronJob, next: Next, at: u64) -> anyhow::Result<Option<String>> {
    Ok(match next {
        Next::None => None,
        Next::At(ms) => next_text_at(job, Some(ms)),
        Next::Roll => next_run_at_for_schedule(&job.schedule, at)?.map(iso_from_millis),
    })
}
