//! Generic cron job operations: create/list/cancel, session binding and
//! rebinding, due-claim dispatch, the finish step that records a dispatch's
//! result, and interrupted-dispatch recovery. The compiled core decides
//! each job (`eukhe_bend::rules::cron`: when it is due, the failure backoff
//! and stop, cancel); this file reads and writes the file around it.
//! Section of the port of the `AgentCronJobStore` half of core/cron-jobs.ts.

use std::sync::Arc;

use crate::cron::JobSource;
use uuid::Uuid;

use super::state::{
    claim_due_in_state, compare_optional_iso, normalize_optional_label,
    recover_interrupted_in_state, resolve_path,
};
use eukhe_bend::rules::cron::{self as rule, Cut, Finished};

use super::facts::{fact_of, job_status, next_text, next_text_at};
use super::{
    iso_from_millis, now_millis, AgentCronJobStore, CancelJobsFilter, CreateAgentCronJobInput,
    DispatchOutcome, DispatchResultOptions, RunningDispatch, SessionBinding,
};
use crate::cron::{
    is_due_job, parse_agent_cron_schedule, parse_iso_millis, AgentCronJob, JobStatus,
};

impl AgentCronJobStore {
    pub fn list(&self) -> Vec<AgentCronJob> {
        let mut jobs = self.read_jobs();
        jobs.sort_by(|left, right| {
            compare_optional_iso(left.next_run_at.as_deref(), right.next_run_at.as_deref())
        });
        jobs
    }

    /// Create a cron job from the input schedule and prompt.
    ///
    /// # Errors
    ///
    /// Returns an error when the prompt is empty or the schedule text cannot
    /// be parsed.
    pub fn create(&self, input: &CreateAgentCronJobInput) -> anyhow::Result<AgentCronJob> {
        let prompt = input.prompt.trim();
        if prompt.is_empty() {
            anyhow::bail!("Cron job prompt cannot be empty");
        }
        let now = input.now.unwrap_or_else(now_millis);
        let parsed = parse_agent_cron_schedule(&input.schedule_text, now)?;
        let now_iso = iso_from_millis(now);
        let job = AgentCronJob {
            id: Uuid::new_v4().to_string(),
            status: JobStatus::Active,
            source: input.source.unwrap_or(JobSource::Cron),
            runtime_kind: input.runtime_kind.clone(),
            delivery_mode: None,
            active_session_id: input.active_session_id.clone(),
            session_id: input.session_id.clone(),
            session_file: input.session_file.clone(),
            cwd: input.cwd.clone(),
            label: normalize_optional_label(input.label.as_deref()),
            prompt: prompt.to_string(),
            schedule: parsed.0,
            created_at: now_iso.clone(),
            updated_at: now_iso,
            next_run_at: Some(iso_from_millis(parsed.1)),
            last_run_at: None,
            last_skipped_at: None,
            last_error: None,
            run_count: 0,
            failure_streak: 0,
        };
        let mut jobs = self.read_jobs();
        jobs.push(job.clone());
        self.write_jobs(&jobs)?;
        Ok(job)
    }

    /// Bind jobs stored for a session file to a live session id on restore, or
    /// move a live session's jobs to a new file when it switches.
    ///
    /// # Errors
    ///
    /// Returns an error when the state lock or write fails.
    pub fn rebind_session_jobs(&self, input: &SessionBinding) -> anyhow::Result<Vec<AgentCronJob>> {
        let target_session_file = resolve_path(&input.session_file);
        let mut rebound_jobs = Vec::new();
        let jobs: Vec<AgentCronJob> = self
            .read_jobs()
            .into_iter()
            .map(|job| {
                if job.active_session_id != input.active_session_id
                    && resolve_path(&job.session_file) != target_session_file
                {
                    return job;
                }
                if job.active_session_id == input.active_session_id
                    && job.session_id == input.session_id
                    && resolve_path(&job.session_file) == target_session_file
                    && job.cwd == input.cwd
                {
                    return job;
                }
                let rebound = AgentCronJob {
                    active_session_id: input.active_session_id.clone(),
                    session_id: input.session_id.clone(),
                    session_file: input.session_file.clone(),
                    cwd: input.cwd.clone(),
                    ..job
                };
                rebound_jobs.push(rebound.clone());
                rebound
            })
            .collect();
        if !rebound_jobs.is_empty() {
            self.write_jobs(&jobs)?;
        }
        Ok(rebound_jobs)
    }
    /// # Errors
    ///
    /// Returns an error when the state lock or write fails.
    pub fn cancel_jobs_for_session(
        &self,
        input: &CancelJobsFilter,
        now: u64,
    ) -> anyhow::Result<Vec<AgentCronJob>> {
        let now_iso = iso_from_millis(now);
        let target_session_file = input.session_file.as_ref().map(|file| resolve_path(file));
        let mut cancelled = Vec::new();
        let jobs: Vec<AgentCronJob> = self
            .read_jobs()
            .into_iter()
            .map(|job| {
                let matches = input
                    .active_session_id
                    .as_ref()
                    .is_some_and(|id| *id == job.active_session_id)
                    || input
                        .session_id
                        .as_ref()
                        .is_some_and(|id| *id == job.session_id)
                    || target_session_file
                        .as_ref()
                        .is_some_and(|file| resolve_path(&job.session_file) == *file);
                if !matches || !matches!(job.status, JobStatus::Active | JobStatus::Paused) {
                    return job;
                }
                let cancelled_job = AgentCronJob {
                    status: JobStatus::Cancelled,
                    next_run_at: None,
                    updated_at: now_iso.clone(),
                    ..job
                };
                cancelled.push(cancelled_job.clone());
                cancelled_job
            })
            .collect();
        if !cancelled.is_empty() {
            self.write_jobs(&jobs)?;
        }
        Ok(cancelled)
    }
    /// # Errors
    ///
    /// Returns an error when the state lock or write fails.
    pub fn cancel(&self, id: &str, now: u64) -> anyhow::Result<Option<AgentCronJob>> {
        let now_iso = iso_from_millis(now);
        let mut cancelled = None;
        let jobs: Vec<AgentCronJob> = self
            .read_jobs()
            .into_iter()
            .map(|job| {
                if job.id != id {
                    return job;
                }
                let Cut::Cut { status, next } = rule::cancel(&fact_of(&job)) else {
                    return job;
                };
                let cancelled_job = AgentCronJob {
                    status: job_status(status),
                    next_run_at: next_text_at(&job, next),
                    updated_at: now_iso.clone(),
                    ..job
                };
                cancelled = Some(cancelled_job.clone());
                cancelled_job
            })
            .collect();
        if cancelled.is_some() {
            self.write_jobs(&jobs)?;
        }
        Ok(cancelled)
    }

    pub fn due(&self, now: u64) -> Vec<AgentCronJob> {
        self.read_jobs()
            .into_iter()
            .filter(|job| is_due_job(job, now))
            .collect()
    }

    /// Atomically claim due jobs: advance their schedule and record
    /// dispatches owned by this process. Each claimed dispatch runs until
    /// its [`RunningDispatch`] drops.
    ///
    /// # Errors
    ///
    /// Returns an error when the state lock or write fails.
    pub fn claim_due(&self, due_at: u64, claimed_at: u64) -> anyhow::Result<Vec<RunningDispatch>> {
        let dispatches =
            self.mutate_states(|state| claim_due_in_state(state, due_at, claimed_at, &self.owner))?;
        Ok(dispatches
            .into_iter()
            .map(|dispatch| RunningDispatch::new(dispatch, Arc::clone(&self.owner)))
            .collect())
    }

    pub fn get_claimed_job(&self, id: &str) -> Option<AgentCronJob> {
        for state in self.read_states() {
            if !state
                .dispatches
                .iter()
                .any(|dispatch| dispatch.job_id == id)
            {
                continue;
            }
            return state
                .jobs
                .into_iter()
                .find(|job| job.id == id && job.status == JobStatus::Active);
        }
        None
    }

    /// The finish step of a claimed dispatch: release the claim and record
    /// the result on its job, as the compiled core decides it
    /// (`rule::finish`): only an active job counts a result; a one-shot is
    /// completed; a failed run of a repeating job counts one more failure
    /// in a row, pushes the next run out by the backoff (never earlier than
    /// the schedule) or, at the cap, pauses the job; a good run sets the
    /// count back to 0; a skip leaves it. Returns the updated job, or
    /// `None` when the dispatch is no longer pending or its job is not
    /// active.
    ///
    /// # Errors
    ///
    /// Returns an error when the state lock or write fails.
    pub fn record_dispatch_result(
        &self,
        dispatch_id: &str,
        result: &DispatchResultOptions,
    ) -> anyhow::Result<Option<AgentCronJob>> {
        let now = result.now.unwrap_or_else(now_millis);
        let now_iso = iso_from_millis(now);
        let mut updated = None;
        self.mutate_states(|state| {
            let Some(at) = state
                .dispatches
                .iter()
                .position(|candidate| candidate.id == dispatch_id)
            else {
                return Vec::new();
            };
            let dispatch = state.dispatches.remove(at);
            let Some(job) = state.jobs.iter_mut().find(|job| job.id == dispatch.job_id) else {
                return Vec::new();
            };
            let (ran, becomes) = match rule::finish(
                &fact_of(job),
                result.outcome == DispatchOutcome::Ran,
                result.error.is_some(),
                now,
            ) {
                Finished::Untouched => return Vec::new(),
                Finished::Ran(becomes) => (true, becomes),
                Finished::Skipped(becomes) => (false, becomes),
            };
            if ran {
                job.last_run_at = Some(now_iso.clone());
                job.last_error.clone_from(&result.error);
                job.run_count += 1;
            } else {
                job.last_skipped_at = Some(now_iso.clone());
            }
            job.next_run_at = next_text(job, becomes.next, now).ok().flatten();
            job.status = job_status(becomes.status);
            job.failure_streak = becomes.streak;
            job.updated_at.clone_from(&now_iso);
            updated = Some(job.clone());
            Vec::new()
        })?;
        Ok(updated)
    }

    /// Clear the claims this process may clear: its own claims with no live
    /// run (their pass unwound), and the claims of dead processes. The live
    /// claim of another process is never cleared. Returns the active jobs
    /// whose run was interrupted.
    ///
    /// # Errors
    ///
    /// Returns an error when the state lock or write fails.
    pub fn recover_interrupted_dispatches(&self, now: u64) -> anyhow::Result<Vec<AgentCronJob>> {
        let mut recovered = Vec::new();
        self.mutate_states(|state| {
            recover_interrupted_in_state(state, now, &mut recovered, &self.owner);
            Vec::new()
        })?;
        Ok(recovered)
    }

    pub fn next_active_run_at(&self) -> Option<u64> {
        self.read_jobs()
            .iter()
            .filter(|job| job.status == JobStatus::Active)
            .filter_map(|job| job.next_run_at.as_deref().and_then(parse_iso_millis))
            .min()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cron::store::input;
    use crate::cron::ScheduleKind;

    #[test]
    fn create_list_and_cancel() {
        let dir = tempfile::TempDir::new().unwrap();
        let store = AgentCronJobStore::new(dir.path().join("jobs.json"));
        let now = 1_700_000_000_000;
        let job = store
            .create(&input("check the build", "every 10m", now))
            .unwrap();
        assert_eq!(job.status, JobStatus::Active);
        assert_eq!(job.source, JobSource::Cron);
        assert_eq!(job.schedule.kind, ScheduleKind::Interval);
        assert_eq!(store.list().len(), 1);
        let due = store.due(now + 600_000);
        assert!(due.iter().any(|found| found.id == job.id));
        // Cancel.
        let cancelled = store.cancel(&job.id, now + 1).unwrap().unwrap();
        assert_eq!(cancelled.status, JobStatus::Cancelled);
        assert_eq!(store.list()[0].status, JobStatus::Cancelled);
        // Empty prompt rejected.
        assert!(store.create(&input("  ", "every 10m", now)).is_err());
    }

    #[test]
    fn cancel_does_not_ack_when_state_lock_is_held() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("jobs.json");
        let store = AgentCronJobStore::new(path.clone());
        let now = 1_700_000_000_000;
        let job = store.create(&input("tick", "every 10m", now)).unwrap();
        let before = std::fs::read(&path).unwrap();
        let held =
            crate::platform::lock_dir::LockDir::acquire(&path, std::time::Duration::from_secs(30))
                .unwrap();
        assert!(store.cancel(&job.id, now + 1).is_err());
        assert_eq!(std::fs::read(&path).unwrap(), before);
        drop(held);
        assert_eq!(store.list(), vec![job]);
    }

    #[test]
    fn claim_dispatch_and_result_recording() {
        let dir = tempfile::TempDir::new().unwrap();
        let store = AgentCronJobStore::new(dir.path().join("jobs.json"));
        let now = 1_700_000_000_000;
        let job = store.create(&input("tick", "every 10m", now)).unwrap();
        // Not due yet.
        assert!(store.claim_due(now, now).unwrap().is_empty());
        // Due later: claim advances the schedule and records a dispatch.
        let dispatches = store.claim_due(now + 600_000, now + 600_000).unwrap();
        assert_eq!(dispatches.len(), 1);
        assert_eq!(dispatches[0].dispatch().job.id, job.id);
        assert_eq!(
            dispatches[0].dispatch().job.next_run_at.as_deref(),
            Some(iso_from_millis(now + 1_200_000).as_str())
        );
        // The claimed job is retrievable.
        assert!(store.get_claimed_job(&job.id).is_some());
        // Record a run result: clears the dispatch, bumps counters.
        let updated = store
            .record_dispatch_result(
                &dispatches[0].dispatch().id,
                &DispatchResultOptions {
                    now: Some(now + 600_001),
                    outcome: DispatchOutcome::Ran,
                    error: None,
                },
            )
            .unwrap()
            .unwrap();
        assert_eq!(updated.run_count, 1);
        assert!(store.get_claimed_job(&job.id).is_none());
        // A claim whose run is live is not recovered; once its pass
        // unwinds (the running dispatch drops), it is.
        let second = store.claim_due(now + 1_200_000, now + 1_200_000).unwrap();
        assert_eq!(second.len(), 1);
        assert!(store
            .recover_interrupted_dispatches(now + 1_250_000)
            .unwrap()
            .is_empty());
        drop(second);
        let recovered = store
            .recover_interrupted_dispatches(now + 1_300_000)
            .unwrap();
        assert_eq!(recovered.len(), 1);
        assert_eq!(
            recovered[0].last_error.as_deref(),
            Some("Interrupted before scheduled operation completion")
        );
    }

    #[test]
    fn claim_due_skips_while_the_state_lock_is_held() {
        let dir = tempfile::tempdir().unwrap();
        let store = AgentCronJobStore::new(dir.path().join("jobs.json"));
        let now = 1_700_000_000_000;
        let job = store.create(&input("tick", "every 10m", now)).unwrap();
        let path = store.require_file_path();
        let before = std::fs::read(&path).unwrap();
        {
            let _held = crate::platform::lock_dir::LockDir::acquire(
                &path,
                std::time::Duration::from_secs(30),
            )
            .unwrap();
            assert!(store.claim_due(now + 600_000, now + 600_000).is_err());
            assert_eq!(std::fs::read(&path).unwrap(), before);
        }
        let dispatches = store.claim_due(now + 600_000, now + 600_000).unwrap();
        assert_eq!(dispatches.len(), 1);
        assert_eq!(dispatches[0].dispatch().job.id, job.id);
    }

    /// Audit F6: a job record this build cannot read was dropped by the
    /// next write. Now it, an unread claim and an unknown key stay as
    /// they are.
    #[test]
    fn an_unread_job_survives_a_create() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("jobs.json");
        let unread_job = serde_json::json!({"id": "newer", "schedule": {"kind": "lunar"}});
        let unread_claim =
            serde_json::json!({"id": "old", "jobId": "x", "claimedAt": "", "scheduledFor": ""});
        std::fs::write(
            &path,
            serde_json::json!({"jobs": [unread_job], "dispatches": [unread_claim], "note": 1.5})
                .to_string(),
        )
        .unwrap();
        let store = AgentCronJobStore::new(path.clone());
        let job = store
            .create(&input("tick", "every 10m", 1_700_000_000_000))
            .unwrap();
        let written: serde_json::Value =
            serde_json::from_str(&std::fs::read_to_string(&path).unwrap()).unwrap();
        assert_eq!(
            written,
            serde_json::json!({
                "jobs": [serde_json::to_value(&job).unwrap(), unread_job],
                "dispatches": [unread_claim],
                "note": 1.5
            })
        );
    }

    /// Audit F6: a corrupt file read as empty and the next write replaced
    /// it. Now a read leaves it, and the next update moves it aside first.
    #[test]
    fn a_corrupt_file_is_moved_aside() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("jobs.json");
        std::fs::write(&path, "{\"jobs\": [ torn").unwrap();
        let store = AgentCronJobStore::new(path.clone());
        assert_eq!(store.list(), Vec::new());
        assert_eq!(std::fs::read_to_string(&path).unwrap(), "{\"jobs\": [ torn");
        let job = store
            .create(&input("tick", "every 10m", 1_700_000_000_000))
            .unwrap();
        let aside: Vec<String> = std::fs::read_dir(dir.path())
            .unwrap()
            .map(|entry| entry.unwrap().file_name().to_string_lossy().into_owned())
            .filter(|name| name.starts_with("jobs.json.corrupt-"))
            .map(|name| std::fs::read_to_string(dir.path().join(name)).unwrap())
            .collect();
        assert_eq!(aside, vec!["{\"jobs\": [ torn".to_string()]);
        assert_eq!(store.list(), vec![job]);
    }
}
