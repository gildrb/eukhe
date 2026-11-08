//! `/heartbeat` job management: create/pause/resume/clear lifecycle plus
//! the heartbeat management actions (pause/resume/stop). Every status a
//! heartbeat takes comes from the compiled core (`eukhe_bend::rules::cron`
//! `make`, `halt`, `resume`).
//! Section of the port of the `AgentCronJobStore` half of core/cron-jobs.ts.

use crate::cron::JobSource;
use uuid::Uuid;

use eukhe_bend::rules::cron::{self as rule, Again, Cut, Halt};

use super::facts::{fact_of, job_status, next_text, next_text_at};
use super::state::normalize_optional_label;
use super::{
    iso_from_millis, now_millis, AgentCronJobStore, CreateAgentCronJobInput,
    HeartbeatManagementAction,
};
use crate::cron::{
    is_heartbeat_cron_job, parse_agent_cron_schedule, parse_iso_millis, AgentCronJob, JobStatus,
    ScheduleKind, DEFAULT_HEARTBEAT_DELIVERY_MODE,
};

impl AgentCronJobStore {
    pub fn get_heartbeat(&self, active_session_id: &str) -> Option<AgentCronJob> {
        self.read_jobs()
            .into_iter()
            .filter(|job| {
                job.active_session_id == active_session_id
                    && job.source == JobSource::Heartbeat
                    && matches!(job.status, JobStatus::Active | JobStatus::Paused)
            })
            .max_by_key(|job| parse_iso_millis(&job.updated_at).unwrap_or(0))
    }

    /// Create the heartbeat job for a session, cancelling its existing
    /// active/paused heartbeat first.
    ///
    /// # Errors
    ///
    /// Returns an error when the schedule text cannot be parsed, when the
    /// schedule is not recurring, or when the heartbeat instruction is empty.
    pub fn create_heartbeat(
        &self,
        input: &CreateAgentCronJobInput,
    ) -> anyhow::Result<AgentCronJob> {
        let now = input.now.unwrap_or_else(now_millis);
        let parsed = parse_agent_cron_schedule(&input.schedule_text, now)?;
        if parsed.0.kind == ScheduleKind::Once {
            anyhow::bail!("Heartbeat schedule must be recurring");
        }
        let prompt = input.prompt.trim();
        if prompt.is_empty() {
            anyhow::bail!("Heartbeat instruction cannot be empty");
        }
        let now_iso = iso_from_millis(now);
        // Stop the session's existing heartbeats (the compiled core leaves
        // a completed or cancelled one as it is).
        let existing: Vec<AgentCronJob> = self
            .read_jobs()
            .into_iter()
            .map(|job| {
                if job.active_session_id != input.active_session_id
                    || job.source != JobSource::Heartbeat
                {
                    return job;
                }
                match rule::halt(&fact_of(&job), Halt::Stop) {
                    Cut::Same => job,
                    Cut::Cut { status, next } => AgentCronJob {
                        status: job_status(status),
                        next_run_at: next_text_at(&job, next),
                        updated_at: now_iso.clone(),
                        ..job
                    },
                }
            })
            .collect();
        let made = rule::make(parsed.1);
        let job = AgentCronJob {
            id: Uuid::new_v4().to_string(),
            status: job_status(made.status),
            source: JobSource::Heartbeat,
            runtime_kind: input.runtime_kind.clone(),
            delivery_mode: Some(
                input
                    .delivery_mode
                    .unwrap_or(DEFAULT_HEARTBEAT_DELIVERY_MODE),
            ),
            active_session_id: input.active_session_id.clone(),
            session_id: input.session_id.clone(),
            session_file: input.session_file.clone(),
            cwd: input.cwd.clone(),
            label: normalize_optional_label(input.label.as_deref()),
            prompt: prompt.to_string(),
            schedule: parsed.0,
            created_at: now_iso.clone(),
            updated_at: now_iso,
            next_run_at: Some(iso_from_millis(made.next)),
            last_run_at: None,
            last_skipped_at: None,
            last_error: None,
            run_count: 0,
            failure_streak: made.streak,
        };
        let mut jobs = existing;
        jobs.push(job.clone());
        self.write_jobs(&jobs)?;
        Ok(job)
    }
    /// # Errors
    ///
    /// Returns an error when the state lock or write fails.
    pub fn pause_heartbeat(
        &self,
        active_session_id: &str,
        now: u64,
    ) -> anyhow::Result<Option<AgentCronJob>> {
        let Some(current) = self.get_heartbeat(active_session_id) else {
            return Ok(None);
        };
        let now_iso = iso_from_millis(now);
        let mut paused = None;
        let jobs: Vec<AgentCronJob> = self
            .read_jobs()
            .into_iter()
            .map(|job| {
                if job.id != current.id {
                    return job;
                }
                let Cut::Cut { status, next } = rule::halt(&fact_of(&job), Halt::Pause) else {
                    return job;
                };
                let paused_job = AgentCronJob {
                    status: job_status(status),
                    next_run_at: next_text_at(&job, next),
                    updated_at: now_iso.clone(),
                    ..job
                };
                paused = Some(paused_job.clone());
                paused_job
            })
            .collect();
        if paused.is_some() {
            self.write_jobs(&jobs)?;
        }
        Ok(paused)
    }

    /// Resume the heartbeat for a session, recomputing its next run time.
    /// Returns `Ok(None)` when the session has no heartbeat.
    ///
    /// # Errors
    ///
    /// Returns an error when the stored schedule is invalid or not
    /// recurring.
    pub fn resume_heartbeat(
        &self,
        active_session_id: &str,
        now: u64,
    ) -> anyhow::Result<Option<AgentCronJob>> {
        let Some(current) = self.get_heartbeat(active_session_id) else {
            return Ok(None);
        };
        let becomes = match rule::resume(&fact_of(&current), now) {
            Again::Resumed(becomes) => becomes,
            Again::Ended => return Ok(None),
            Again::NotRecurring => anyhow::bail!("Heartbeat schedule must be recurring"),
        };
        let next_run_at = next_text(&current, becomes.next, now)?;
        let now_iso = iso_from_millis(now);
        let mut resumed = None;
        let jobs: Vec<AgentCronJob> = self
            .read_jobs()
            .into_iter()
            .map(|job| {
                if job.id != current.id {
                    return job;
                }
                let resumed_job = AgentCronJob {
                    status: job_status(becomes.status),
                    next_run_at: next_run_at.clone(),
                    updated_at: now_iso.clone(),
                    failure_streak: becomes.streak,
                    ..job
                };
                resumed = Some(resumed_job.clone());
                resumed_job
            })
            .collect();
        self.write_jobs(&jobs)?;
        Ok(resumed)
    }

    /// # Errors
    ///
    /// Returns an error when the state lock or write fails.
    pub fn clear_heartbeat(
        &self,
        active_session_id: &str,
        now: u64,
    ) -> anyhow::Result<Option<AgentCronJob>> {
        let Some(current) = self.get_heartbeat(active_session_id) else {
            return Ok(None);
        };
        let now_iso = iso_from_millis(now);
        let mut cleared = None;
        let jobs: Vec<AgentCronJob> = self
            .read_jobs()
            .into_iter()
            .map(|job| {
                if job.id != current.id {
                    return job;
                }
                let Cut::Cut { status, next } = rule::halt(&fact_of(&job), Halt::Stop) else {
                    return job;
                };
                let cleared_job = AgentCronJob {
                    status: job_status(status),
                    next_run_at: next_text_at(&job, next),
                    updated_at: now_iso.clone(),
                    ..job
                };
                cleared = Some(cleared_job.clone());
                cleared_job
            })
            .collect();
        if cleared.is_some() {
            self.write_jobs(&jobs)?;
        }
        Ok(cleared)
    }

    /// Apply a pause, stop, or resume management action to a heartbeat job.
    /// Returns `Ok(None)` when no matching heartbeat job was found (cancelled
    /// and completed jobs are left untouched).
    ///
    /// # Errors
    ///
    /// Returns an error when resuming a job whose stored schedule is invalid
    /// or not recurring.
    pub fn manage_heartbeat(
        &self,
        active_session_id: &str,
        id: &str,
        action: HeartbeatManagementAction,
        now: u64,
    ) -> anyhow::Result<Option<AgentCronJob>> {
        let now_iso = iso_from_millis(now);
        let mut jobs = self.read_jobs();
        let Some(job) = jobs.iter_mut().find(|job| {
            job.id == id && job.active_session_id == active_session_id && is_heartbeat_cron_job(job)
        }) else {
            return Ok(None);
        };
        match action {
            HeartbeatManagementAction::Pause | HeartbeatManagementAction::Stop => {
                let how = if action == HeartbeatManagementAction::Pause {
                    Halt::Pause
                } else {
                    Halt::Stop
                };
                let Cut::Cut { status, next } = rule::halt(&fact_of(job), how) else {
                    return Ok(None);
                };
                job.next_run_at = next_text_at(job, next);
                job.status = job_status(status);
            }
            HeartbeatManagementAction::Resume => {
                let becomes = match rule::resume(&fact_of(job), now) {
                    Again::Resumed(becomes) => becomes,
                    Again::Ended => return Ok(None),
                    Again::NotRecurring => {
                        anyhow::bail!("Heartbeat schedule must be recurring")
                    }
                };
                job.next_run_at = next_text(job, becomes.next, now)?;
                job.status = job_status(becomes.status);
                job.failure_streak = becomes.streak;
            }
        }
        job.updated_at = now_iso;
        let updated = job.clone();
        self.write_jobs(&jobs)?;
        Ok(Some(updated))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cron::store::input;

    #[test]
    fn pause_does_not_ack_when_state_lock_is_held() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("jobs.json");
        let store = AgentCronJobStore::new(path.clone());
        let now = 1_700_000_000_000;
        let heartbeat = store
            .create_heartbeat(&input("continue", "every 5m", now))
            .unwrap();
        let before = std::fs::read(&path).unwrap();
        let held =
            crate::platform::lock_dir::LockDir::acquire(&path, std::time::Duration::from_secs(30))
                .unwrap();
        assert!(store.pause_heartbeat("live-1", now + 1).is_err());
        assert_eq!(std::fs::read(&path).unwrap(), before);
        drop(held);
        assert_eq!(store.get_heartbeat("live-1"), Some(heartbeat));
    }

    #[test]
    fn heartbeat_lifecycle() {
        let dir = tempfile::TempDir::new().unwrap();
        let store = AgentCronJobStore::new(dir.path().join("jobs.json"));
        let now = 1_700_000_000_000;
        let heartbeat = store
            .create_heartbeat(&input("continue the mission", "every 5m", now))
            .unwrap();
        assert_eq!(store.get_heartbeat("live-1").unwrap().id, heartbeat.id);
        // Pause clears nextRunAt.
        let paused = store.pause_heartbeat("live-1", now + 1).unwrap().unwrap();
        assert_eq!(paused.status, JobStatus::Paused);
        assert_eq!(paused.next_run_at, None);
        // Resume recomputes nextRunAt.
        let resumed = store.resume_heartbeat("live-1", now + 2).unwrap().unwrap();
        assert_eq!(resumed.status, JobStatus::Active);
        assert!(resumed.next_run_at.is_some());
        // A second create cancels the first.
        let second = store
            .create_heartbeat(&input("new instruction", "every 2m", now + 3))
            .unwrap();
        assert_eq!(store.get_heartbeat("live-1").unwrap().id, second.id);
        assert_eq!(store.list().len(), 2);
        let jobs = store.list();
        let cancelled_first = jobs.iter().find(|job| job.id != second.id).unwrap();
        assert_eq!(cancelled_first.status, JobStatus::Cancelled);
        // Clear cancels.
        let cleared = store.clear_heartbeat("live-1", now + 4).unwrap().unwrap();
        assert_eq!(cleared.status, JobStatus::Cancelled);
        // One-shot schedules are rejected for heartbeats.
        assert!(store
            .create_heartbeat(&input("nope", "in 10m", now))
            .is_err());
    }
}
