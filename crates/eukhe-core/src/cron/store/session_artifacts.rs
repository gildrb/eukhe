//! Session-artifact partitioning: registration of per-session scheduled-jobs
//! artifact files, recovery of a session's jobs from its artifact partition,
//! and the partitioned merge-write that keeps each artifact file holding only
//! its session's jobs and dispatches. Records a file holds that this build
//! cannot read, and dispatches of no known job, stay in their file.
//! Section of the port of the `AgentCronJobStore` half of core/cron-jobs.ts.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use super::state::{
    load_jobs_state, merge_fresh_jobs, read_jobs_state, with_state_locks, write_jobs_state,
};
use super::{AgentCronJobStore, CronJobsState, SESSION_SCHEDULED_JOBS_FILENAME};
use crate::cron::AgentCronJob;

impl AgentCronJobStore {
    /// Register one session's artifact partition. Idempotent: re-registering
    /// the same directory is a no-op, so call sites can bind on every read.
    pub fn register_session_artifact(&self, session_id: &str, artifact_dir: &Path) -> bool {
        if !self.session_artifact_mode {
            return false;
        }
        let path = artifact_dir.join(SESSION_SCHEDULED_JOBS_FILENAME);
        let mut files = self
            .session_artifact_files
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if files.get(session_id) == Some(&path) {
            return false;
        }
        files.insert(session_id.to_string(), path);
        true
    }

    /// Every registered `(session id, artifact file)` pair.
    pub fn session_artifacts(&self) -> Vec<(String, PathBuf)> {
        let files = self
            .session_artifact_files
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        files.clone().into_iter().collect()
    }

    pub(crate) fn write_jobs_session_artifacts(&self, jobs: &[AgentCronJob]) -> anyhow::Result<()> {
        let artifact_files = self
            .session_artifact_files
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .clone();
        let registered: std::collections::HashSet<String> =
            artifact_files.keys().cloned().collect();
        for job in jobs {
            if !registered.contains(&job.session_id) {
                anyhow::bail!(
                    "cron job session artifact not registered: {}",
                    job.session_id
                );
            }
        }
        let paths: Vec<PathBuf> = artifact_files.values().cloned().collect();
        let with_locks = with_state_locks(&paths, || -> anyhow::Result<()> {
            let current_by_session_id: HashMap<String, CronJobsState> = artifact_files
                .iter()
                .map(|(session_id, path)| Ok((session_id.clone(), load_jobs_state(path)?)))
                .collect::<anyhow::Result<_>>()?;
            let incoming_by_id: HashMap<&str, &AgentCronJob> =
                jobs.iter().map(|job| (job.id.as_str(), job)).collect();
            let mut merged_by_session_id: HashMap<String, Vec<AgentCronJob>> = HashMap::new();
            for (session_id, current) in &current_by_session_id {
                let retained: Vec<AgentCronJob> = current
                    .jobs
                    .iter()
                    .filter(|job| {
                        incoming_by_id
                            .get(job.id.as_str())
                            .is_none_or(|incoming| incoming.session_id == *session_id)
                    })
                    .cloned()
                    .collect();
                let session_jobs: Vec<AgentCronJob> = jobs
                    .iter()
                    .filter(|job| job.session_id == *session_id)
                    .cloned()
                    .collect();
                merged_by_session_id
                    .insert(session_id.clone(), merge_fresh_jobs(retained, session_jobs));
            }
            let session_id_by_job_id: HashMap<String, String> = merged_by_session_id
                .iter()
                .flat_map(|(session_id, session_jobs)| {
                    session_jobs
                        .iter()
                        .map(move |job| (job.id.clone(), session_id.clone()))
                })
                .collect();
            let session_id_by_job_id = &session_id_by_job_id;
            for (session_id, path) in &artifact_files {
                let Some(current) = current_by_session_id.get(session_id) else {
                    continue;
                };
                // A dispatch goes to the file of its job's session; a
                // dispatch of no known job stays in its own file.
                let dispatches = current_by_session_id
                    .iter()
                    .flat_map(|(from, state)| {
                        state.dispatches.iter().filter(move |dispatch| {
                            match session_id_by_job_id.get(&dispatch.job_id) {
                                Some(to) => to == session_id,
                                None => from == session_id,
                            }
                        })
                    })
                    .cloned()
                    .collect();
                let next_state = CronJobsState {
                    jobs: merged_by_session_id
                        .get(session_id)
                        .cloned()
                        .unwrap_or_default(),
                    dispatches,
                    unread_jobs: current.unread_jobs.clone(),
                    unread_dispatches: current.unread_dispatches.clone(),
                    other_keys: current.other_keys.clone(),
                };
                if serde_json::to_string(current).unwrap_or_default()
                    != serde_json::to_string(&next_state).unwrap_or_default()
                {
                    write_jobs_state(path, &next_state)?;
                }
            }
            Ok(())
        });
        with_locks.ok_or_else(|| anyhow::anyhow!("cron jobs state lock not acquired; skipped"))?
    }
}

/// Read one scheduled-jobs artifact file's job rows: an unlocked read-only
/// scan (the atomic rename means a reader never sees a torn file) shared by
/// the update-flow roster projection (heartbeat rows are a projection of
/// these files, never a separate write path) and the supervisor's boot
/// re-arm. A missing or unparseable file reads as no jobs.
#[must_use]
pub fn read_scheduled_jobs_artifact(path: &Path) -> Vec<AgentCronJob> {
    read_jobs_state(path).jobs
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cron::store::{input, CancelJobsFilter, SessionBinding};

    #[test]
    fn session_artifact_partitioning() {
        let dir = tempfile::TempDir::new().unwrap();
        let store = AgentCronJobStore::for_session_artifacts();
        let artifacts_a = dir.path().join("a");
        let artifacts_b = dir.path().join("b");
        std::fs::create_dir_all(&artifacts_a).unwrap();
        std::fs::create_dir_all(&artifacts_b).unwrap();
        assert!(store.register_session_artifact("session-1", &artifacts_a));
        assert!(!store.register_session_artifact("session-1", &artifacts_a)); // idempotent
        assert!(store.register_session_artifact("session-2", &artifacts_b));
        let now = 1_700_000_000_000;
        store.create(&input("job a", "every 10m", now)).unwrap();
        let mut job_b = input("job b", "every 20m", now);
        job_b.session_id = "session-2".to_string();
        store.create(&job_b).unwrap();
        let jobs = store.list();
        assert_eq!(jobs.len(), 2);
        // Each artifact file holds only its session's jobs.
        let state_a = read_jobs_state(&artifacts_a.join(SESSION_SCHEDULED_JOBS_FILENAME));
        assert_eq!(state_a.jobs.len(), 1);
        assert_eq!(state_a.jobs[0].prompt, "job a");
        let state_b = read_jobs_state(&artifacts_b.join(SESSION_SCHEDULED_JOBS_FILENAME));
        assert_eq!(state_b.jobs.len(), 1);
        let rebound = store
            .rebind_session_jobs(&SessionBinding {
                active_session_id: "live-2".to_string(),
                session_id: "session-1".to_string(),
                session_file: "/w/session.jsonl".to_string(),
                cwd: "/w".to_string(),
            })
            .unwrap();
        assert_eq!(rebound.len(), 2);
        assert!(rebound.iter().all(|job| job.active_session_id == "live-2"));
        let cancelled = store
            .cancel_jobs_for_session(
                &CancelJobsFilter {
                    session_file: Some("/w/session.jsonl".to_string()),
                    ..Default::default()
                },
                now + 1,
            )
            .unwrap();
        // Both jobs share the session file (the rebind moved both), so both cancel.
        assert_eq!(cancelled.len(), 2);
    }
}
