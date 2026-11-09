//! Session-artifact partitioning: registration of per-session scheduled-jobs
//! artifact files and the read of one artifact file. A change keeps each
//! artifact file holding only its session's jobs and their dispatches
//! (`AgentCronJobStore::mutate_jobs`, in [`super::state`]); records a file
//! holds that this build cannot read, and dispatches of no known job, stay
//! in their file.
//! Section of the port of the `AgentCronJobStore` half of core/cron-jobs.ts.

use std::path::{Path, PathBuf};

use super::state::read_jobs_state;
use super::{AgentCronJobStore, SESSION_SCHEDULED_JOBS_FILENAME};
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
            .rebind_session_jobs(
                &SessionBinding {
                    active_session_id: "live-2".to_string(),
                    session_id: "session-1".to_string(),
                    session_file: "/w/session.jsonl".to_string(),
                    cwd: "/w".to_string(),
                },
                now,
            )
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
