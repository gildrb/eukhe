//! State save/load for the cron job store: cross-process file locking
//! (lockfile with stale takeover), state read/write/merge helpers, and the
//! in-state due-claim / interrupted-dispatch recovery transitions.
//! Section of the port of the `AgentCronJobStore` half of core/cron-jobs.ts.
//!
//! A file that exists but cannot be read or parsed is never overwritten:
//! an update moves it aside (`<name>.corrupt-<ms>-<id>`) and starts from an
//! empty state. Only a missing file reads as empty. A record that does not
//! parse is kept as it is and written back unchanged.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use serde_json::Value;
use uuid::Uuid;

use super::owner::ClaimOwner;
use super::{
    iso_from_millis, now_millis, AgentCronDispatch, AgentCronDispatchRecord, AgentCronJob,
    AgentCronJobStore, CronJobsState,
};
use crate::cron::{
    is_due_job, next_run_at_for_schedule, parse_iso_millis, JobStatus, ScheduleKind,
};

const LOCK_STALE_MS: u64 = 30_000;

impl AgentCronJobStore {
    pub(crate) fn read_jobs(&self) -> Vec<AgentCronJob> {
        self.read_states()
            .into_iter()
            .flat_map(|state| state.jobs)
            .collect()
    }

    pub(crate) fn read_states(&self) -> Vec<CronJobsState> {
        if self.session_artifact_mode {
            let files = self
                .session_artifact_files
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            return files.values().map(|path| read_jobs_state(path)).collect();
        }
        vec![read_jobs_state(&self.require_file_path())]
    }

    pub(crate) fn mutate_states(
        &self,
        mut mutator: impl FnMut(&mut CronJobsState) -> Vec<AgentCronDispatch>,
    ) -> anyhow::Result<Vec<AgentCronDispatch>> {
        let paths: Vec<PathBuf> = if self.session_artifact_mode {
            self.session_artifact_files
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .values()
                .cloned()
                .collect()
        } else {
            vec![self.require_file_path()]
        };
        let previous_heartbeats = Self::heartbeat_catalog_signature(&self.read_jobs());
        let mut changed = false;
        let dispatches = with_state_locks(&paths, || {
            let mut dispatches = Vec::new();
            for path in &paths {
                let mut state = load_jobs_state(path)?;
                let before = serde_json::to_string(&state).unwrap_or_default();
                dispatches.extend(mutator(&mut state));
                if serde_json::to_string(&state).unwrap_or_default() != before {
                    write_jobs_state(path, &state)?;
                    changed = true;
                }
            }
            Ok::<_, anyhow::Error>(dispatches)
        })
        .ok_or_else(|| anyhow::anyhow!("cron jobs state lock not acquired; skipped"))??;
        if changed && Self::heartbeat_catalog_signature(&self.read_jobs()) != previous_heartbeats {
            self.notify_heartbeat_change();
        }
        Ok(dispatches)
    }

    pub(crate) fn write_jobs(&self, jobs: &[AgentCronJob]) -> anyhow::Result<()> {
        let previous_heartbeats = Self::heartbeat_catalog_signature(&self.read_jobs());
        if self.session_artifact_mode {
            self.write_jobs_session_artifacts(jobs)?;
        } else {
            let path = self.require_file_path();
            with_state_locks(std::slice::from_ref(&path), || write_jobs_file(&path, jobs))
                .ok_or_else(|| anyhow::anyhow!("cron jobs state lock not acquired; skipped"))??;
        }
        if Self::heartbeat_catalog_signature(&self.read_jobs()) != previous_heartbeats {
            self.notify_heartbeat_change();
        }
        Ok(())
    }

    pub(crate) fn require_file_path(&self) -> PathBuf {
        self.file_path
            .clone()
            .expect("Cron job store requires a file path")
    }
}

pub(crate) fn resolve_path(path: &str) -> String {
    Path::new("/")
        .join(eukhe_docs::lexical_normalize(Path::new(path)))
        .to_string_lossy()
        .into_owned()
}

pub(crate) fn compare_optional_iso(left: Option<&str>, right: Option<&str>) -> std::cmp::Ordering {
    use std::cmp::Ordering;
    match (left, right) {
        (left, right) if left == right => Ordering::Equal,
        (None, _) => Ordering::Greater,
        (_, None) => Ordering::Less,
        (Some(left), Some(right)) => parse_iso_millis(left)
            .unwrap_or(0)
            .cmp(&parse_iso_millis(right).unwrap_or(0)),
    }
}

pub(crate) fn normalize_optional_label(label: Option<&str>) -> Option<String> {
    let trimmed = label.map(str::trim).filter(|label| !label.is_empty());
    trimmed.map(std::string::ToString::to_string)
}

pub(crate) fn merge_fresh_jobs(
    current_jobs: Vec<AgentCronJob>,
    next_jobs: Vec<AgentCronJob>,
) -> Vec<AgentCronJob> {
    let mut merged: HashMap<String, AgentCronJob> = HashMap::new();
    for job in current_jobs {
        merged.insert(job.id.clone(), job);
    }
    for job in next_jobs {
        let is_fresh = merged
            .get(&job.id)
            .is_none_or(|current| is_at_least_as_fresh(&job, current));
        if is_fresh {
            merged.insert(job.id.clone(), job);
        }
    }
    merged.into_values().collect()
}

fn is_at_least_as_fresh(candidate: &AgentCronJob, current: &AgentCronJob) -> bool {
    let Some(current_time) = parse_iso_millis(&current.updated_at) else {
        return true;
    };
    let Some(candidate_time) = parse_iso_millis(&candidate.updated_at) else {
        return false;
    };
    candidate_time >= current_time
}

/// Claim the due jobs that have no claim on record: each new claim names
/// `owner` and counts as a live run of it. A due job with a claim on
/// record only rolls its next run.
pub(crate) fn claim_due_in_state(
    state: &mut CronJobsState,
    due_at: u64,
    claimed_at: u64,
    owner: &ClaimOwner,
) -> Vec<AgentCronDispatch> {
    let claimed_iso = iso_from_millis(claimed_at);
    let claimed_job_ids: std::collections::HashSet<String> = state
        .dispatches
        .iter()
        .map(|dispatch| dispatch.job_id.clone())
        .collect();
    let mut dispatches = Vec::new();
    for job in &mut state.jobs {
        if !is_due_job(job, due_at) {
            continue;
        }
        let scheduled_for = job.next_run_at.clone().unwrap_or_default();
        job.next_run_at = next_run_at_for_schedule(&job.schedule, claimed_at)
            .ok()
            .flatten()
            .map(iso_from_millis);
        job.updated_at.clone_from(&claimed_iso);
        if claimed_job_ids.contains(&job.id) {
            job.last_skipped_at = Some(claimed_iso.clone());
            continue;
        }
        let dispatch = AgentCronDispatchRecord {
            id: Uuid::new_v4().to_string(),
            job_id: job.id.clone(),
            claimed_at: claimed_iso.clone(),
            scheduled_for,
            owner: owner.identity().clone(),
        };
        owner.start_running(&dispatch.id);
        dispatches.push(AgentCronDispatch {
            id: dispatch.id.clone(),
            job: job.clone(),
        });
        state.dispatches.push(dispatch);
    }
    dispatches
}

/// Clear the claims `owner` may clear (its own with no live run, or a
/// dead owner's). An active job whose claim is cleared records the
/// interruption; a one-shot is then completed, as its one run ended.
pub(crate) fn recover_interrupted_in_state(
    state: &mut CronJobsState,
    now: u64,
    recovered: &mut Vec<AgentCronJob>,
    owner: &ClaimOwner,
) {
    let mut interrupted_job_ids = std::collections::HashSet::new();
    state.dispatches.retain(|dispatch| {
        let clear = owner.may_clear(&dispatch.owner, &dispatch.id);
        if clear {
            interrupted_job_ids.insert(dispatch.job_id.clone());
        }
        !clear
    });
    for job in &mut state.jobs {
        if !interrupted_job_ids.contains(&job.id) || job.status != JobStatus::Active {
            continue;
        }
        if job.schedule.kind == ScheduleKind::Once {
            job.status = JobStatus::Completed;
            job.next_run_at = None;
        }
        job.last_error = Some("Interrupted before scheduled operation completion".to_string());
        job.updated_at = iso_from_millis(now);
        recovered.push(job.clone());
    }
}

/// Cross-process state locks: lockfile with stale takeover, sorted by path.
pub(crate) fn with_state_locks<T>(paths: &[PathBuf], action: impl FnOnce() -> T) -> Option<T> {
    let mut unique: Vec<PathBuf> = paths.to_vec();
    unique.sort();
    unique.dedup();
    let mut guards: Vec<crate::platform::lock_dir::LockDir> = Vec::new();
    for path in &unique {
        if let Some(parent) = path.parent() {
            let _ = std::fs::create_dir_all(parent);
        }
        // TS `withCronJobsStateLocks`: proper-lockfile on the state file,
        // 100 attempts x 10ms, 30s staleness takeover.
        let stale = std::time::Duration::from_millis(LOCK_STALE_MS);
        match crate::platform::lock_dir::LockDir::acquire_retrying(
            path,
            stale,
            100,
            std::time::Duration::from_millis(10),
        ) {
            Ok(guard) => guards.push(guard),
            Err(error) => {
                tracing::warn!(
                    error = %error,
                    path = %path.display(),
                    "cron jobs state lock not acquired; skipped"
                );
                return None;
            }
        }
    }
    let result = action();
    drop(guards);
    Some(result)
}

/// What a jobs file holds.
enum StateFile {
    Missing,
    Read(CronJobsState),
    /// The file exists but cannot be read or parsed: the reason.
    Corrupt(String),
}

/// The records of one list of the file: `None` when the value is not a list.
fn record_list(value: Option<Value>) -> Option<Vec<Value>> {
    match value {
        None => Some(Vec::new()),
        Some(Value::Array(records)) => Some(records),
        Some(
            Value::Null | Value::Bool(_) | Value::Number(_) | Value::String(_) | Value::Object(_),
        ) => None,
    }
}

/// Split records into those this build reads and those it keeps as they are.
fn split_records<T: serde::de::DeserializeOwned>(records: Vec<Value>) -> (Vec<T>, Vec<Value>) {
    let mut read = Vec::new();
    let mut unread = Vec::new();
    for record in records {
        match T::deserialize(&record) {
            Ok(parsed) => read.push(parsed),
            Err(_) => unread.push(record),
        }
    }
    (read, unread)
}

fn read_state_file(path: &Path) -> StateFile {
    let raw = match std::fs::read_to_string(path) {
        Ok(raw) => raw,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return StateFile::Missing,
        Err(error) => return StateFile::Corrupt(format!("cannot be read: {error}")),
    };
    let Ok(Value::Object(mut object)) = serde_json::from_str::<Value>(&raw) else {
        return StateFile::Corrupt("is not a JSON object".to_string());
    };
    let (Some(jobs), Some(dispatches)) = (
        record_list(object.shift_remove("jobs")),
        record_list(object.shift_remove("dispatches")),
    ) else {
        return StateFile::Corrupt("has jobs or dispatches that are not a list".to_string());
    };
    let (jobs, unread_jobs) = split_records(jobs);
    let (dispatches, unread_dispatches) = split_records(dispatches);
    StateFile::Read(CronJobsState {
        jobs,
        dispatches,
        unread_jobs,
        unread_dispatches,
        other_keys: object,
    })
}

/// Read a jobs file without changing it. A corrupt file reads as no jobs
/// and is reported; the next update moves it aside.
pub(crate) fn read_jobs_state(path: &Path) -> CronJobsState {
    match read_state_file(path) {
        StateFile::Missing => CronJobsState::default(),
        StateFile::Read(state) => state,
        StateFile::Corrupt(reason) => {
            tracing::warn!(path = %path.display(), %reason, "cron jobs file is corrupt; read as no jobs");
            CronJobsState::default()
        }
    }
}

/// Read a jobs file for an update, under its lock. A corrupt file is moved
/// aside and reported, and the update starts from an empty state.
///
/// # Errors
///
/// Returns an error when a corrupt file cannot be moved aside.
pub(crate) fn load_jobs_state(path: &Path) -> anyhow::Result<CronJobsState> {
    match read_state_file(path) {
        StateFile::Missing => Ok(CronJobsState::default()),
        StateFile::Read(state) => {
            let unread = state.unread_jobs.len() + state.unread_dispatches.len();
            if unread > 0 {
                tracing::warn!(
                    path = %path.display(),
                    unread,
                    "cron jobs file holds records this build cannot read; they are kept unchanged"
                );
            }
            Ok(state)
        }
        StateFile::Corrupt(reason) => {
            let name = path
                .file_name()
                .map(|name| name.to_string_lossy().into_owned())
                .unwrap_or_default();
            let aside = path.with_file_name(format!(
                "{name}.corrupt-{}-{}",
                now_millis(),
                Uuid::new_v4().simple()
            ));
            std::fs::rename(path, &aside).map_err(|error| {
                anyhow::anyhow!(
                    "cron jobs file {} {reason} and cannot be moved aside: {error}",
                    path.display()
                )
            })?;
            tracing::warn!(
                path = %path.display(),
                aside = %aside.display(),
                %reason,
                "cron jobs file is corrupt; moved aside"
            );
            Ok(CronJobsState::default())
        }
    }
}

fn write_jobs_file(path: &Path, jobs: &[AgentCronJob]) -> anyhow::Result<()> {
    let mut state = load_jobs_state(path)?;
    state.jobs = merge_fresh_jobs(std::mem::take(&mut state.jobs), jobs.to_vec());
    write_jobs_state(path, &state)
}

pub(crate) fn write_jobs_state(path: &Path, state: &CronJobsState) -> anyhow::Result<()> {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)?;
    }
    let serialized = serde_json::to_string_pretty(state)?;
    // The cron state opts into the shared durable write: TS
    // `writeJobsState` passes `{ mode: 0o600, fsync: true }`. Losing the
    // atomic rename after a power failure rolls back to the previous valid
    // file, which cron recovery already tolerates.
    crate::settings::storage::atomic_write_with(
        path,
        &format!("{serialized}\n"),
        crate::settings::storage::AtomicWriteOptions { fsync: true },
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn jobs_state_write_propagates_physical_failure() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("jobs.json");
        std::fs::create_dir(&path).unwrap();
        assert!(write_jobs_state(&path, &CronJobsState::default()).is_err());
    }

    /// Per-call-site served-path oracle (cron-jobs.ts:1697 passes
    /// `{ mode: 0o600, fsync: true }` — the TS test pins
    /// `expect(options).toMatchObject({ fsync: true, mode: 0o600 })`):
    /// the cron state write opts in and syncs exactly once, landing exactly
    /// `to_string_pretty(state) + "\n"` bytes.
    #[test]
    fn jobs_state_write_keeps_exactly_one_fsync() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("jobs.json");
        let state = CronJobsState::default();
        let expected = format!("{}\n", serde_json::to_string_pretty(&state).unwrap());
        let before = crate::settings::storage::opt_in_fsync_calls();
        write_jobs_state(&path, &state).unwrap();
        assert_eq!(
            crate::settings::storage::opt_in_fsync_calls(),
            before + 1,
            "the cron state write must keep its one opt-in fsync"
        );
        assert_eq!(std::fs::read_to_string(&path).unwrap(), expected);
        assert_eq!(
            crate::platform::perms::file_mode(&path),
            Some(0o600),
            "the durable write keeps the private mode"
        );
    }
}
