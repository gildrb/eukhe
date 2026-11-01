//! State save/load for the cron job store: cross-process file locking
//! (lockfile with stale takeover), the file's read (its records in file
//! order, each read or kept as it is), the write, and the merge write of
//! the operations the compiled core does not decide (heartbeat management,
//! session rebinding, per-session cancels).
//! Section of the port of the `AgentCronJobStore` half of core/cron-jobs.ts.
//!
//! A file that exists but cannot be read or parsed is never overwritten:
//! an update moves it aside (`<name>.corrupt-<ms>-<id>`) and starts from an
//! empty state (the compiled core decides it for the updates of
//! [`super::serve`]). Only a missing file reads as empty. A record that does
//! not parse is kept as it is, where it is.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use serde_json::Value;
use uuid::Uuid;

use super::{now_millis, AgentCronJob, AgentCronJobStore, CronJobsState, Record};
use crate::cron::parse_iso_millis;

const LOCK_STALE_MS: u64 = 30_000;

impl AgentCronJobStore {
    pub(crate) fn read_jobs(&self) -> Vec<AgentCronJob> {
        self.read_states()
            .iter()
            .flat_map(|state| state.read_jobs().cloned().collect::<Vec<_>>())
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
pub(crate) enum StateFile {
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

/// Each record read when this build reads it, else kept as it is.
fn read_records<T: serde::de::DeserializeOwned>(records: Vec<Value>) -> Vec<Record<T>> {
    records
        .into_iter()
        .map(|record| match T::deserialize(&record) {
            Ok(parsed) => Record::Read(parsed),
            Err(_) => Record::Unread(record),
        })
        .collect()
}

pub(crate) fn read_state_file(path: &Path) -> StateFile {
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
    let state = CronJobsState {
        jobs: read_records(jobs),
        dispatches: read_records(dispatches),
        other_keys: object,
    };
    let unread = state.jobs.len() + state.dispatches.len()
        - state.read_jobs().count()
        - state.read_dispatches().count();
    if unread > 0 {
        tracing::warn!(
            path = %path.display(),
            unread,
            "cron jobs file holds records this build cannot read; they are kept unchanged"
        );
    }
    StateFile::Read(state)
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

/// Move the unreadable file at `path` aside (`<name>.corrupt-<ms>-<id>`).
///
/// # Errors
///
/// Returns an error when it cannot be moved.
pub(crate) fn move_aside(path: &Path, reason: &str) -> anyhow::Result<()> {
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
    Ok(())
}

/// Read a jobs file for a merge write, under its lock. A corrupt file is
/// moved aside and reported, and the write starts from an empty state.
///
/// # Errors
///
/// Returns an error when a corrupt file cannot be moved aside.
pub(crate) fn load_jobs_state(path: &Path) -> anyhow::Result<CronJobsState> {
    match read_state_file(path) {
        StateFile::Missing => Ok(CronJobsState::default()),
        StateFile::Read(state) => Ok(state),
        StateFile::Corrupt(reason) => {
            move_aside(path, &reason)?;
            Ok(CronJobsState::default())
        }
    }
}

/// The file's job records with the jobs merged in: each read job replaced
/// by its merged version where it is, a record this build cannot read kept
/// where it is, the merged jobs not in the file appended.
pub(crate) fn merge_records(
    records: &[Record<AgentCronJob>],
    merged: Vec<AgentCronJob>,
) -> Vec<Record<AgentCronJob>> {
    let mut by_id: HashMap<String, AgentCronJob> = merged
        .into_iter()
        .map(|job| (job.id.clone(), job))
        .collect();
    let mut out: Vec<Record<AgentCronJob>> = records
        .iter()
        .filter_map(|record| match record {
            Record::Read(job) => by_id.remove(&job.id).map(Record::Read),
            Record::Unread(value) => Some(Record::Unread(value.clone())),
        })
        .collect();
    let mut added: Vec<AgentCronJob> = by_id.into_values().collect();
    added.sort_by(|left, right| left.id.cmp(&right.id));
    out.extend(added.into_iter().map(Record::Read));
    out
}

fn write_jobs_file(path: &Path, jobs: &[AgentCronJob]) -> anyhow::Result<()> {
    let mut state = load_jobs_state(path)?;
    let merged = merge_fresh_jobs(state.read_jobs().cloned().collect(), jobs.to_vec());
    state.jobs = merge_records(&state.jobs, merged);
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
