//! State save/load for the cron job store: cross-process file locking
//! (lockfile with stale takeover), state read/write/merge helpers, and the
//! passes over a whole file (a claim pass, a recovery; the finish step is
//! in [`super::jobs`]). The compiled core decides each pass record by
//! record (`eukhe_bend::rules::cron`, `bend/cron_file.bend`): which jobs a
//! claim pass claims, which claim records stay, what each job becomes. This
//! file gathers the facts (a key per job id, whose each claim is) and
//! applies the answers. Section of the port of the `AgentCronJobStore`
//! half of core/cron-jobs.ts.
//!
//! A file that exists but cannot be read or parsed: the compiled core
//! decides (`rules::cron::moves_aside`) that an update moves it aside
//! (`<name>.corrupt-<ms>-<id>`) and starts from an empty state, and a read
//! leaves it and reads no jobs. Only a missing file reads as empty. A
//! record that does not parse is kept as its bytes: the passes answer
//! for the claim records too, and no pass changes a job record it cannot
//! read.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use eukhe_bend::rules::cron::{self as rule, Back, Hold, Reading, Slot, Took};
use serde_json::Value;
use uuid::Uuid;

use super::facts::{fact_of, job_status, next_text, next_text_at};
use super::owner::ClaimOwner;
use super::{
    iso_from_millis, now_millis, AgentCronDispatch, AgentCronDispatchRecord, AgentCronJob,
    AgentCronJobStore, CronJobsState,
};
use crate::cron::parse_iso_millis;

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

/// The key of each job id of `jobs`: the place of its first job record.
/// Equal keys are equal job ids; the compiled core matches a claim record
/// to its job by key.
pub(crate) fn id_keys(jobs: &[AgentCronJob]) -> HashMap<&str, u64> {
    let mut keys = HashMap::new();
    for (at, job) in (0u64..).zip(jobs) {
        keys.entry(job.id.as_str()).or_insert(at);
    }
    keys
}

/// The job records of a file as the compiled core reads them.
pub(crate) fn slots_of(jobs: &[AgentCronJob], keys: &HashMap<&str, u64>) -> Vec<Slot> {
    jobs.iter()
        .map(|job| Slot {
            key: keys[job.id.as_str()],
            fact: fact_of(job),
        })
        .collect()
}

/// A claim pass (the compiled core decides it: `rule::take_all`): each job
/// becomes what the core answers; a job it claims gets one claim record,
/// naming `owner` and counting as a live run of it.
pub(crate) fn claim_due_in_state(
    state: &mut CronJobsState,
    due_at: u64,
    claimed_at: u64,
    owner: &ClaimOwner,
) -> Vec<AgentCronDispatch> {
    let claimed_iso = iso_from_millis(claimed_at);
    let answers = {
        let keys = id_keys(&state.jobs);
        let claims: Vec<Option<u64>> = state
            .dispatches
            .iter()
            .map(|dispatch| keys.get(dispatch.job_id.as_str()).copied())
            .collect();
        rule::take_all(&slots_of(&state.jobs, &keys), &claims, due_at, claimed_at)
    };
    let mut dispatches = Vec::new();
    for (job, took) in state.jobs.iter_mut().zip(answers) {
        let (next, claim) = match took {
            Took::Keep => continue,
            Took::Roll(next) => (next, false),
            Took::Claim(next) => (next, true),
        };
        let scheduled_for = job.next_run_at.clone().unwrap_or_default();
        job.next_run_at = next_text(job, next, claimed_at).ok().flatten();
        job.updated_at.clone_from(&claimed_iso);
        if !claim {
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

/// A recovery (the compiled core decides it: `rule::recover_all`, from
/// whose each claim record is): the claim records it clears go (this
/// process's own with no live run, a dead owner's); an active job whose
/// claim was cleared records the interruption, a one-shot is then
/// completed, as its one run ended.
pub(crate) fn recover_interrupted_in_state(
    state: &mut CronJobsState,
    now: u64,
    recovered: &mut Vec<AgentCronJob>,
    owner: &ClaimOwner,
) {
    let swept = {
        let keys = id_keys(&state.jobs);
        let claims: Vec<Hold> = state
            .dispatches
            .iter()
            .map(|dispatch| Hold::Held {
                key: keys.get(dispatch.job_id.as_str()).copied(),
                who: owner.who(&dispatch.owner, &dispatch.id),
            })
            .chain(state.unread_dispatches.iter().map(|_| Hold::Unheld))
            .collect();
        rule::recover_all(&slots_of(&state.jobs, &keys), &claims)
    };
    let mut keep = swept.keep.into_iter();
    state.dispatches.retain(|_| keep.next().unwrap_or(true));
    state
        .unread_dispatches
        .retain(|_| keep.next().unwrap_or(true));
    for (job, back) in state.jobs.iter_mut().zip(swept.jobs) {
        let Back::Interrupted { status, next } = back else {
            continue;
        };
        job.status = job_status(status);
        job.next_run_at = next_text_at(job, next);
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

/// A corrupt jobs file read for `reading`: the compiled core decides
/// whether it is moved aside (an update) or left in place (a read); either
/// way the file reads as no jobs.
///
/// # Errors
///
/// Returns an error when the file cannot be moved aside.
fn open_corrupt(path: &Path, reason: &str, reading: Reading) -> anyhow::Result<CronJobsState> {
    if !rule::moves_aside(reading) {
        tracing::warn!(path = %path.display(), %reason, "cron jobs file is corrupt; read as no jobs");
        return Ok(CronJobsState::default());
    }
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

/// Read a jobs file without changing it. A corrupt file reads as no jobs
/// and is reported.
pub(crate) fn read_jobs_state(path: &Path) -> CronJobsState {
    match read_state_file(path) {
        StateFile::Missing => CronJobsState::default(),
        StateFile::Read(state) => state,
        StateFile::Corrupt(reason) => {
            open_corrupt(path, &reason, Reading::Read).unwrap_or_else(|error| {
                tracing::warn!(%error, "cron jobs file is corrupt; read as no jobs");
                CronJobsState::default()
            })
        }
    }
}

/// Read a jobs file for an update, under its lock. A corrupt file is
/// handled as the compiled core decides for an update (moved aside, the
/// update starting from an empty state).
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
        StateFile::Corrupt(reason) => open_corrupt(path, &reason, Reading::Update),
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
