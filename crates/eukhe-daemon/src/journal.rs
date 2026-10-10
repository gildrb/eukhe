//! Append-only recovery journals (port of worker-recovery-journal.ts): the
//! worker journal records the latest busy/operation state per session so a
//! replacement can mark interrupted work instead of guessing.

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::collections::HashMap;
use std::fs::{self, File, OpenOptions};
use std::io::{BufWriter, Write};
use std::path::Path;

pub(crate) const RECOVERY_JOURNAL_SUFFIX: &str = ".recovery.jsonl";

pub(crate) fn append_record(path: &Path, record: &Value) -> Result<()> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).with_context(|| format!("create {}", parent.display()))?;
    }
    let mut file = OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)
        .with_context(|| format!("open journal {}", path.display()))?;
    let mut line = serde_json::to_string(record)?;
    line.push('\n');
    file.write_all(line.as_bytes())?;
    eukhe_core::platform::fsync(&file)?;
    Ok(())
}

/// Whether the temp journal's data rides a full sync before the rename
/// onto its path: each variant is the sync class its TS counterpart (or
/// Rust-native owner) carries.
#[derive(Debug, Clone, Copy)]
pub(crate) enum Finalize {
    /// Temp file synced before the rename (TS `writeFileAtomicSync` with
    /// `fsync: true`; the Rust-native terminal-compaction journal keeps
    /// the same belt).
    Synced,
    /// Rename with an UNSYNCED temp (TS
    /// `worker-recovery-journal.ts` compact: `writeFileSync` + plain
    /// `renameSync` — no temp fsync): the OS carries the temp
    /// data to the rename. Durability is owned by the append path — the
    /// compacted form holds only records the append path already made
    /// durable, so a lost compact falls back to the append-only history,
    /// which replays identically.
    Bare,
}

pub(crate) fn rewrite_records(path: &Path, records: &[Value], finalize: Finalize) -> Result<()> {
    let temp = path.with_extension(format!("jsonl.tmp-{}", std::process::id()));
    {
        let file = File::create(&temp).with_context(|| format!("create {}", temp.display()))?;
        let mut writer = BufWriter::new(file);
        for record in records {
            let mut line = serde_json::to_string(record)?;
            line.push('\n');
            writer.write_all(line.as_bytes())?;
        }
        writer.flush()?;
        if !matches!(finalize, Finalize::Bare) {
            writer.get_ref().sync_all()?;
        }
    }
    fs::rename(&temp, path).with_context(|| format!("persist {}", path.display()))?;
    Ok(())
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct WorkerRecoveryRecord {
    pub active_session_id: String,
    pub session_id: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub session_file: Option<String>,
    pub busy: bool,
    pub operation: String,
    pub recorded_at: String,
}

fn parse_worker_records(path: &Path) -> Result<HashMap<String, WorkerRecoveryRecord>> {
    let mut latest = HashMap::new();
    let Ok(content) = fs::read_to_string(path) else {
        return Ok(latest);
    };
    for line in content.lines() {
        if line.is_empty() {
            continue;
        }
        let Ok(record) = serde_json::from_str::<WorkerRecoveryRecord>(line) else {
            continue;
        };
        latest.insert(record.active_session_id.clone(), record);
    }
    Ok(latest)
}

/// Port of `WorkerRecoveryJournal`: latest busy/operation per active session
/// (the durable session resumes its own queue; no queue snapshot rides here).
pub struct WorkerRecoveryJournal {
    path: std::path::PathBuf,
    latest: HashMap<String, WorkerRecoveryRecord>,
}

impl WorkerRecoveryJournal {
    /// Open the worker journal at `path` (creating the parent directory as
    /// needed) and load the latest busy records and queue snapshots.
    ///
    /// # Errors
    ///
    /// Returns an error when the parent directory cannot be created, or
    /// when the journal exists but the queue-snapshot pass cannot read it
    /// (a missing journal loads as empty).
    pub fn open(path: &Path) -> Result<Self> {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)?;
        }
        Ok(WorkerRecoveryJournal {
            path: path.to_path_buf(),
            latest: parse_worker_records(path)?,
        })
    }

    /// Read the latest worker record per active session straight from a
    /// journal file.
    ///
    /// # Errors
    ///
    /// Never errors: a missing or unreadable journal reads as an empty
    /// set (the `Result` wrapper keeps the reading seam uniform).
    pub fn read_latest(path: &Path) -> Result<Vec<WorkerRecoveryRecord>> {
        Ok(parse_worker_records(path)?.into_values().collect())
    }

    /// Does the journal prove live work at the worker's last exit? A plain
    /// supervisor startup adopts a dead worker only when this holds (a
    /// restart must not mass-revive historical sessions): a latest `busy`
    /// record marks an in-flight turn or an admitted-but-undelivered
    /// prompt/queue lane. An unreadable journal proves nothing —
    /// uncertainty must not revive a session.
    #[must_use]
    pub fn read_interrupted(path: &Path) -> bool {
        Self::read_latest(path).is_ok_and(|records| records.iter().any(|record| record.busy))
    }

    /// The newest `busy` record's `recorded_at`, when the journal proves
    /// live work: the timestamp the boot-revival gate ages the evidence
    /// against (an old busy record is residue of an era that already
    /// ended, not interrupted work this boot must heal). A journal with
    /// no busy record answers `None`.
    #[must_use]
    pub fn latest_busy_recorded_at(path: &Path) -> Option<String> {
        Self::read_latest(path)
            .ok()?
            .iter()
            .filter(|record| record.busy)
            .map(|record| record.recorded_at.clone())
            .max()
    }

    /// Settle every busy session to idle with `operation` (the give-up
    /// belt): a supervisor that gave up on a worker records the verdict
    /// in the same journal a later boot would read as revival evidence —
    /// stale busy evidence must not outlive the give-up that superseded
    /// it, or every boot re-storms the slot the cap already condemned.
    ///
    /// # Errors
    ///
    /// Returns an error when the journal cannot be opened or a settle
    /// record cannot be appended.
    pub fn settle_busy_records(path: &Path, operation: &str) -> Result<()> {
        let mut journal = Self::open(path)?;
        let busy: Vec<WorkerRecoveryRecord> = journal
            .get_latest()
            .into_iter()
            .filter(|record| record.busy)
            .collect();
        for record in busy {
            journal.record(
                &record.active_session_id,
                &record.session_id,
                record.session_file.as_deref(),
                false,
                operation,
            )?;
        }
        Ok(())
    }

    /// Record the latest busy/operation state for an active session; an
    /// unchanged record is skipped.
    ///
    /// # Errors
    ///
    /// Returns an error when the record cannot be serialized or appended,
    /// or when the all-idle compaction fails.
    pub fn record(
        &mut self,
        active_session_id: &str,
        session_id: &str,
        session_file: Option<&str>,
        busy: bool,
        operation: &str,
    ) -> Result<()> {
        if let Some(previous) = self.latest.get(active_session_id) {
            if previous.busy == busy
                && previous.operation == operation
                && previous.session_file.as_deref() == session_file
            {
                return Ok(());
            }
        }
        let record = WorkerRecoveryRecord {
            active_session_id: active_session_id.to_string(),
            session_id: session_id.to_string(),
            session_file: session_file.map(str::to_string),
            busy,
            operation: operation.to_string(),
            recorded_at: crate::util::now_iso(),
        };
        append_record(&self.path, &serde_json::to_value(&record)?)?;
        self.latest.insert(active_session_id.to_string(), record);
        // TS parity: the all-idle check includes the just-landed record
        // (TS `record` runs `[...this.latest.values()].every(!busy)`
        // AFTER `set`). Checking before the insert let the session's own
        // busy admission record block its settle's compaction, so a
        // single-session journal never compacted and grew append-only
        // for the session's lifetime; the compaction now fires at every
        // changed-idle record like TS, keeping the file bounded.
        if self.latest.values().all(|entry| !entry.busy) {
            self.compact()?;
        }
        Ok(())
    }

    #[must_use]
    pub fn get_latest(&self) -> Vec<WorkerRecoveryRecord> {
        self.latest.values().cloned().collect()
    }

    fn compact(&self) -> Result<()> {
        let records: Vec<Value> = self
            .latest
            .values()
            .map(serde_json::to_value)
            .collect::<std::result::Result<_, _>>()?;
        rewrite_records(&self.path, &records, Finalize::Bare)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn temp_path(name: &str) -> std::path::PathBuf {
        let dir =
            std::env::temp_dir().join(format!("eukhe-daemon-journal-{}", uuid::Uuid::new_v4()));
        fs::create_dir_all(&dir).unwrap();
        dir.join(name)
    }

    #[test]
    fn worker_journal_keeps_latest_per_session() {
        let path = temp_path("worker.recovery.jsonl");
        let mut journal = WorkerRecoveryJournal::open(&path).unwrap();
        journal
            .record("s1", "sess1", Some("/a.jsonl"), true, "prompt")
            .unwrap();
        journal.record("s2", "sess2", None, false, "ready").unwrap();
        journal
            .record("s1", "sess1", Some("/a.jsonl"), false, "idle")
            .unwrap();
        let latest = WorkerRecoveryJournal::read_latest(&path).unwrap();
        assert_eq!(latest.len(), 2);
        let s1 = latest.iter().find(|r| r.active_session_id == "s1").unwrap();
        assert!(!s1.busy);
        let _ = fs::remove_dir_all(path.parent().unwrap());
    }

    #[test]
    fn worker_journal_interrupted_evidence_tracks_latest_busy() {
        let path = temp_path("interrupted.recovery.jsonl");
        let mut journal = WorkerRecoveryJournal::open(&path).unwrap();
        // Idle sessions prove nothing: no interrupted work to revive.
        journal
            .record("s1", "sess1", None, false, "shutdown")
            .unwrap();
        journal.record("s2", "sess2", None, false, "ready").unwrap();
        assert!(!WorkerRecoveryJournal::read_interrupted(&path));
        // One busy session is durable evidence of interrupted work.
        journal
            .record("s2", "sess2", Some("/b.jsonl"), true, "create")
            .unwrap();
        assert!(WorkerRecoveryJournal::read_interrupted(&path));
        // The latest record per session decides: s2 settles back to idle.
        journal
            .record("s2", "sess2", None, false, "shutdown")
            .unwrap();
        assert!(!WorkerRecoveryJournal::read_interrupted(&path));
        let _ = fs::remove_dir_all(path.parent().unwrap());
    }

    /// TS parity oracle: a single session's settle compacts (the post-
    /// insert all-idle check). The OLD pre-insert check let the session's
    /// own busy admission record block the compaction, so a single-session
    /// journal grew append-only forever; TS compacts at every changed-idle
    /// record and so does the port now.
    #[test]
    fn worker_journal_settle_compacts_single_session() {
        let path = temp_path("settle-compacts.recovery.jsonl");
        let mut journal = WorkerRecoveryJournal::open(&path).unwrap();
        // Two busy/idle cycles through the plain `record` path: the first
        // settle compacts to one line, so the second admission starts from
        // a one-line file (two lines mid-flight, one after the settle) —
        // without the settle compaction the file would grow 2 lines per
        // cycle.
        journal
            .record("s1", "sess1", Some("/a.jsonl"), true, "prompt_accepted")
            .unwrap();
        journal
            .record("s1", "sess1", Some("/a.jsonl"), false, "turn_end")
            .unwrap();
        assert_eq!(
            fs::read_to_string(&path).unwrap().lines().count(),
            1,
            "the first settle compacted to the latest record"
        );
        journal
            .record("s1", "sess1", Some("/a.jsonl"), true, "prompt_accepted")
            .unwrap();
        assert_eq!(
            fs::read_to_string(&path).unwrap().lines().count(),
            2,
            "the second admission grows the compacted file"
        );
        journal
            .record("s1", "sess1", Some("/a.jsonl"), false, "turn_end")
            .unwrap();
        // The settle compacted: the file holds exactly the latest record.
        let content = fs::read_to_string(&path).unwrap();
        let lines: Vec<&str> = content.lines().filter(|l| !l.trim().is_empty()).collect();
        assert_eq!(lines.len(), 1, "the settle compacts to the latest record");
        let record: Value = serde_json::from_str(lines[0]).unwrap();
        assert_eq!(record["busy"], false);
        assert_eq!(record["operation"], "turn_end");
        // The compacted journal replays the same latest state.
        let reopened = WorkerRecoveryJournal::open(&path).unwrap();
        let latest = reopened.get_latest();
        assert_eq!(latest.len(), 1);
        assert!(!latest[0].busy);
        assert!(!WorkerRecoveryJournal::read_interrupted(&path));
        let _ = fs::remove_dir_all(path.parent().unwrap());
    }

    /// An unchanged verdict appends nothing and never compacts (TS
    /// `record` early-returns before its compaction check).
    #[test]
    fn worker_journal_unchanged_verdict_does_not_compact() {
        let path = temp_path("unchanged-nocompact.recovery.jsonl");
        let mut journal = WorkerRecoveryJournal::open(&path).unwrap();
        journal
            .record("s1", "sess1", None, true, "run_started")
            .unwrap();
        journal
            .record("s1", "sess1", None, false, "run_ended")
            .unwrap();
        let lines_after_settle = fs::read_to_string(&path).unwrap().lines().count();
        journal
            .record("s1", "sess1", None, false, "run_ended")
            .unwrap();
        let lines_after_unchanged = fs::read_to_string(&path).unwrap().lines().count();
        assert_eq!(lines_after_unchanged, lines_after_settle);
        let _ = fs::remove_dir_all(path.parent().unwrap());
    }

    #[test]
    fn worker_journal_missing_or_unreadable_file_is_not_interrupted() {
        let path = temp_path("missing.recovery.jsonl");
        // No journal: no evidence, so no revival on uncertainty.
        assert!(!WorkerRecoveryJournal::read_interrupted(&path));
        std::fs::write(&path, "not json").unwrap();
        assert!(!WorkerRecoveryJournal::read_interrupted(&path));
        let _ = fs::remove_dir_all(path.parent().unwrap());
    }
}
