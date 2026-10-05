//! Orphan-process journal: how the host tracks `bash()` children a kernel left
//! behind, so a killed/crashed kernel cannot leak process groups.
//!
//! The kernel manager hands every kernel it spawns its own journal file
//! through `EUKHE_INTERNAL_ORPHAN_PROCESS_JOURNAL`; the Python runtime
//! journals every `bash()` process group there under the kernel pid
//! (`kernelPid`). `bash()` groups run in their own sessions, so a kernel
//! killed without running its shutdown hook leaves them alive: the host
//! reaps them from the journal at teardown and deletes the file.
//!
//! Ported from `core/orphan-process-journal.ts`.

use std::collections::HashMap;
use std::path::Path;

/// Environment variable naming the journal file.
pub const ORPHAN_PROCESS_JOURNAL_ENV: &str = "EUKHE_INTERNAL_ORPHAN_PROCESS_JOURNAL";

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ActiveOrphanProcess {
    pub pid: i32,
    pub kernel_pid: Option<i32>,
    /// Missing on identity-free records: old journals or host writes whose
    /// start-id query failed. Identity-free records cannot prove the pid still
    /// names the journaled process; on POSIX the group-scoped kill stays
    /// best-effort safe, so they may still be reaped.
    pub process_start_id: Option<String>,
}

/// Pid-reuse identity (`proc:<starttime>`), shared with eukhe-daemon through
/// `eukhe_types::platform::process`.
#[must_use]
pub fn get_process_start_id(pid: i32) -> Option<String> {
    if pid <= 0 {
        return None;
    }
    eukhe_types::platform::process::process_start_id(pid as u32)
}

/// Read the still-active orphan processes recorded by this host process.
///
/// # Errors
///
/// Returns an error when the journal file cannot be read (a missing file is
/// an empty record; malformed or partial lines are skipped).
///
/// # Panics
///
/// The `pid` field of a record is unwrapped, but only after the validity
/// filter guarantees it is a positive integer, so the unwraps are
/// unreachable.
pub fn read_active_orphan_processes(path: &Path) -> anyhow::Result<Vec<ActiveOrphanProcess>> {
    let owner_pid = i64::from(std::process::id());
    let contents = match std::fs::read_to_string(path) {
        Ok(c) => c,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(Vec::new()),
        Err(e) => return Err(e.into()),
    };
    let mut latest: HashMap<i64, serde_json::Value> = HashMap::new();
    for line in contents.split('\n') {
        if line.is_empty() {
            continue;
        }
        let Ok(record) = serde_json::from_str::<serde_json::Value>(line) else {
            // A crash can truncate only the final append.
            continue;
        };
        let valid = record["version"] == 1
            && record["pid"].as_i64().is_some_and(|p| p > 0)
            && record["ownerPid"].as_i64() == Some(owner_pid)
            && record["active"].is_boolean()
            && record["recordedAt"].is_string();
        if valid {
            latest.insert(record["pid"].as_i64().unwrap(), record);
        }
    }
    let mut out: Vec<ActiveOrphanProcess> = latest
        .into_values()
        .filter(|record| record["active"].as_bool() == Some(true))
        .map(|record| ActiveOrphanProcess {
            pid: record["pid"].as_i64().unwrap() as i32,
            kernel_pid: record["kernelPid"].as_i64().map(|p| p as i32),
            process_start_id: record["processStartId"].as_str().map(str::to_string),
        })
        .collect();
    out.sort_by_key(|o| o.pid);
    Ok(out)
}

/// True when the record's pid identity still matches the live process, so
/// killing it cannot hit a reused pid.
#[must_use]
pub fn is_orphan_process_identity_current(orphan: &ActiveOrphanProcess) -> bool {
    match &orphan.process_start_id {
        None => false,
        Some(recorded) => get_process_start_id(orphan.pid).as_deref() == Some(recorded.as_str()),
    }
}

fn should_reap(orphan: &ActiveOrphanProcess) -> bool {
    match orphan.process_start_id {
        // Identity-free records: POSIX keeps the best-effort kill.
        None => true,
        Some(_) => is_orphan_process_identity_current(orphan),
    }
}

/// Kill a journaled orphan: its process group first (`bash()` children are
/// group-contained), then the bare pid.
#[must_use]
pub fn kill_orphan_process(pid: i32) -> bool {
    crate::platform::process::kill_process_group_or_pid(pid)
}

/// Kill the still-active `bash()` children `journal` holds for the given
/// kernel pid, then delete the journal: its kernel is gone, so nothing
/// appends to it again. A journal that was never created (the kernel ran
/// no `bash()`) is an empty record.
///
/// # Errors
///
/// Returns an error when the journal exists but cannot be read or removed.
pub fn reap_kernel_orphan_processes(journal: &Path, kernel_pid: i32) -> anyhow::Result<()> {
    for orphan in read_active_orphan_processes(journal)? {
        if orphan.kernel_pid != Some(kernel_pid) || orphan.pid == kernel_pid {
            continue;
        }
        if !should_reap(&orphan) {
            continue;
        }
        // `false` means the group is already gone: nothing left to reap.
        let _ = kill_orphan_process(orphan.pid);
    }
    match std::fs::remove_file(journal) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(error.into()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn process_start_id_reads_the_platform_ladder() {
        // Linux answers from /proc (`proc:`); macOS/BSD answer
        // `ps:<lstart>` - the same ladder TS `getProcessStartId` walks.
        let id = get_process_start_id(std::process::id() as i32);
        let id = id.expect("own pid must be readable");
        assert!(id.starts_with("proc:") || id.starts_with("ps:"));
    }
}
