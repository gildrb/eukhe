//! The process groups a session worker's commands run in, journaled while
//! they run so they die with the worker.
//!
//! Every external command of the `bash` tool and of a user `!` command
//! leads its own process group, so a cancel reaches its whole tree. A
//! worker that dies without its teardown (SIGKILL, a crash, a kill by its
//! supervisor) leaves those groups running: nothing waits for them any
//! more, and the run that resumes in the next worker reads the call as
//! interrupted while the command still runs. The worker records each group
//! here while it runs ([`RunningGroup`]); once the worker is gone its
//! supervisor kills the groups still recorded ([`reap`]), on Linux and
//! macOS alike (the record needs no `/proc` ancestry, which the death
//! loses).
//!
//! One JSON line per change; the latest line of a group wins. A group is
//! recorded with its leader's start identity ([`process_start_id`]) and
//! signaled only while the leader still has it: a pid the system gave to
//! another process since is never signaled (the kernel orphan journal's
//! identity rule). A record without an identity (the platform answered
//! none) is reaped best-effort, as that journal's are. While nothing runs
//! the file is empty, so it never holds more lines than the groups that
//! ran since the last moment nothing did.

use std::collections::HashMap;
use std::fs::{File, OpenOptions};
use std::io::Write as _;
use std::os::unix::fs::OpenOptionsExt as _;
use std::path::Path;
use std::sync::{Mutex, OnceLock, PoisonError};

use serde::{Deserialize, Serialize};

use super::process::process_start_id;

/// One journal line.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
struct Record {
    /// The group id: the pid of its leader, the spawned command.
    pgid: u32,
    /// The leader's start identity when the group was recorded running.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    start_id: Option<String>,
    running: bool,
}

/// This process's open journal and the count of groups it records running.
struct Journal {
    file: File,
    running: usize,
}

static JOURNAL: OnceLock<Mutex<Journal>> = OnceLock::new();

/// Open `path` as this process's group journal (a session worker, once at
/// startup). Until it is open, [`RunningGroup::record`] records nothing.
///
/// # Errors
///
/// The file does not open, or this process already opened its journal.
pub fn open(path: &Path) -> std::io::Result<()> {
    let file = OpenOptions::new()
        .create(true)
        .append(true)
        .mode(0o600)
        .open(path)?;
    JOURNAL
        .set(Mutex::new(Journal { file, running: 0 }))
        .map_err(|_| std::io::Error::other("the process group journal is already open"))
}

/// Append `record`; a failed write loses only this group's protection.
fn append(file: &mut File, record: &Record) {
    let mut line = serde_json::to_vec(record).expect("a journal record serializes");
    line.push(b'\n');
    if let Err(error) = file.write_all(&line) {
        tracing::warn!(%error, pgid = record.pgid, "the process group journal write failed");
    }
}

/// A process group recorded running in the journal until the guard drops.
#[must_use = "the group is recorded only while the guard lives"]
pub struct RunningGroup(Option<u32>);

impl RunningGroup {
    /// Record the group `pgid` leads (a child spawned into a group of its
    /// own: its pid) running. A process with no open journal records
    /// nothing.
    pub fn record(pgid: u32) -> Self {
        let Some(journal) = JOURNAL.get() else {
            return Self(None);
        };
        // The identity read may spawn `ps` (macOS): outside the lock.
        let record = Record {
            pgid,
            start_id: process_start_id(pgid),
            running: true,
        };
        let mut journal = journal.lock().unwrap_or_else(PoisonError::into_inner);
        journal.running += 1;
        append(&mut journal.file, &record);
        Self(Some(pgid))
    }
}

impl Drop for RunningGroup {
    fn drop(&mut self) {
        let (Some(pgid), Some(journal)) = (self.0, JOURNAL.get()) else {
            return;
        };
        let mut journal = journal.lock().unwrap_or_else(PoisonError::into_inner);
        journal.running = journal.running.saturating_sub(1);
        if journal.running > 0 {
            append(
                &mut journal.file,
                &Record {
                    pgid,
                    start_id: None,
                    running: false,
                },
            );
        } else if let Err(error) = journal.file.set_len(0) {
            // Nothing runs: the journal starts over (appends follow the
            // new end).
            tracing::warn!(%error, "the process group journal did not empty");
        }
    }
}

/// Kill the groups the journal at `path` records running (a dead worker's)
/// with SIGKILL, then delete it. A group whose leader no longer has its
/// recorded start identity is left alone. Answers the groups signaled, in
/// order. A missing journal records nothing.
///
/// # Errors
///
/// The journal exists but does not read or delete.
pub fn reap(path: &Path) -> std::io::Result<Vec<u32>> {
    let contents = match std::fs::read_to_string(path) {
        Ok(contents) => contents,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(Vec::new()),
        Err(error) => return Err(error),
    };
    let mut latest: HashMap<u32, Record> = HashMap::new();
    // A kill can cut only the last line short: an unreadable line is skipped.
    for record in contents
        .lines()
        .filter_map(|line| serde_json::from_str::<Record>(line).ok())
    {
        latest.insert(record.pgid, record);
    }
    let mut signaled: Vec<u32> = latest
        .into_values()
        .filter(|record| record.running)
        .filter(|record| match &record.start_id {
            Some(recorded) => process_start_id(record.pgid).as_ref() == Some(recorded),
            None => true,
        })
        .filter_map(|record| {
            // Group 0 is the caller's own and 1 is init's: never a command's.
            let group = i32::try_from(record.pgid).ok().filter(|group| *group > 1)?;
            nix::sys::signal::killpg(
                nix::unistd::Pid::from_raw(group),
                nix::sys::signal::Signal::SIGKILL,
            )
            .ok()
            .map(|()| record.pgid)
        })
        .collect();
    signaled.sort_unstable();
    match std::fs::remove_file(path) {
        Ok(()) => Ok(signaled),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(signaled),
        Err(error) => Err(error),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::process::ExitStatusExt as _;

    /// A child in a group of its own that runs until killed.
    fn group_leader() -> std::process::Child {
        use std::os::unix::process::CommandExt as _;
        std::process::Command::new("sleep")
            .arg("600")
            .process_group(0)
            .spawn()
            .expect("spawn sleep")
    }

    fn line(record: &Record) -> String {
        format!("{}\n", serde_json::to_string(record).unwrap())
    }

    /// The reap kills the groups whose latest line is running with the
    /// leader's identity, and only those, then deletes the journal.
    #[test]
    fn the_reap_kills_the_groups_recorded_running() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("w.groups.jsonl");
        let mut running = group_leader();
        let mut ended = group_leader();
        let mut recycled = group_leader();
        let running_pid = running.id();
        let ended_pid = ended.id();
        let recycled_pid = recycled.id();
        let journal = [
            Record {
                pgid: running_pid,
                start_id: process_start_id(running_pid),
                running: true,
            },
            Record {
                pgid: ended_pid,
                start_id: process_start_id(ended_pid),
                running: true,
            },
            Record {
                pgid: ended_pid,
                start_id: None,
                running: false,
            },
            Record {
                pgid: recycled_pid,
                start_id: Some("proc:another-process".to_string()),
                running: true,
            },
        ]
        .iter()
        .map(line)
        .collect::<String>();
        // The torn last line of a killed writer.
        std::fs::write(&path, format!("{journal}{{\"pgid\":")).unwrap();

        assert_eq!(reap(&path).unwrap(), vec![running_pid]);

        assert_eq!(running.wait().unwrap().signal(), Some(9));
        assert!(!path.exists(), "the reaped journal is deleted");
        for leftover in [&mut ended, &mut recycled] {
            assert_eq!(leftover.try_wait().unwrap(), None, "left alone");
            leftover.kill().unwrap();
            leftover.wait().unwrap();
        }
    }

    #[test]
    fn a_missing_journal_records_nothing() {
        let dir = tempfile::tempdir().unwrap();
        assert_eq!(
            reap(&dir.path().join("none.jsonl")).unwrap(),
            Vec::<u32>::new()
        );
    }
}
