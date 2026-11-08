//! The session's seen-line journal (`eukhe_docs::SeenJournal`):
//! `<storage>/seen-lines.jsonl`, one record per line, appended as lines
//! become seen (one `O_APPEND` write, no fsync: a lost record costs a
//! re-read). The next process of the session (a headless `-c` turn, a
//! worker restart, a resume) loads it at its first edit and restores only
//! the records of the text each file still holds.
//!
//! A line that does not parse (a torn final append, or an append that
//! landed after one) is skipped: it loses only its own lines.

use std::io::Write as _;
use std::path::{Path, PathBuf};

use eukhe_docs::{SeenJournal, SeenRecord};
use serde::{Deserialize, Serialize};

/// The journal's file name in the session's storage directory.
pub(super) const SEEN_LOG_FILE: &str = "seen-lines.jsonl";

/// The journal of one session's storage.
pub(super) struct SeenLog {
    path: PathBuf,
}

impl SeenLog {
    pub(super) fn in_storage(storage_dir: &Path) -> Self {
        Self {
            path: storage_dir.join(SEEN_LOG_FILE),
        }
    }
}

/// One line of the journal.
#[derive(Serialize, Deserialize)]
struct Line {
    path: String,
    tag: String,
    digest: String,
    runs: Vec<(u32, u32)>,
}

impl SeenJournal for SeenLog {
    fn load(&self) -> Vec<SeenRecord> {
        let contents = match std::fs::read(&self.path) {
            Ok(contents) => contents,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Vec::new(),
            Err(error) => {
                tracing::warn!(path = %self.path.display(), %error, "seen-line journal unreadable: no seen lines restored");
                return Vec::new();
            }
        };
        let mut skipped = 0usize;
        let records: Vec<SeenRecord> = contents
            .split(|byte| *byte == b'\n')
            .filter(|line| !line.is_empty())
            .filter_map(|line| {
                let parsed = serde_json::from_slice::<Line>(line).ok();
                skipped += usize::from(parsed.is_none());
                parsed
            })
            .map(|line| SeenRecord {
                path: PathBuf::from(line.path),
                tag: line.tag,
                digest: line.digest,
                runs: line.runs,
            })
            .collect();
        if skipped > 0 {
            tracing::warn!(path = %self.path.display(), skipped, "seen-line journal lines skipped");
        }
        records
    }

    fn append(&self, record: &SeenRecord) {
        // A path that is not UTF-8 has no JSON form: its lines stay in
        // this process.
        let Some(path) = record.path.to_str() else {
            return;
        };
        let line = Line {
            path: path.to_owned(),
            tag: record.tag.clone(),
            digest: record.digest.clone(),
            runs: record.runs.clone(),
        };
        let append = || -> std::io::Result<()> {
            let mut bytes = serde_json::to_vec(&line)?;
            bytes.push(b'\n');
            let mut options = std::fs::OpenOptions::new();
            options.create(true).append(true);
            crate::platform::perms::set_private_mode(&mut options);
            options.open(&self.path)?.write_all(&bytes)
        };
        if let Err(error) = append() {
            tracing::warn!(path = %self.path.display(), %error, "seen-line journal append failed");
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn record(path: &str, tag: &str, runs: Vec<(u32, u32)>) -> SeenRecord {
        SeenRecord {
            path: PathBuf::from(path),
            tag: tag.to_owned(),
            digest: "0123456789abcdef".to_owned(),
            runs,
        }
    }

    /// The records come back in order; a torn line, and the append that
    /// landed after it, are skipped, and the later records still load.
    #[test]
    fn records_round_trip_and_a_torn_line_loses_only_itself() {
        let dir = tempfile::tempdir().expect("dir");
        let log = SeenLog::in_storage(dir.path());
        assert_eq!(log.load(), Vec::new());
        let first = record("/w/a.rs", "AB12", vec![(1, 3), (7, 7)]);
        log.append(&first);
        std::fs::OpenOptions::new()
            .append(true)
            .open(dir.path().join(SEEN_LOG_FILE))
            .expect("open")
            .write_all(b"{\"path\":\"/w/b")
            .expect("torn");
        log.append(&record("/w/b.rs", "CD34", vec![(2, 2)]));
        let last = record("/w/c.rs", "EF56", vec![(4, 9)]);
        log.append(&last);
        assert_eq!(log.load(), vec![first, last]);
    }
}
