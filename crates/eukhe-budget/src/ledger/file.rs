//! An account file held under its exclusive lock: the last record read
//! from its end, each new record appended and synced.

use std::fs::{File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};

use eukhe_types::budget::{BudgetAmounts, BudgetPhase, BudgetReport};
use serde::Deserialize;

use super::{add, step, sub, LedgerError, State};
use crate::record::{Op, Outcome, Record};

/// How many bytes of the file's end one read takes while it looks for the
/// last complete line.
const CHUNK_BYTES: usize = 4096;

/// Whether opening a ledger may create its file.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum OpenMode {
    Existing,
    Create,
}

/// The part of the last record an operation reads: its place and the
/// state (serde skips its op and outcome).
#[derive(Debug, Deserialize)]
pub(super) struct LastRecord {
    seq: u64,
    state: State,
}

/// What follows the last complete line.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum After {
    /// Nothing: the next record goes at the end.
    Nothing,
    /// A line cut short by a crash: it is cut before the next record.
    Torn,
}

/// Where a backward search for the last complete line stands after one
/// chunk.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Search {
    /// The line spans `[start, end)` of the file, its newline last.
    Line { start: u64, end: u64 },
    /// The chunk began at the file's start or holds no line start yet:
    /// read the chunk before it, `end` the end of the line found so far.
    Before { end: Option<u64> },
    /// The file holds no complete line.
    Empty,
}

/// The search after the chunk `bytes` read at `from`, given the end of the
/// last complete line found in the chunks after it, if any.
fn search(bytes: &[u8], from: u64, end: Option<u64>) -> Search {
    let newlines = bytes
        .iter()
        .enumerate()
        .rev()
        .filter(|(_, byte)| **byte == b'\n')
        .map(|(at, _)| from + at as u64 + 1);
    // At most two newlines decide it: the one ending the line, the one
    // before it.
    let found =
        newlines.take(2).fold(
            end.map_or(Found::Nothing, Found::End),
            |found, after| match found {
                Found::Nothing => Found::End(after),
                Found::End(end) => Found::Line { start: after, end },
                Found::Line { start, end } => Found::Line { start, end },
            },
        );
    match (found, from) {
        (Found::Line { start, end }, _) => Search::Line { start, end },
        (Found::End(end), 0) => Search::Line { start: 0, end },
        (Found::End(end), _) => Search::Before { end: Some(end) },
        (Found::Nothing, 0) => Search::Empty,
        (Found::Nothing, _) => Search::Before { end: None },
    }
}

/// The newlines a backward search has passed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Found {
    Nothing,
    /// The newline that ends the last complete line: the position after it.
    End(u64),
    Line {
        start: u64,
        end: u64,
    },
}

/// The file's last complete line as read from its end, and where it ends.
#[derive(Debug)]
struct Tail {
    last: Option<LastRecord>,
    end: u64,
    after: After,
    line_len: usize,
}

/// The tail of `file` (`len` bytes): chunks read backwards until the last
/// complete line is found, then that line parsed from the chunk, or read
/// whole when it began in an earlier chunk.
fn read_tail(path: &Path, mut file: &File, len: u64) -> Result<Tail, LedgerError> {
    let io = |source| LedgerError::Io {
        path: path.to_path_buf(),
        source,
    };
    let mut chunk = [0; CHUNK_BYTES];
    let mut to = len;
    let mut end = None;
    loop {
        let from = to.saturating_sub(CHUNK_BYTES as u64);
        let read = &mut chunk[..usize::try_from(to - from).unwrap_or(CHUNK_BYTES)];
        file.seek(SeekFrom::Start(from)).map_err(io)?;
        file.read_exact(read).map_err(io)?;
        match search(read, from, end) {
            Search::Before { end: found } => {
                end = found;
                to = from;
            }
            Search::Empty => {
                return Ok(Tail {
                    last: None,
                    end: 0,
                    after: if len == 0 {
                        After::Nothing
                    } else {
                        After::Torn
                    },
                    line_len: 0,
                })
            }
            Search::Line { start, end } => {
                let line_len = usize::try_from(end - start - 1).map_err(|_| {
                    io(std::io::Error::new(
                        std::io::ErrorKind::InvalidData,
                        "a ledger record longer than memory",
                    ))
                })?;
                // The line lies in this chunk unless it ends past it.
                let within = usize::try_from(start - from)
                    .ok()
                    .filter(|_| end <= to)
                    .and_then(|at| read.get(at..at + line_len));
                let last = if let Some(line) = within {
                    parse(path, line)?
                } else {
                    let mut line = vec![0; line_len];
                    file.seek(SeekFrom::Start(start)).map_err(io)?;
                    file.read_exact(&mut line).map_err(io)?;
                    parse(path, &line)?
                };
                return Ok(Tail {
                    last: Some(last),
                    end,
                    after: if end == len {
                        After::Nothing
                    } else {
                        After::Torn
                    },
                    line_len,
                });
            }
        }
    }
}

fn parse(path: &Path, line: &[u8]) -> Result<LastRecord, LedgerError> {
    serde_json::from_slice(line).map_err(|error| LedgerError::Corrupt {
        path: path.to_path_buf(),
        line: 0,
        reason: error.to_string(),
    })
}

/// A ledger file held under its exclusive lock: the lock lasts as long as
/// the value.
pub(super) struct Locked {
    path: PathBuf,
    file: File,
    /// The last record, if the file has one.
    last: Option<LastRecord>,
    /// Where the last complete line ends.
    end: u64,
    after: After,
    /// The length of the last line: the next one is about as long.
    line_len: usize,
}

impl Locked {
    fn io(&self, source: std::io::Error) -> LedgerError {
        LedgerError::Io {
            path: self.path.clone(),
            source,
        }
    }

    /// Opens (creating it in [`OpenMode::Create`]) and locks the file,
    /// then reads its last complete line. `None`: the file does not
    /// exist.
    pub(super) fn open(path: &Path, mode: OpenMode) -> Result<Option<Locked>, LedgerError> {
        let io = |source| LedgerError::Io {
            path: path.to_path_buf(),
            source,
        };
        if let (OpenMode::Create, Some(dir)) = (mode, path.parent()) {
            std::fs::create_dir_all(dir).map_err(io)?;
        }
        let file = match OpenOptions::new()
            .read(true)
            .append(true)
            .create(mode == OpenMode::Create)
            .open(path)
        {
            Ok(file) => file,
            Err(error)
                if mode == OpenMode::Existing && error.kind() == std::io::ErrorKind::NotFound =>
            {
                return Ok(None)
            }
            Err(error) => return Err(io(error)),
        };
        file.lock().map_err(io)?;
        let len = file.metadata().map_err(io)?.len();
        let tail = read_tail(path, &file, len)?;
        Ok(Some(Locked {
            path: path.to_path_buf(),
            file,
            last: tail.last,
            end: tail.end,
            after: tail.after,
            line_len: tail.line_len,
        }))
    }

    /// The account's state: the last record's, `None` before the first.
    pub(super) fn state(&self) -> Option<&State> {
        self.last.as_ref().map(|record| &record.state)
    }

    /// The budget as `agent` sees it at `now`, in the account of `owner`.
    pub(super) fn report(&self, owner: &str, agent: &str, now: u64) -> BudgetReport {
        let empty = State::default();
        let state = self.state().unwrap_or(&empty);
        let member = state.members.get(agent);
        let phase = member.map_or(BudgetPhase::Working, |member| member.phase);
        BudgetReport {
            session_id: owner.to_owned(),
            agent_session_id: agent.to_owned(),
            limits: state.limits,
            free: BudgetAmounts {
                time_ms: match state.limits.time_ms {
                    Some(_) => state.account.until.saturating_sub(now),
                    None => 0,
                },
                ..state.account.free
            },
            held: state.account.held(),
            spent: sub(add(state.account.spent, state.tally), state.mark),
            lent: state.account.lent,
            over: state.account.over,
            phase,
            short: match phase {
                BudgetPhase::Working => None,
                BudgetPhase::WrapUp | BudgetPhase::Exhausted => {
                    member.and_then(|member| member.short)
                }
            },
            deadline_ms: state.limits.time_ms.map(|_| state.account.until),
            parent_session_id: state
                .parent
                .as_ref()
                .map(|parent| parent.session_id.clone()),
            kind: state.run.as_ref().map(|run| run.kind),
            sources: state
                .run
                .as_ref()
                .map_or_else(Default::default, |run| run.sources.clone()),
            program_runs: state.program_runs,
            plan: state.plan.clone(),
            next: Some(state.next_run.clone()).filter(|next| !next.is_empty()),
        }
    }

    /// Applies `op` to the state, appends the record (written at `at_ms`)
    /// and syncs it: the file after it, and the core's answer.
    pub(super) fn apply(self, op: Op, at_ms: u64) -> Result<(Locked, Outcome), LedgerError> {
        let empty = State::default();
        let (state, outcome) = step(self.state().unwrap_or(&empty), &op)?;
        let record = Record {
            seq: self.last.as_ref().map_or(0, |record| record.seq + 1),
            at_ms,
            op,
            outcome,
            state,
        };
        let mut line = Vec::with_capacity(self.line_len + 1);
        serde_json::to_writer(&mut line, &record).map_err(|error| LedgerError::Corrupt {
            path: self.path.clone(),
            line: record.seq,
            reason: error.to_string(),
        })?;
        let line_len = line.len();
        line.push(b'\n');
        // A line cut short by a crash is dropped before the next record.
        match self.after {
            After::Torn => self.file.set_len(self.end).map_err(|e| self.io(e))?,
            After::Nothing => {}
        }
        (&self.file).write_all(&line).map_err(|e| self.io(e))?;
        self.file.sync_data().map_err(|e| self.io(e))?;
        // The file's first record: its directory entry is made durable
        // too, or a crash could lose the file with what it acknowledged.
        if let (0, Some(dir)) = (self.end, self.path.parent()) {
            File::open(dir)
                .and_then(|dir| dir.sync_all())
                .map_err(|e| self.io(e))?;
        }
        Ok((
            Locked {
                end: self.end + line.len() as u64,
                after: After::Nothing,
                line_len,
                last: Some(LastRecord {
                    seq: record.seq,
                    state: record.state,
                }),
                ..self
            },
            outcome,
        ))
    }

    /// Applies each of `ops` in order, all at `at_ms`; their answers are
    /// in the states.
    pub(super) fn apply_all(
        self,
        ops: impl IntoIterator<Item = Op>,
        at_ms: u64,
    ) -> Result<Locked, LedgerError> {
        ops.into_iter().try_fold(self, |locked, op| {
            locked.apply(op, at_ms).map(|(locked, _)| locked)
        })
    }
}

/// Removes the link file of `session_id` under `dir`: it draws from no
/// shared account any more. A link that is not there is fine.
pub(super) fn remove_link(dir: &Path, session_id: &str) -> Result<(), LedgerError> {
    let link = dir.join(format!("{session_id}.link"));
    match std::fs::remove_file(&link) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(source) => Err(LedgerError::Io { path: link, source }),
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::*;
    use crate::record::Member;

    /// The last complete line of `text` as the backward search finds it,
    /// chunk by chunk of `size` bytes.
    fn last_line(text: &str, size: usize) -> Option<(u64, u64)> {
        let len = text.len() as u64;
        let (mut to, mut end) = (len, None);
        loop {
            let from = to.saturating_sub(size as u64);
            let bytes = &text.as_bytes()[usize::try_from(from).ok()?..usize::try_from(to).ok()?];
            match search(bytes, from, end) {
                Search::Line { start, end } => return Some((start, end)),
                Search::Empty => return None,
                Search::Before { end: found } => (to, end) = (from, found),
            }
        }
    }

    #[test]
    fn the_last_complete_line_is_found_across_chunks() {
        let long = "x".repeat(10);
        let text = format!("a\n{long}\ntorn");
        let line = Some((2, 2 + 10 + 1));
        for size in [1, 2, 3, 4, 7, 16, 64] {
            assert_eq!(last_line(&text, size), line, "chunk {size}");
        }
        assert_eq!(last_line(&format!("{long}\n"), 3), Some((0, 11)));
        assert_eq!(last_line("torn", 3), None);
        assert_eq!(last_line("", 3), None);
    }

    /// A last record longer than a chunk reads whole, and a torn line
    /// after it is marked to be cut.
    #[test]
    fn a_last_record_longer_than_a_chunk_reads_whole() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("a.jsonl");
        let state = State {
            next_id: 7,
            members: BTreeMap::from([("m".repeat(3 * CHUNK_BYTES), Member::default())]),
            ..State::default()
        };
        let line = serde_json::json!({ "seq": 4, "state": state }).to_string();
        std::fs::write(&path, format!("{{}}\n{line}\n{{\"seq\":5")).unwrap();
        let file = File::open(&path).unwrap();
        let len = file.metadata().unwrap().len();
        let tail = read_tail(&path, &file, len).unwrap();
        let last = tail.last.unwrap();
        assert_eq!((last.seq, last.state), (4, state));
        assert_eq!(
            (tail.end, tail.after, tail.line_len),
            (3 + line.len() as u64 + 1, After::Torn, line.len())
        );
    }
}
