//! The rules of an append-only log of lines, decided by the compiled Bend
//! core (`bend/log.bend`, entry `bend/ffi_log.bend`; laws `laws/log.bend`):
//! what an open does with a file ([`tail`]), and the steps a storage does
//! at open and per commit ([`Plan`]). The storage reads the facts and does
//! the steps: a session's commit log (`main.jsonl`, eukhe-durable's
//! `JsonlStorage`), and each account file of a budget's ledger
//! (eukhe-budget's `Ledger`: a stamped storage whose commits touch no
//! sidecar file; laws `ledger_ack_durable`, `ledger_kept_flushes_once`).

use crate::wire::{Reader, WireError, Writer};
use crate::{call, Entry, Error, Stepper};

/// What an open does with a file (`Lg.Tail`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Tail {
    /// Every byte lies in a complete line: read them all.
    Whole,
    /// The bytes after the last newline are a torn tail: cut the file to
    /// its first `n` bytes, then read them.
    Torn(usize),
    /// No file has these facts (a newline at or past its end).
    Odd,
}

/// What an open does with a file of `len` bytes whose last newline is at
/// the index `last` (`Lg.tail`).
///
/// # Errors
///
/// [`Error`] only from an inconsistent build (see [`crate::expect_core`]).
pub fn tail(len: usize, last: Option<usize>) -> Result<Tail, Error> {
    let mut request = Writer::new();
    request.count(len);
    match last {
        Some(index) => request.some().count(index),
        None => request.none(),
    };
    let reply = call(Entry::Log, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let tag = reader.tag_of(3, "an open of a file")?;
    let tail = if tag == 0 {
        Tail::Whole
    } else if tag == 1 {
        Tail::Torn(reader.count()?)
    } else {
        Tail::Odd
    };
    reader.end()?;
    Ok(tail)
}

/// A step of a storage (`Lg.Act`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Act {
    /// Flush the storage directory's parent (the storage directory's entry).
    FlushParent,
    /// Append the records of the commit's sidecar file at this index.
    AppendSide(usize),
    /// Flush the commit's sidecar file at this index.
    FlushSide(usize),
    /// Flush the storage directory (its files' entries).
    FlushDir,
    /// Append the commit's marker to `main.jsonl`.
    AppendMain,
    /// Flush `main.jsonl`.
    FlushMain,
    /// Acknowledge the commit.
    Ack,
    /// Link the storage's stamp to `main.jsonl`: its directory entry and
    /// the storage directory's are durable.
    Stamp,
}

fn read_acts(reply: &str) -> Result<Vec<Act>, WireError> {
    let mut reader = Reader::reply(reply)?;
    let count = reader.count()?;
    let mut acts = Vec::new();
    for _ in 0..count {
        let tag = reader.tag_of(8, "a step of the plan")?;
        acts.push(if tag == 0 {
            Act::FlushParent
        } else if tag == 1 {
            Act::AppendSide(reader.count()?)
        } else if tag == 2 {
            Act::FlushSide(reader.count()?)
        } else if tag == 3 {
            Act::FlushDir
        } else if tag == 4 {
            Act::AppendMain
        } else if tag == 5 {
            Act::FlushMain
        } else if tag == 6 {
            Act::Ack
        } else {
            Act::Stamp
        });
    }
    reader.end()?;
    Ok(acts)
}

/// How a storage opens (`Lr.How`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Open {
    /// Nothing is flushed.
    Unsynced,
    /// Every write is flushed before it is acknowledged.
    Synced,
    /// Synced, and a stamp keeps on disk that the directory entries of
    /// `main.jsonl` and of the storage directory are durable: `kept` when
    /// the stamp names `main.jsonl`, so the open flushes no directory.
    Stamped {
        /// The stamp names `main.jsonl`.
        kept: bool,
    },
}

/// The plan of one storage: the compiled core's stepper, which keeps
/// whether the storage syncs, whether `main.jsonl`'s directory entry is
/// durable and whether it stamps it (`Lg.Store`).
#[derive(Debug)]
pub struct Plan {
    core: Stepper,
}

impl Plan {
    /// The plan of a storage opened as `open` says, and the steps of its
    /// open (`Lg.Store.open`).
    ///
    /// # Errors
    ///
    /// [`Error`] only from an inconsistent build (see [`crate::expect_core`]).
    pub fn open(open: Open) -> Result<(Plan, Vec<Act>), Error> {
        let mut request = Writer::new();
        match open {
            Open::Unsynced => request.tag(0),
            Open::Synced => request.tag(1),
            Open::Stamped { kept } => request.tag(2).bool(kept),
        };
        let (core, reply) = Stepper::open(Entry::Log, &request.finish()?)?;
        Ok((Plan { core }, read_acts(&reply)?))
    }

    /// The steps of a commit whose sidecar files have durable directory
    /// entries as `durable` says, in the commit's order (`Lg.Store.commit`).
    ///
    /// # Errors
    ///
    /// [`Error`] only from an inconsistent build (see [`crate::expect_core`]).
    pub fn commit(&mut self, durable: &[bool]) -> Result<Vec<Act>, Error> {
        let mut request = Writer::new();
        request.count(durable.len());
        for &entry in durable {
            request.bool(entry);
        }
        let reply = self.core.step(&request.finish()?)?;
        Ok(read_acts(&reply)?)
    }
}

#[cfg(test)]
mod tests {
    use super::{tail, Act, Open, Plan, Tail};
    use crate::wire::NAT_MAX;

    #[test]
    fn an_open_asks_the_compiled_core() {
        assert_eq!(tail(10, Some(4)).unwrap(), Tail::Torn(5));
    }

    /// The laws of `tail` quantify over unbounded Nats; the runtime's Nat
    /// stops at 2^48 - 1. These are the sizes Rust sends: a 128 KiB file and
    /// files of the largest length the wire carries.
    #[test]
    fn an_open_of_any_size_the_wire_carries() {
        let max = usize::try_from(NAT_MAX).unwrap();
        assert_eq!(tail(131_072, Some(131_071)).unwrap(), Tail::Whole);
        assert_eq!(tail(max, Some(max - 1)).unwrap(), Tail::Whole);
        assert_eq!(tail(max, Some(max - 2)).unwrap(), Tail::Torn(max - 1));
        assert_eq!(tail(max, Some(max)).unwrap(), Tail::Odd);
        assert_eq!(tail(max, None).unwrap(), Tail::Torn(0));
    }

    #[test]
    fn a_plan_asks_the_compiled_core() {
        let (mut plan, opening) = Plan::open(Open::Synced).unwrap();
        assert_eq!(opening, vec![Act::FlushParent]);
        assert_eq!(
            plan.commit(&[true, false]).unwrap(),
            vec![
                Act::AppendSide(0),
                Act::AppendSide(1),
                Act::FlushSide(0),
                Act::FlushSide(1),
                Act::FlushDir,
                Act::AppendMain,
                Act::FlushMain,
                Act::FlushDir,
                Act::Ack,
            ]
        );
    }

    /// Commits with no sidecar file: the first of an open also makes the
    /// file's directory entry durable; without fsync nothing is flushed.
    #[test]
    fn a_plan_of_commits_without_sidecars() {
        let (mut plan, opening) = Plan::open(Open::Synced).unwrap();
        assert_eq!(opening, vec![Act::FlushParent]);
        assert_eq!(
            plan.commit(&[]).unwrap(),
            vec![Act::AppendMain, Act::FlushMain, Act::FlushDir, Act::Ack]
        );
        assert_eq!(
            plan.commit(&[]).unwrap(),
            vec![Act::AppendMain, Act::FlushMain, Act::Ack]
        );
        let (mut unsynced, opening) = Plan::open(Open::Unsynced).unwrap();
        assert_eq!(opening, Vec::new());
        assert_eq!(
            unsynced.commit(&[]).unwrap(),
            vec![Act::AppendMain, Act::Ack]
        );
    }

    /// A ledger's account file: a stamped storage. One its stamp does not
    /// name flushes both directories and links the stamp before its first
    /// ack; one its stamp names flushes only the file, once per record.
    #[test]
    fn a_plan_of_a_stamped_storage() {
        let (mut fresh, opening) = Plan::open(Open::Stamped { kept: false }).unwrap();
        assert_eq!(opening, vec![Act::FlushParent]);
        assert_eq!(
            fresh.commit(&[]).unwrap(),
            vec![
                Act::AppendMain,
                Act::FlushMain,
                Act::FlushDir,
                Act::Stamp,
                Act::Ack
            ]
        );
        assert_eq!(
            fresh.commit(&[]).unwrap(),
            vec![Act::AppendMain, Act::FlushMain, Act::Ack]
        );
        let (mut kept, opening) = Plan::open(Open::Stamped { kept: true }).unwrap();
        assert_eq!(opening, Vec::new());
        for _ in 0..2 {
            assert_eq!(
                kept.commit(&[]).unwrap(),
                vec![Act::AppendMain, Act::FlushMain, Act::Ack]
            );
        }
    }
}
