//! The rules of an append-only log of lines, decided by the compiled Bend
//! core (`bend/log.bend`, entry `bend/ffi_log.bend`; laws `laws/log.bend`):
//! what an open does with a file ([`tail`]), and the steps a storage does
//! at open and per commit ([`Plan`]). The storage reads the facts and does
//! the steps: a session's commit log (`main.jsonl`, eukhe-durable's
//! `JsonlStorage`), and each account file of a budget's ledger
//! (eukhe-budget's `Ledger`: commits that touch no sidecar file, one per
//! open; law `ledger_ack_durable`).

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
}

fn read_acts(reply: &str) -> Result<Vec<Act>, WireError> {
    let mut reader = Reader::reply(reply)?;
    let count = reader.count()?;
    let mut acts = Vec::new();
    for _ in 0..count {
        let tag = reader.tag_of(7, "a step of the plan")?;
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
        } else {
            Act::Ack
        });
    }
    reader.end()?;
    Ok(acts)
}

/// Whether a storage flushes (`fsync`) what it writes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fsync {
    /// Every write is flushed before it is acknowledged.
    On,
    /// Nothing is flushed.
    Off,
}

/// The plan of one storage: the compiled core's stepper, which keeps
/// whether the storage syncs and whether `main.jsonl`'s directory entry is
/// durable (`Lg.Store`).
#[derive(Debug)]
pub struct Plan {
    core: Stepper,
}

impl Plan {
    /// The plan of a storage that syncs or not, and the steps of its open
    /// (`Lg.Store.open`).
    ///
    /// # Errors
    ///
    /// [`Error`] only from an inconsistent build (see [`crate::expect_core`]).
    pub fn open(fsync: Fsync) -> Result<(Plan, Vec<Act>), Error> {
        let mut request = Writer::new();
        request.bool(match fsync {
            Fsync::On => true,
            Fsync::Off => false,
        });
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
    use super::{tail, Act, Fsync, Plan, Tail};
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
        let (mut plan, opening) = Plan::open(Fsync::On).unwrap();
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

    /// A ledger's account file: commits with no sidecar file; the first
    /// of an open also makes the file's directory entry durable.
    #[test]
    fn a_plan_of_commits_without_sidecars() {
        let (mut plan, opening) = Plan::open(Fsync::On).unwrap();
        assert_eq!(opening, vec![Act::FlushParent]);
        assert_eq!(
            plan.commit(&[]).unwrap(),
            vec![Act::AppendMain, Act::FlushMain, Act::FlushDir, Act::Ack]
        );
        assert_eq!(
            plan.commit(&[]).unwrap(),
            vec![Act::AppendMain, Act::FlushMain, Act::Ack]
        );
        let (mut unsynced, opening) = Plan::open(Fsync::Off).unwrap();
        assert_eq!(opening, Vec::new());
        assert_eq!(
            unsynced.commit(&[]).unwrap(),
            vec![Act::AppendMain, Act::Ack]
        );
    }
}
