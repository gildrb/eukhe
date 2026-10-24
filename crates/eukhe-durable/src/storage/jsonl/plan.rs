//! The rules of the commit log, decided by the compiled Bend core
//! (`bend/log.bend`, entry `bend/ffi_log.bend`; laws `laws/log.bend`):
//! what an open does with a file ([`tail`]), and the steps a storage does
//! at open and per commit ([`Plan`]). [`super::JsonlStorage`] reads the
//! facts and does the steps.

use eukhe_bend::wire::{Reader, WireError, Writer};
use eukhe_bend::{call, Entry, Error, Stepper};

/// What an open does with a file (`Lg.Tail`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Tail {
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
/// [`Error`] only from an inconsistent build (see [`eukhe_bend::expect_core`]).
pub(super) fn tail(len: usize, last: Option<usize>) -> Result<Tail, Error> {
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

/// A step of [`super::JsonlStorage`] (`Lg.Act`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Act {
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

/// The plan of one storage: the compiled core's stepper, which keeps
/// whether the storage syncs and whether `main.jsonl`'s directory entry is
/// durable (`Lg.Store`).
#[derive(Debug)]
pub(super) struct Plan {
    core: Stepper,
}

impl Plan {
    /// The plan of a storage that syncs (`fsync`) or not, and the steps of
    /// its open (`Lg.Store.open`).
    ///
    /// # Errors
    ///
    /// [`Error`] only from an inconsistent build (see [`eukhe_bend::expect_core`]).
    pub(super) fn open(fsync: bool) -> Result<(Plan, Vec<Act>), Error> {
        let mut request = Writer::new();
        request.bool(fsync);
        let (core, reply) = Stepper::open(Entry::Log, &request.finish()?)?;
        Ok((Plan { core }, read_acts(&reply)?))
    }

    /// The steps of a commit whose sidecar files have durable directory
    /// entries as `durable` says, in the commit's order (`Lg.Store.commit`).
    ///
    /// # Errors
    ///
    /// [`Error`] only from an inconsistent build (see [`eukhe_bend::expect_core`]).
    pub(super) fn commit(&mut self, durable: &[bool]) -> Result<Vec<Act>, Error> {
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
    use super::{tail, Act, Plan, Tail};

    #[test]
    fn an_open_asks_the_compiled_core() {
        assert_eq!(tail(10, Some(4)).unwrap(), Tail::Torn(5));
    }

    #[test]
    fn a_plan_asks_the_compiled_core() {
        let (mut plan, opening) = Plan::open(true).unwrap();
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
}
