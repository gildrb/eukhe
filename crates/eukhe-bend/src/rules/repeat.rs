//! The rounds in a row with the same tool calls and the same results
//! (`bend/repeat.bend`, stepper `bend/ffi_repeat.bend`;
//! `laws/repeat.bend`, docs/harness.md H4.8.4): the walk stays in the
//! Bend heap; the caller sends the context's messages newest first, each
//! result and each reply's calls as an id (equal values, equal ids), and
//! reads whether the row ended and its count.

use std::num::NonZeroU32;

use crate::wire::{Reader, WireError, Writer};
use crate::{expect_core, Entry, Error, Stepper};

/// A message of the context as the walk reads it (`Rp.Ev`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Seen {
    System,
    User,
    /// A tool result: the id of its content and error flag.
    Result(u64),
    /// A reply with tool calls: the id of its calls (as a set).
    Called(u64),
    /// A reply with no tool call.
    Said,
}

/// The walk of one count: open with the id of the calls the new reply
/// would make, then [`Row::step`] each message newest first until it
/// answers the count, or [`Row::end`] at the context's start.
#[derive(Debug)]
pub struct Row {
    core: Stepper,
}

impl Row {
    /// A walk of the calls `want` (an id below [`crate::wire::NAT_MAX`])
    /// that read no message yet.
    #[must_use]
    pub fn open(want: u64) -> Row {
        let opened = (|| -> Result<Row, Error> {
            let mut request = Writer::new();
            request.nat(want);
            let (core, reply) = Stepper::open(Entry::Repeat, &request.finish()?)?;
            Reader::reply(&reply)?.end()?;
            Ok(Row { core })
        })();
        expect_core(Entry::Repeat, opened)
    }

    /// Read the next older message (its ids below
    /// [`crate::wire::NAT_MAX`]); the count once it ends the row.
    pub fn step(&mut self, seen: Seen) -> Option<NonZeroU32> {
        let mut request = Writer::new();
        match seen {
            Seen::System => request.tag(0),
            Seen::User => request.tag(1),
            Seen::Result(id) => request.tag(2).nat(id),
            Seen::Called(id) => request.tag(3).nat(id),
            Seen::Said => request.tag(4),
        };
        expect_core(Entry::Repeat, self.step_call(request))
    }

    /// The count when the context has no older message.
    #[must_use]
    pub fn end(mut self) -> NonZeroU32 {
        let mut request = Writer::new();
        request.tag(5);
        let ended = self.step_call(request).and_then(|count| {
            count.ok_or(Error::Wire(WireError::Malformed {
                at: 0,
                expected: "the count at the context's start",
            }))
        });
        expect_core(Entry::Repeat, ended)
    }

    fn step_call(&mut self, mut request: Writer) -> Result<Option<NonZeroU32>, Error> {
        let reply = self.core.step(&request.finish()?)?;
        let mut reader = Reader::reply(&reply)?;
        let count = if reader.tag_of(2, "a walk's answer")? == 0 {
            None
        } else {
            let count = NonZeroU32::new(reader.u32()?).ok_or(WireError::Malformed {
                at: 2,
                expected: "a count of at least 1",
            })?;
            Some(count)
        };
        reader.end()?;
        Ok(count)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Each message goes to the compiled core: two rounds with the
    /// requested calls and the same result, a system message between them,
    /// make a row of 3 that the context's start ends; a user message ends
    /// a row at once.
    #[test]
    fn the_walk_runs_in_the_compiled_core() {
        let mut row = Row::open(0);
        let read: Vec<Option<NonZeroU32>> = [
            Seen::Result(1),
            Seen::Called(0),
            Seen::System,
            Seen::Result(1),
            Seen::Called(0),
        ]
        .into_iter()
        .map(|seen| row.step(seen))
        .collect();
        assert_eq!(read, [None; 5]);
        assert_eq!(row.end().get(), 3);
        let mut steered = Row::open(0);
        assert_eq!(steered.step(Seen::User), NonZeroU32::new(1));
    }
}
