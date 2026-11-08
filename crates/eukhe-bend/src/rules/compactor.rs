//! The compactor's decisions (`bend/compactor.bend`, entry
//! `bend/ffi_compactor.bend`; `laws/compactor.bend`, spec/README.md M2):
//! how a line of the chat memory ends, one model reply at a time, and the
//! failure cap of a node not built yet. The caller keeps the texts and
//! sends their lengths in UTF-8 bytes; each function encodes them, calls
//! [`Entry::Compactor`] and decodes the decision.

use crate::wire::{Reader, Writer, NAT_MAX};
use crate::{call, expect_core, Entry, Error};

/// A line being written (`Lst`): the calls it may still make, the calls it
/// made, and the length of the shortest reply so far (each follow-up must
/// be shorter).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Line {
    left: u64,
    made: u64,
    best: Option<u64>,
}

/// How a line ends (`Fin`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fin {
    /// The reply just read is the line.
    Whole,
    /// The reply just read, cut to the node's size (the last try).
    CutReply,
    /// The shortest reply before it, cut to the node's size.
    CutBest,
    /// The node's input, cut to the node's size.
    CutInput,
    /// The call failed (a provider error).
    Lost,
}

/// What a line does next (`Next`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Next {
    /// The line ends after `calls` model calls.
    Ends { calls: u64, fin: Fin },
    /// The next model call goes; the reply just read is the shortest.
    Asks(Line),
}

/// One reply of the model, as the line reads it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Reply {
    /// The call failed: a provider error, or a reply that stopped with one.
    Erred,
    /// The reply's text (thinking dropped, trimmed) has this many bytes.
    Says(usize),
}

/// A line of at most `tries` model calls (`line.open`).
#[must_use]
pub fn open(tries: usize) -> Next {
    expect_core(Entry::Compactor, open_call(tries))
}

fn open_call(tries: usize) -> Result<Next, Error> {
    let mut request = Writer::new();
    request.tag(0).nat(saturate(tries));
    next_of(&call(Entry::Compactor, &request.finish()?)?)
}

impl Line {
    /// The decision on one reply to a line of `node`-byte lines
    /// (`line.step`).
    #[must_use]
    pub fn read(self, node: usize, reply: Reply) -> Next {
        expect_core(Entry::Compactor, self.read_call(node, reply))
    }

    fn read_call(self, node: usize, reply: Reply) -> Result<Next, Error> {
        let mut request = Writer::new();
        request
            .tag(1)
            .nat(self.left)
            .nat(self.made)
            .nat(saturate(node));
        match self.best {
            None => request.none(),
            Some(len) => request.some().nat(len),
        };
        match reply {
            Reply::Erred => request.tag(0),
            Reply::Says(len) => request.tag(1).nat(saturate(len)),
        };
        next_of(&call(Entry::Compactor, &request.finish()?)?)
    }
}

/// A length on the wire: a text past [`NAT_MAX`] bytes (100 TB) cannot be
/// in memory, so the bound never changes a decision.
fn saturate(n: usize) -> u64 {
    u64::try_from(n).map_or(NAT_MAX, |n| n.min(NAT_MAX))
}

fn next_of(reply: &str) -> Result<Next, Error> {
    let mut reader = Reader::reply(reply)?;
    // `tag_of` answers a tag below 2: 0 the line ends, 1 the next call goes.
    let next = if reader.tag_of(2, "a line's next step")? == 0 {
        let calls = reader.nat()?;
        let fin = match reader.tag_of(5, "how a line ends")? {
            0 => Fin::Whole,
            1 => Fin::CutReply,
            2 => Fin::CutBest,
            3 => Fin::CutInput,
            // `tag_of` answers a tag below 5: this is 4.
            _ => Fin::Lost,
        };
        Next::Ends { calls, fin }
    } else {
        let left = reader.nat()?;
        let made = reader.nat()?;
        let best = if reader.maybe()? {
            Some(reader.nat()?)
        } else {
            None
        };
        Next::Asks(Line { left, made, best })
    };
    reader.end()?;
    Ok(next)
}

/// A node of the view, as the failure cap counts it (`Pend`): built, or
/// owing its line with the failed calls it has left before the cap builds
/// it from its input.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Pend {
    Made,
    Owed(u32),
}

/// How a call of a node ended (`Outcome`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Outcome {
    /// Its line was saved.
    Built,
    /// The model call failed: a provider error, or past its deadline.
    Failed,
    /// The disk failed: the node's input could not be read, or a line not
    /// saved.
    Disk,
    /// A waiting turn stopped it.
    Stopped,
}

impl Pend {
    /// The node after one of its calls ended with `outcome` (`Pend.after`).
    #[must_use]
    pub fn after(self, outcome: Outcome) -> Pend {
        expect_core(Entry::Compactor, self.after_call(outcome))
    }

    fn after_call(self, outcome: Outcome) -> Result<Pend, Error> {
        let mut request = Writer::new();
        request.tag(2);
        match self {
            Pend::Made => request.tag(0),
            Pend::Owed(left) => request.tag(1).nat(u64::from(left)),
        };
        request.tag(match outcome {
            Outcome::Built => 0,
            Outcome::Failed => 1,
            Outcome::Disk => 2,
            Outcome::Stopped => 3,
        });
        let reply = call(Entry::Compactor, &request.finish()?)?;
        let mut reader = Reader::reply(&reply)?;
        let pend = match reader.tag_of(2, "a pending node")? {
            0 => Pend::Made,
            // `tag_of` answers a tag below 2: this is 1.
            _ => Pend::Owed(reader.u32()?),
        };
        reader.end()?;
        Ok(pend)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Each decision comes from the compiled core: a line opens, reads an
    /// over-long reply, then a shorter one that fits; a failed call of a
    /// node with no failures left builds it.
    #[test]
    fn the_compactor_decisions_come_from_the_compiled_core() {
        let Next::Asks(line) = open(5) else {
            panic!("a line of 5 tries asks");
        };
        let Next::Asks(follow_up) = line.read(512, Reply::Says(700)) else {
            panic!("an over-long first reply asks again");
        };
        assert_eq!(
            (
                follow_up,
                follow_up.read(512, Reply::Says(512)),
                follow_up.read(512, Reply::Erred),
                Pend::Owed(0).after(Outcome::Failed),
                Pend::Owed(2).after(Outcome::Disk),
            ),
            (
                Line {
                    left: 4,
                    made: 1,
                    best: Some(700)
                },
                Next::Ends {
                    calls: 2,
                    fin: Fin::Whole
                },
                Next::Ends {
                    calls: 2,
                    fin: Fin::Lost
                },
                Pend::Made,
                Pend::Owed(2),
            )
        );
    }
}
