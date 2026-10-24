//! The repetition guard of one stream (`bend/infer_guard.bend`, stepper
//! `bend/ffi_infer_guard.bend`; `laws/infer_guard.bend`, docs/inference.md
//! S6.5): the guard stays in the Bend heap, the caller sends one id per
//! chunk (equal chunks, equal ids) and reads whether it cut the stream.

use crate::wire::{Reader, Writer};
use crate::{expect_core, Entry, Error, Stepper};

/// Where the guard cut its stream (`Cuts`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Cut {
    /// The chunks read, including the one that completed the window.
    pub chunks: u64,
    /// The shortest period of the window, in chunks (1: one chunk
    /// repeated).
    pub period: u32,
}

/// The guard of one stream with a window of `limit` chunks: the chunk
/// that makes the last `limit` chunks periodic, with a period of at most
/// `max(1, limit / 4)`, cuts it.
#[derive(Debug)]
pub struct Guard {
    core: Stepper,
}

impl Guard {
    /// A guard that read no chunk yet.
    #[must_use]
    pub fn new(limit: u32) -> Guard {
        let opened = (|| -> Result<Guard, Error> {
            let mut request = Writer::new();
            request.u32(limit);
            let (core, reply) = Stepper::open(Entry::InferGuard, &request.finish()?)?;
            Reader::reply(&reply)?.end()?;
            Ok(Guard { core })
        })();
        expect_core(Entry::InferGuard, opened)
    }

    /// Read the next chunk, by its id (below [`crate::wire::NAT_MAX`]: an
    /// id per distinct chunk of one stream); the cut when it completes a
    /// periodic window. A cut stream stays cut: every later chunk answers
    /// the same cut.
    pub fn feed(&mut self, chunk: u64) -> Option<Cut> {
        expect_core(Entry::InferGuard, self.feed_call(chunk))
    }

    fn feed_call(&mut self, chunk: u64) -> Result<Option<Cut>, Error> {
        let mut request = Writer::new();
        request.nat(chunk);
        let reply = self.core.step(&request.finish()?)?;
        let mut reader = Reader::reply(&reply)?;
        let cut = if reader.tag_of(2, "a guard's answer")? == 0 {
            None
        } else {
            Some(Cut {
                chunks: reader.nat()?,
                period: reader.u32()?,
            })
        };
        reader.end()?;
        Ok(cut)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Each chunk goes to the compiled core: a window of 8 cuts a two-chunk
    /// block at its fourth repetition, period 2, and stays cut.
    #[test]
    fn the_guard_runs_in_the_compiled_core() {
        let mut guard = Guard::new(8);
        let fed: Vec<Option<Cut>> = [1, 2, 1, 2, 1, 2, 1, 2, 3]
            .into_iter()
            .map(|chunk| guard.feed(chunk))
            .collect();
        let cut = Some(Cut {
            chunks: 8,
            period: 2,
        });
        assert_eq!(fed, [None, None, None, None, None, None, None, cut, cut]);
    }
}
