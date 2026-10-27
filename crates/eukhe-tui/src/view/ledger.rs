//! The transcript ledger: the state of each chat entry on the inline
//! terminal (rule 1; model `bend/screen.bend`
//! section 1, `run`).
//!
//! An entry is active (it can still change), final (its rows are fixed),
//! or committed (its rows are in the terminal's native scrollback). A
//! flush commits the final entries in order, up to the first active one,
//! so the committed entries are always a prefix. Committed rows are never
//! written again: a finish of a committed entry changes nothing here, and
//! a new width only applies to the rows written after it.
//!
//! Entry `i` of the chat is block `i`. The rule runs as its Bend model, one
//! call of the compiled core per frame (`bend/ffi_screen.bend`, law
//! `screen_ffi_run`): the events of the frame on the blocks after the
//! committed prefix (law `tx_committed_inert`: committed blocks are inert,
//! so the prefix never travels).

use std::ops::Range;

use eukhe_bend::wire::{Reader, WireError, Writer, NAT_MAX};
use eukhe_bend::Entry;

/// The state of one block.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Phase {
    /// The entry can still change; it renders in the live area.
    Active,
    /// The entry can no longer change; the next flush commits it when no
    /// active entry comes before it.
    Final,
    /// The entry's rows are in the native scrollback.
    Committed,
}

/// One step of the transcript protocol (model `Ev`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Event {
    /// A new block starts, active (model `Open`).
    Open,
    /// Block `id` can no longer change (model `Fin`).
    Finish(usize),
    /// Commit the final blocks in order, up to the first active block
    /// (model `Flush`).
    Flush,
    /// The terminal has a new width (model `Resize`).
    Resize(usize),
}

/// A phase, by its tag in `bend/ffi_screen.bend` (model `St`).
fn phase_tag(phase: Phase) -> u32 {
    match phase {
        Phase::Active => 0,
        Phase::Final => 1,
        Phase::Committed => 2,
    }
}

/// A width as the core reads it: saturated at the wire's largest Nat (a
/// width never ends a row, so the cap writes the same rows).
fn wire_width(width: usize) -> u64 {
    u64::try_from(width).map_or(NAT_MAX, |width| width.min(NAT_MAX))
}

/// The request: the blocks from `first` (model `Tx`: each block's id, its
/// phase and its length 0, then the next id and the width), and the
/// events.
fn write_run(writer: &mut Writer, first: usize, phases: &[Phase], width: usize, events: &[Event]) {
    writer.tag(0).count(phases.len());
    for (offset, phase) in phases.iter().enumerate() {
        writer.count(first + offset).tag(phase_tag(*phase)).nat(0);
    }
    writer
        .count(first + phases.len())
        .nat(wire_width(width))
        .count(events.len());
    for event in events {
        match *event {
            Event::Open => writer.tag(0),
            Event::Finish(id) => writer.tag(2).count(id),
            Event::Flush => writer.tag(3),
            Event::Resize(width) => writer.tag(4).nat(wire_width(width)),
        };
    }
}

/// The reply: the blocks' phases and the width (model `Tx`).
fn read_run(reader: &mut Reader<'_>) -> Result<(Vec<Phase>, usize), WireError> {
    let blocks = reader.count()?;
    let mut phases = Vec::with_capacity(blocks);
    for _ in 0..blocks {
        let _id = reader.nat()?;
        phases.push(match reader.tag_of(3, "a block state")? {
            0 => Phase::Active,
            1 => Phase::Final,
            // `tag_of` answered at most 2.
            2..=u32::MAX => Phase::Committed,
        });
        let _len = reader.nat()?;
    }
    let _next = reader.nat()?;
    // The width the request saturated, back as a `usize`.
    let width = reader.count()?;
    Ok((phases, width))
}

/// The blocks, in chat order, and the width new rows are written at.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct Ledger {
    blocks: Vec<Phase>,
    width: usize,
}

impl Ledger {
    /// The width new rows are written at.
    pub(crate) fn width(&self) -> usize {
        self.width
    }

    /// The number of blocks (one per chat entry the ledger has seen).
    pub(crate) fn len(&self) -> usize {
        self.blocks.len()
    }

    /// The number of committed blocks (they come first).
    pub(crate) fn committed(&self) -> usize {
        self.blocks
            .iter()
            .take_while(|phase| **phase == Phase::Committed)
            .count()
    }

    /// Apply a frame's `events` (model `run`, in the compiled core).
    /// Returns the ids they committed: their rows go into scrollback now.
    pub(crate) fn apply(&mut self, events: &[Event]) -> Range<usize> {
        let start = self.committed();
        let (phases, width) = crate::bend_core::decide(
            Entry::Screen,
            |writer| write_run(writer, start, &self.blocks[start..], self.width, events),
            read_run,
        );
        self.blocks.truncate(start);
        self.blocks.extend(phases);
        self.width = width;
        start..self.committed()
    }

    /// Keep only the first `len` blocks (the chat popped its last
    /// entries). Outside the model: a popped entry is active, as the
    /// settle rule keeps it live; a popped committed entry stays in
    /// scrollback as written.
    pub(crate) fn truncate(&mut self, len: usize) {
        self.blocks.truncate(len);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The core's reply replaces the blocks after the committed prefix,
    /// which stays in Rust: a flush commits the final prefix and stops at
    /// the first active block, and the range names the ids it committed.
    #[test]
    fn a_flush_commits_up_to_the_first_active_block() {
        let mut ledger = Ledger::default();
        let committed = ledger.apply(&[
            Event::Open,
            Event::Open,
            Event::Open,
            Event::Finish(0),
            Event::Finish(2),
            Event::Flush,
        ]);
        assert_eq!(committed, 0..1);
        assert_eq!(ledger.apply(&[Event::Finish(0)]), 1..1);
        assert_eq!(
            ledger,
            Ledger {
                blocks: vec![Phase::Committed, Phase::Active, Phase::Final],
                width: 0,
            }
        );
        assert_eq!(ledger.apply(&[Event::Finish(1), Event::Flush]), 1..3);
        assert_eq!(ledger.committed(), 3);
    }
}
