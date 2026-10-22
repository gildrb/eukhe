//! The transcript ledger: the state of each chat entry on the inline
//! terminal (docs/interface.md S8, rule 1; model `bend/screen.bend`
//! section 1, `run`).
//!
//! An entry is active (it can still change), final (its rows are fixed),
//! or committed (its rows are in the terminal's native scrollback). A
//! flush commits the final entries in order, up to the first active one,
//! so the committed entries are always a prefix. Committed rows are never
//! written again: a finish of a committed entry changes nothing here, and
//! a new width only applies to the rows written after it.
//!
//! Entry `i` of the chat is block `i`. The rule is one pure call, [`run`]:
//! the events of a frame applied to the blocks after the committed prefix
//! (law `tx_committed_inert`: committed blocks are inert, so the prefix
//! never travels).

use std::ops::Range;

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

/// The blocks after the committed prefix (model `Tx`): block
/// `first + i` is `phases[i]`, the next block opens as
/// `first + phases.len()`.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Tail {
    first: usize,
    phases: Vec<Phase>,
    width: usize,
}

/// The transcript after `events` (model `run`).
fn run(tail: Tail, events: &[Event]) -> Tail {
    let Tail {
        first,
        mut phases,
        mut width,
    } = tail;
    for event in events {
        match *event {
            Event::Open => phases.push(Phase::Active),
            Event::Finish(id) => {
                if let Some(phase) = id
                    .checked_sub(first)
                    .and_then(|index| phases.get_mut(index))
                {
                    match phase {
                        Phase::Active => *phase = Phase::Final,
                        Phase::Final | Phase::Committed => {}
                    }
                }
            }
            Event::Flush => {
                for phase in &mut phases {
                    match phase {
                        Phase::Active => break,
                        Phase::Final | Phase::Committed => *phase = Phase::Committed,
                    }
                }
            }
            Event::Resize(new) => width = new,
        }
    }
    Tail {
        first,
        phases,
        width,
    }
}

/// The blocks, in chat order, and the width new rows are written at.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct Ledger {
    blocks: Vec<Phase>,
    width: usize,
}

impl Ledger {
    /// The blocks in chat order (the bridge reads them).
    #[cfg(test)]
    pub(crate) fn blocks(&self) -> &[Phase] {
        &self.blocks
    }

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

    /// Apply a frame's `events` (model `run`). Returns the ids they
    /// committed: their rows go into scrollback now.
    pub(crate) fn apply(&mut self, events: &[Event]) -> Range<usize> {
        let start = self.committed();
        let after = run(
            Tail {
                first: start,
                phases: self.blocks.split_off(start),
                width: self.width,
            },
            events,
        );
        self.blocks.extend(after.phases);
        self.width = after.width;
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

    /// A flush commits the final prefix and stops at the first active
    /// block; a finish of a committed block changes nothing.
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
