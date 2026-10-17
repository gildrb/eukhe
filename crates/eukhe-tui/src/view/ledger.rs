//! The transcript ledger: the state of each chat entry on the inline
//! terminal (docs/harness.md S8, rule 1; model `bend/screen.bend`
//! section 1, `step`).
//!
//! An entry is active (it can still change), final (its rows are fixed),
//! or committed (its rows are in the terminal's native scrollback). A
//! flush commits the final entries in order, up to the first active one,
//! so the committed entries are always a prefix. Committed rows are never
//! written again: an edit to a committed entry changes nothing here, and
//! a new width only applies to the rows written after it.
//!
//! Entry `i` of the chat is block `i`. A block's `len` counts the changes
//! it took while it was active: the model's length of a block.

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

/// One chat entry's state and the changes it took while active.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Block {
    pub(crate) phase: Phase,
    pub(crate) len: usize,
}

/// The blocks, in chat order, and the width new rows are written at.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct Ledger {
    blocks: Vec<Block>,
    width: usize,
}

impl Ledger {
    /// The blocks in chat order (the bridge reads them).
    #[cfg(test)]
    pub(crate) fn blocks(&self) -> &[Block] {
        &self.blocks
    }

    /// The width new rows are written at.
    pub(crate) fn width(&self) -> usize {
        self.width
    }

    /// The number of committed blocks (they come first).
    pub(crate) fn committed(&self) -> usize {
        self.blocks
            .iter()
            .take_while(|block| block.phase == Phase::Committed)
            .count()
    }

    /// A new block starts, active (model `Open`). Returns its id.
    pub(crate) fn open(&mut self) -> usize {
        self.blocks.push(Block {
            phase: Phase::Active,
            len: 0,
        });
        self.blocks.len() - 1
    }

    /// Open a block for every chat entry the ledger does not have yet.
    pub(crate) fn open_to(&mut self, entries: usize) {
        while self.blocks.len() < entries {
            self.open();
        }
    }

    /// Block `id` took `n` more changes (model `Grow`). Only an active
    /// block grows: a final or committed block keeps its rows.
    pub(crate) fn grow(&mut self, id: usize, n: usize) {
        if let Some(block) = self.blocks.get_mut(id) {
            match block.phase {
                Phase::Active => block.len += n,
                Phase::Final | Phase::Committed => {}
            }
        }
    }

    /// Block `id` can no longer change (model `Fin`).
    pub(crate) fn finish(&mut self, id: usize) {
        if let Some(block) = self.blocks.get_mut(id) {
            match block.phase {
                Phase::Active => block.phase = Phase::Final,
                Phase::Final | Phase::Committed => {}
            }
        }
    }

    /// Commit the final blocks in order, up to the first active block
    /// (model `Flush`). Returns the ids it committed: their rows go into
    /// scrollback now.
    pub(crate) fn flush(&mut self) -> Range<usize> {
        let start = self.committed();
        let mut end = start;
        for block in &mut self.blocks[start..] {
            match block.phase {
                Phase::Active => break,
                Phase::Final | Phase::Committed => {
                    block.phase = Phase::Committed;
                    end += 1;
                }
            }
        }
        start..end
    }

    /// The terminal has a new width (model `Resize`): rows written from
    /// now on use it; no block is written again.
    pub(crate) fn resize(&mut self, width: usize) {
        self.width = width;
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
    /// block; a growth of a committed block changes nothing.
    #[test]
    fn a_flush_commits_up_to_the_first_active_block() {
        let mut ledger = Ledger::default();
        ledger.open_to(3);
        ledger.grow(0, 2);
        ledger.finish(0);
        ledger.finish(2);
        assert_eq!(ledger.flush(), 0..1);
        ledger.grow(0, 5);
        ledger.grow(1, 1);
        assert_eq!(
            ledger,
            Ledger {
                blocks: vec![
                    Block {
                        phase: Phase::Committed,
                        len: 2
                    },
                    Block {
                        phase: Phase::Active,
                        len: 1
                    },
                    Block {
                        phase: Phase::Final,
                        len: 0
                    },
                ],
                width: 0,
            }
        );
        ledger.finish(1);
        assert_eq!(ledger.flush(), 1..3);
        assert_eq!(ledger.committed(), 3);
    }
}
