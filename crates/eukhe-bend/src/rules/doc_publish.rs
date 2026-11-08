//! The step of a publish after it re-checked its target, just before the
//! rename (`bend/doc_publish.bend`, entry `bend/ffi_doc_publish.bend`;
//! `laws/doc_publish.bend`, spec `spec/harness/doc_publish.bend`): a
//! publish renames only over the bytes its edit was based on; over other
//! bytes it rebases the edit onto them and checks again, a bounded number
//! of times; a target gone, or changed once the rebases ran out, is
//! refused.

use crate::wire::{Reader, Writer};
use crate::{call, expect_core, Entry, Error};

/// What the re-check of the target met.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Seen {
    /// The target holds the bytes the edit was based on.
    Same,
    /// No file is there.
    Gone,
    /// Other bytes are there.
    Moved,
}

/// What the publish does next.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Step {
    /// Rename the new bytes over the target.
    Place,
    /// Rebase the edit onto the target's bytes, write them, re-check.
    Rebase,
    /// Write nothing: the target keeps its bytes.
    Refuse,
}

/// The next step of a publish that rebased `rebases` times and then met
/// `seen`.
#[must_use]
pub fn step(rebases: u32, seen: Seen) -> Step {
    expect_core(Entry::DocPublish, step_call(rebases, seen))
}

fn step_call(rebases: u32, seen: Seen) -> Result<Step, Error> {
    let tag = match seen {
        Seen::Same => 0,
        Seen::Gone => 1,
        Seen::Moved => 2,
    };
    let mut request = Writer::new();
    request.u32(rebases).tag(tag);
    let reply = call(Entry::DocPublish, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let step = match reader.tag_of(3, "a publish step")? {
        0 => Step::Place,
        1 => Step::Rebase,
        // `tag_of` answers a tag below 3: this is 2.
        _ => Step::Refuse,
    };
    reader.end()?;
    Ok(step)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The table comes from the compiled core: only the base is replaced;
    /// other bytes are rebased onto three times, then refused.
    #[test]
    fn the_core_replaces_only_the_base() {
        let table: Vec<[Step; 3]> = (0..5)
            .map(|rebases| [Seen::Same, Seen::Gone, Seen::Moved].map(|seen| step(rebases, seen)))
            .collect();
        let (place, rebase, refuse) = (Step::Place, Step::Rebase, Step::Refuse);
        assert_eq!(
            table,
            vec![
                [place, refuse, rebase],
                [place, refuse, rebase],
                [place, refuse, rebase],
                [place, refuse, refuse],
                [place, refuse, refuse],
            ]
        );
    }
}
