//! The hand-back of a split child given a list of items
//! (`bend/work_list.bend`, entry `bend/ffi_work_list.bend`;
//! `laws/work_list.bend`, spec `spec/agents/work_list.bend`): the child
//! accounts for each item done or left; its hand-back is finished only when
//! every item is done, else stopped, naming the items left in the parent's
//! order. An item the child never accounted for is left.

use crate::wire::{Reader, WireError, Writer};
use crate::{call, expect_core, Entry, Error};

/// The hand-back of a work list.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Outcome {
    /// Every item is done.
    Finished,
    /// The positions of the items not done, ascending.
    Stopped { left: Vec<usize> },
}

/// The hand-back of the items `done` marks, one per item in the parent's
/// order: `true` only for an item the child accounted done.
#[must_use]
pub fn outcome(done: &[bool]) -> Outcome {
    expect_core(Entry::WorkList, outcome_call(done))
}

fn outcome_call(done: &[bool]) -> Result<Outcome, Error> {
    let mut request = Writer::new();
    request.count(done.len());
    for item in done {
        request.bool(*item);
    }
    let reply = call(Entry::WorkList, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    // tag_of refuses a tag past 1: 0 finished, 1 stopped.
    let outcome = if reader.tag_of(2, "a work list hand-back")? == 0 {
        Outcome::Finished
    } else {
        let count = reader.count()?;
        let left = (0..count)
            .map(|_| position(&mut reader, done.len()))
            .collect::<Result<Vec<_>, _>>()?;
        Outcome::Stopped { left }
    };
    reader.end()?;
    Ok(outcome)
}

/// One position of an item left, below `items`.
fn position(reader: &mut Reader<'_>, items: usize) -> Result<usize, WireError> {
    let at = reader.nat()?;
    usize::try_from(at)
        .ok()
        .filter(|at| *at < items)
        .ok_or(WireError::Malformed {
            at: 0,
            expected: "the position of an item",
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The table comes from the compiled core: no items and all done
    /// finish; every item not done is left, in order.
    #[test]
    fn the_core_stops_on_every_item_not_done() {
        assert_eq!(
            [
                outcome(&[]),
                outcome(&[true, true]),
                outcome(&[true, false, true, false]),
                outcome(&[false]),
            ],
            [
                Outcome::Finished,
                Outcome::Finished,
                Outcome::Stopped { left: vec![1, 3] },
                Outcome::Stopped { left: vec![0] },
            ]
        );
    }
}
