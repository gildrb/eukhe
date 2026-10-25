//! The order in which the state tree records one commit's changes
//! (`bend/tree_commit.bend`, entry `bend/ffi_tree_commit.bend`;
//! `laws/tree_commit.bend`): the Puts in rounds over the waiting ones, in
//! commit order, each once its parent is present; then the unknown
//! parents; then the Dels. The caller interns the commit's keys to
//! commit-local numbers and says, per Put, whether its parent is in the
//! tree now (the root or a node) or which commit key it is; it gets each
//! change's payload back in the order to apply it.

use crate::wire::{Reader, WireError, Writer};
use crate::{call, expect_core, Entry, Error};

/// A change of a commit; its keys are commit-local numbers (below
/// [`crate::wire::NAT_MAX`]). `P` is a Put's payload, `D` a Del's.
#[derive(Debug, PartialEq, Eq)]
pub enum Change<P, D> {
    /// A Put whose parent is the root or a node of the tree now.
    Here { key: u64, put: P },
    /// A Put whose parent is the commit key `parent`, absent from the tree
    /// now.
    Under { key: u64, parent: u64, put: P },
    /// A Del.
    Gone(D),
}

/// What to do with a change, in order.
#[derive(Debug, PartialEq, Eq)]
pub enum Step<P, D> {
    /// Apply the Put: its parent is present.
    Apply(P),
    /// The Put's parent is not in the tree (an [`Change::Under`] Put).
    Orphan(P),
    /// Apply the Del.
    Retire(D),
}

enum Held<P, D> {
    Put(P),
    /// A Put under a commit key: only these can be unknown parents.
    Under(P),
    Del(D),
}

/// Each change's step, in the order to take them.
///
/// # Panics
/// When the compiled core fails (an inconsistent build), or when a key is
/// above [`crate::wire::NAT_MAX`].
#[must_use]
pub fn order<P, D>(changes: Vec<Change<P, D>>) -> Vec<Step<P, D>> {
    expect_core(Entry::TreeCommit, call_order(changes))
}

fn call_order<P, D>(changes: Vec<Change<P, D>>) -> Result<Vec<Step<P, D>>, Error> {
    let mut request = Writer::new();
    request.count(changes.len());
    let mut held = Vec::with_capacity(changes.len());
    for change in changes {
        held.push(Some(match change {
            Change::Here { key, put } => {
                request.tag(0).nat(key);
                Held::Put(put)
            }
            Change::Under { key, parent, put } => {
                request.tag(1).nat(key).nat(parent);
                Held::Under(put)
            }
            Change::Gone(del) => {
                request.tag(2);
                Held::Del(del)
            }
        }));
    }
    let reply = call(Entry::TreeCommit, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let count = reader.count()?;
    let mut steps = Vec::with_capacity(count);
    for _ in 0..count {
        let tag = reader.tag_of(3, "a result")?;
        let slot = usize::try_from(reader.nat()?)
            .ok()
            .and_then(|index| held.get_mut(index))
            .ok_or(WireError::Malformed {
                at: 0,
                expected: "the index of a change",
            })?;
        steps.push(match (tag, slot.take()) {
            (0, Some(Held::Put(put) | Held::Under(put))) => Step::Apply(put),
            (1, Some(Held::Under(put))) => Step::Orphan(put),
            (2.., Some(Held::Del(del))) => Step::Retire(del),
            (0 | 1, Some(Held::Del(_)))
            | (1, Some(Held::Put(_)))
            | (2.., Some(Held::Put(_) | Held::Under(_)))
            | (_, None) => {
                return Err(WireError::Malformed {
                    at: 0,
                    expected: "one step of the change's kind for each change",
                }
                .into());
            }
        });
    }
    reader.end()?;
    if steps.len() == held.len() {
        Ok(steps)
    } else {
        Err(WireError::Malformed {
            at: 0,
            expected: "a step for each change",
        }
        .into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The changes go to the compiled core: an entry before its
    /// conversation applies after it, an entry under an unknown
    /// conversation is an unknown parent, and the Del comes last.
    #[test]
    fn the_order_runs_in_the_compiled_core() {
        let changes = vec![
            Change::Under {
                key: 0,
                parent: 1,
                put: "entry",
            },
            Change::Gone("retired"),
            Change::Here {
                key: 1,
                put: "conversation",
            },
            Change::Under {
                key: 2,
                parent: 3,
                put: "orphan",
            },
        ];
        assert_eq!(
            order(changes),
            vec![
                Step::Apply("conversation"),
                Step::Apply("entry"),
                Step::Orphan("orphan"),
                Step::Retire("retired"),
            ]
        );
    }
}
