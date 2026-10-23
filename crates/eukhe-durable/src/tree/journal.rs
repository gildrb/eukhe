//! The journal: the records of a session tree, in order, the live tree
//! they make, and the core that decides each record: a stepper of the
//! compiled Bend core (`bend/ffi_tree.bend` over the core of
//! `bend/tree.bend`). The core's state is the live tree (node ids, parents
//! and value indexes) and the journal, kept in the Bend heap; a record and
//! a question cross the wire, the tree does not.

use std::collections::HashMap;
use std::hash::Hash;
use std::sync::{Mutex, PoisonError};

use eukhe_bend::wire::{Reader, WireError, Writer};
use eukhe_bend::{expect_core, Entry, Stepper};

use super::{Applied, Node, NodeId, RewindEffect, SessionTree, TreeOp, TreeRecord};

/// How many halves of the core's key range [0, 2^47) the journal opens the
/// core with: 2^46, ..., 2, 1. The key map splits each place of the range
/// at its middle, so a path to a node has at most 47 forks whatever the
/// order of the puts; 2^47 is the first power of two above the wire's
/// largest Nat, so every id the wire carries is in the range.
const HALVES: u32 = 47;

/// The values of a journal, each once: equal values get one index, so the
/// core compares values by their indexes.
#[derive(Debug)]
struct Values<V> {
    list: Vec<V>,
    index: HashMap<V, u64>,
}

impl<V: Clone + Eq + Hash> Values<V> {
    fn index(&mut self, value: &V) -> u64 {
        if let Some(index) = self.index.get(value) {
            return *index;
        }
        let index = self.list.len() as u64;
        self.list.push(value.clone());
        self.index.insert(value.clone(), index);
        index
    }

    fn get(&self, index: u64) -> Option<&V> {
        usize::try_from(index).ok().and_then(|at| self.list.get(at))
    }

    /// Writes `op` as the core reads it: `0, id, parent, value index` for
    /// a put, `1, id` for a delete.
    fn write_op(&mut self, ask: &mut Writer, op: &TreeOp<V>) {
        match op {
            TreeOp::Put { id, parent, value } => {
                let value = self.index(value);
                ask.tag(0).nat(id.0).nat(parent.0).nat(value);
            }
            TreeOp::Del { id } => {
                ask.tag(1).nat(id.0);
            }
        }
    }
}

/// The core's answer to a record.
enum Taken {
    /// The tree rejected the record and did not change.
    Kept,
    /// The tree took a put or a rewind: its own changes apply.
    Took,
    /// The tree took a delete: these nodes went, in id order.
    Cut(Vec<NodeId>),
}

/// The records of a session tree and the live tree. The journal keeps
/// every record, also a rejected one: a replay rejects it again.
#[derive(Debug)]
pub struct Journal<V> {
    records: Vec<TreeRecord<V>>,
    tree: SessionTree<V>,
    values: Values<V>,
    /// A question (a rewind plan, a snapshot) leaves the core as it was
    /// (`laws/tree.bend` `tree_core_plan_keeps`, `tree_core_snap_keeps`), so the
    /// journal asks it through `&self`. A poisoned lock still holds a
    /// core in step with the journal: a question that panicked left the
    /// core as it was, and a record steps it through `&mut self`.
    core: Mutex<Stepper>,
}

impl<V: Clone + Eq + Hash> Default for Journal<V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<V: Clone + Eq + Hash> Journal<V> {
    /// An empty journal with an empty tree.
    ///
    /// # Panics
    /// When the compiled core fails to open (an inconsistent build).
    #[must_use]
    pub fn new() -> Self {
        let opened = (|| -> Result<Stepper, eukhe_bend::Error> {
            let mut halves = Writer::new();
            halves.count(HALVES as usize);
            for depth in (0..HALVES).rev() {
                halves.nat(1 << depth);
            }
            let (core, reply) = Stepper::open(Entry::Tree, &halves.finish()?)?;
            Reader::reply(&reply)?.end()?;
            Ok(core)
        })();
        Self {
            records: Vec::new(),
            tree: SessionTree::default(),
            values: Values {
                list: Vec::new(),
                index: HashMap::new(),
            },
            core: Mutex::new(expect_core(Entry::Tree, opened)),
        }
    }

    /// Apply `record` to the live tree and keep it. The core decides; the
    /// live tree changes as it answers.
    ///
    /// # Panics
    /// When the compiled core fails, or when an id is above
    /// [`eukhe_bend::wire::NAT_MAX`] (the wire's largest Nat; the ids of a
    /// [`super::StateTree`] count its keys).
    pub fn push(&mut self, record: TreeRecord<V>) -> Applied {
        let mut ask = Writer::new();
        ask.tag(0);
        match &record {
            TreeRecord::Do(op) => {
                ask.tag(0);
                self.values.write_op(&mut ask, op);
            }
            TreeRecord::Rewind(ops) => {
                ask.tag(1).count(ops.len());
                for op in ops {
                    self.values.write_op(&mut ask, op);
                }
            }
        }
        let core = self.core.get_mut().unwrap_or_else(PoisonError::into_inner);
        let taken = (|| -> Result<Taken, eukhe_bend::Error> {
            let reply = core.step(&ask.finish()?)?;
            Ok(read_taken(&reply)?)
        })();
        let applied = match expect_core(Entry::Tree, taken) {
            Taken::Kept => Applied::Rejected,
            Taken::Took => {
                match &record {
                    TreeRecord::Do(op) => take(&mut self.tree, op),
                    TreeRecord::Rewind(ops) => {
                        for op in ops {
                            take(&mut self.tree, op);
                        }
                    }
                }
                Applied::Accepted
            }
            Taken::Cut(ids) => {
                for id in ids {
                    self.tree.remove(id);
                }
                Applied::Accepted
            }
        };
        self.records.push(record);
        applied
    }

    /// The live tree.
    #[must_use]
    pub fn tree(&self) -> &SessionTree<V> {
        &self.tree
    }

    /// The records, in order.
    #[must_use]
    pub fn records(&self) -> &[TreeRecord<V>] {
        &self.records
    }

    /// The snapshot after the first `n` records: their replay. All the
    /// records when `n` is more than their count.
    ///
    /// # Panics
    /// When the compiled core fails.
    #[must_use]
    pub fn snapshot_at(&self, n: usize) -> SessionTree<V> {
        let reply = self.ask(2, n);
        expect_core(Entry::Tree, self.read_nodes(&reply))
    }

    /// What a rewind from the live tree to the snapshot after the first
    /// `n` records does to the work of each node, in the order of the
    /// rewind's ops: a stop for each node the snapshot does not have, then
    /// a start or a restore for each node of the snapshot the live tree
    /// does not have the same, in id order.
    ///
    /// # Panics
    /// When the compiled core fails.
    #[must_use]
    pub fn rewind_plan(&self, n: usize) -> Vec<RewindEffect> {
        let reply = self.ask(1, n);
        expect_core(Entry::Tree, read_plan(&reply))
    }

    /// The core's reply to the question `tag` (1: the rewind plan, 2: the
    /// snapshot) about the tree after the first `n` records. A count past
    /// the records asks for all of them, as `n` does.
    fn ask(&self, tag: u32, n: usize) -> String {
        let n = n.min(self.records.len()) as u64;
        let mut core = self.core.lock().unwrap_or_else(PoisonError::into_inner);
        let reply = (|| -> Result<String, eukhe_bend::Error> {
            Ok(core.step(&Writer::new().tag(tag).nat(n).finish()?)?)
        })();
        expect_core(Entry::Tree, reply)
    }

    /// A snapshot's nodes: `4`, then each node as `id, parent, value
    /// index`, in id order.
    fn read_nodes(&self, reply: &str) -> Result<SessionTree<V>, WireError> {
        let mut reader = Reader::reply(reply)?;
        expect_tag(&mut reader, 4, "a snapshot")?;
        let mut tree = SessionTree::default();
        for _ in 0..reader.count()? {
            let id = NodeId(reader.nat()?);
            let parent = NodeId(reader.nat()?);
            let value = self.values.get(reader.nat()?).ok_or(WireError::Malformed {
                at: 0,
                expected: "a snapshot of the values the journal gave the core",
            })?;
            tree.insert(
                id,
                Node {
                    parent,
                    value: value.clone(),
                },
            );
        }
        reader.end()?;
        Ok(tree)
    }
}

/// The answer's tag is `tag`: the core answers a question with the kind of
/// answer it asks for.
fn expect_tag(reader: &mut Reader<'_>, tag: u32, expected: &'static str) -> Result<(), WireError> {
    if reader.tag()? == tag {
        Ok(())
    } else {
        Err(WireError::Malformed { at: 0, expected })
    }
}

/// The answer to a record: `0` kept, `1` took, `2` and the ids a delete
/// cut.
fn read_taken(reply: &str) -> Result<Taken, WireError> {
    let mut reader = Reader::reply(reply)?;
    let tag = reader.tag_of(3, "the answer to a record")?;
    let taken = if tag == 0 {
        Taken::Kept
    } else if tag == 1 {
        Taken::Took
    } else {
        let count = reader.count()?;
        let mut ids = Vec::with_capacity(count.min(reply.len()));
        for _ in 0..count {
            ids.push(NodeId(reader.nat()?));
        }
        Taken::Cut(ids)
    };
    reader.end()?;
    Ok(taken)
}

/// A rewind plan: `3`, then each effect as its tag (`0` start, `1` stop,
/// `2` restore) and the node's id.
fn read_plan(reply: &str) -> Result<Vec<RewindEffect>, WireError> {
    let mut reader = Reader::reply(reply)?;
    expect_tag(&mut reader, 3, "a rewind plan")?;
    let count = reader.count()?;
    let mut effects = Vec::with_capacity(count.min(reply.len()));
    for _ in 0..count {
        let tag = reader.tag_of(3, "a rewind effect")?;
        let id = NodeId(reader.nat()?);
        effects.push(if tag == 0 {
            RewindEffect::Start(id)
        } else if tag == 1 {
            RewindEffect::Stop(id)
        } else {
            RewindEffect::Restore(id)
        });
    }
    reader.end()?;
    Ok(effects)
}

/// Apply one op of a record the core took, exactly.
fn take<V: Clone>(tree: &mut SessionTree<V>, op: &TreeOp<V>) {
    match op {
        TreeOp::Put { id, parent, value } => tree.insert(
            *id,
            Node {
                parent: *parent,
                value: value.clone(),
            },
        ),
        TreeOp::Del { id } => tree.remove(*id),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn put(id: u64, parent: u64, value: u64) -> TreeRecord<u64> {
        TreeRecord::Do(TreeOp::Put {
            id: NodeId(id),
            parent: NodeId(parent),
            value,
        })
    }

    /// The live tree follows the core's answers through the real stepper,
    /// and equal values share one index: a node put again with its
    /// earlier value is the same node to a rewind plan.
    #[test]
    fn the_live_tree_follows_the_core() {
        let mut journal = Journal::new();
        let mut applied: Vec<Applied> = [
            put(1, 0, 10),
            put(2, 1, 20),
            put(3, 2, 30),
            put(4, 9, 40),
            put(2, 1, 21),
            put(2, 1, 20),
        ]
        .into_iter()
        .map(|record| journal.push(record))
        .collect();
        let same = journal.rewind_plan(2);
        applied.push(journal.push(TreeRecord::Do(TreeOp::Del { id: NodeId(2) })));
        applied.push(journal.push(TreeRecord::Rewind(vec![
            TreeOp::Del { id: NodeId(1) },
            TreeOp::Put {
                id: NodeId(5),
                parent: NodeId(0),
                value: 50,
            },
        ])));
        let rows = |tree: &SessionTree<u64>| -> Vec<(u64, u64, u64)> {
            tree.iter()
                .map(|(id, node)| (id.0, node.parent.0, node.value))
                .collect()
        };
        assert_eq!(
            (
                applied,
                same,
                rows(journal.tree()),
                rows(&journal.snapshot_at(3)),
                journal.rewind_plan(3),
                rows(&journal.snapshot_at(usize::MAX)),
            ),
            (
                vec![
                    Applied::Accepted,
                    Applied::Accepted,
                    Applied::Accepted,
                    Applied::Rejected,
                    Applied::Accepted,
                    Applied::Accepted,
                    Applied::Accepted,
                    Applied::Accepted,
                ],
                vec![RewindEffect::Stop(NodeId(3))],
                vec![(5, 0, 50)],
                vec![(1, 0, 10), (2, 1, 20), (3, 2, 30)],
                vec![
                    RewindEffect::Stop(NodeId(5)),
                    RewindEffect::Start(NodeId(1)),
                    RewindEffect::Start(NodeId(2)),
                    RewindEffect::Start(NodeId(3)),
                ],
                vec![(5, 0, 50)],
            )
        );
    }
}
