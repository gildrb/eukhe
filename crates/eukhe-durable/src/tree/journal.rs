//! The journal: the records of a session tree, in order, the live tree
//! they make, and the rule's stepper that decides each record.

use std::collections::HashMap;
use std::hash::Hash;

use super::rule::{Index, Rule, Taken};
use super::{Applied, Node, RewindEffect, SessionTree, TreeOp, TreeRecord};

/// The tree core answered something the journal cannot read.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum CoreError {
    /// A node value index the journal never gave the core.
    #[error("the tree core answered the unknown value index {0}")]
    UnknownValue(u64),
}

/// The values of a journal, each once: equal values get one index, so the
/// rule compares values by their indexes.
#[derive(Clone, Debug)]
struct Values<V> {
    list: Vec<V>,
    index: HashMap<V, Index>,
}

impl<V> Default for Values<V> {
    fn default() -> Self {
        Self {
            list: Vec::new(),
            index: HashMap::new(),
        }
    }
}

impl<V: Clone + Eq + Hash> Values<V> {
    fn index(&mut self, value: &V) -> Index {
        if let Some(index) = self.index.get(value) {
            return *index;
        }
        let index = self.list.len() as Index;
        self.list.push(value.clone());
        self.index.insert(value.clone(), index);
        index
    }

    fn get(&self, index: Index) -> Result<&V, CoreError> {
        usize::try_from(index)
            .ok()
            .and_then(|at| self.list.get(at))
            .ok_or(CoreError::UnknownValue(index))
    }

    fn op(&mut self, op: &TreeOp<V>) -> TreeOp<Index> {
        match op {
            TreeOp::Put { id, parent, value } => TreeOp::Put {
                id: *id,
                parent: *parent,
                value: self.index(value),
            },
            TreeOp::Del { id } => TreeOp::Del { id: *id },
        }
    }
}

/// The records of a session tree and the live tree. The journal keeps
/// every record, also a rejected one: a replay rejects it again.
#[derive(Clone, Debug)]
pub struct Journal<V> {
    records: Vec<TreeRecord<V>>,
    tree: SessionTree<V>,
    values: Values<V>,
    rule: Rule,
}

impl<V> Default for Journal<V> {
    fn default() -> Self {
        Self {
            records: Vec::new(),
            tree: SessionTree::default(),
            values: Values::default(),
            rule: Rule::default(),
        }
    }
}

impl<V: Clone + Eq + Hash> Journal<V> {
    /// An empty journal with an empty tree.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Apply `record` to the live tree and keep it. The rule decides; the
    /// live tree changes as it answers.
    pub fn push(&mut self, record: TreeRecord<V>) -> Applied {
        let indexed = match &record {
            TreeRecord::Do(op) => TreeRecord::Do(self.values.op(op)),
            TreeRecord::Rewind(ops) => {
                TreeRecord::Rewind(ops.iter().map(|op| self.values.op(op)).collect())
            }
        };
        let applied = match self.rule.note(indexed) {
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
    /// # Errors
    /// The core answered a value the journal does not have.
    pub fn snapshot_at(&self, n: usize) -> Result<SessionTree<V>, CoreError> {
        let mut tree = SessionTree::default();
        for (id, node) in self.rule.snap(n) {
            tree.insert(
                id,
                Node {
                    parent: node.parent,
                    value: self.values.get(node.value)?.clone(),
                },
            );
        }
        Ok(tree)
    }

    /// What a rewind from the live tree to the snapshot after the first
    /// `n` records does to the work of each node.
    #[must_use]
    pub fn rewind_plan(&self, n: usize) -> Vec<RewindEffect> {
        self.rule.plan(n)
    }
}

/// Apply one op of a record the rule took, exactly.
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
    use crate::tree::NodeId;

    fn put(id: u64, parent: u64, value: u64) -> TreeRecord<u64> {
        TreeRecord::Do(TreeOp::Put {
            id: NodeId(id),
            parent: NodeId(parent),
            value,
        })
    }

    /// The live tree follows the rule's answers, and equal values share
    /// one index: a node put again with its earlier value is the same node
    /// to a rewind plan.
    #[test]
    fn the_live_tree_follows_the_rule() {
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
                journal.snapshot_at(3).map(|tree| rows(&tree)),
                journal.rewind_plan(3),
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
                ],
                vec![RewindEffect::Stop(NodeId(3))],
                vec![(1, 0, 10)],
                Ok(vec![(1, 0, 10), (2, 1, 20), (3, 2, 30)]),
                vec![
                    RewindEffect::Start(NodeId(2)),
                    RewindEffect::Start(NodeId(3))
                ],
            )
        );
    }
}
