//! The rule of the session tree as one stepper, the shape of the compiled
//! Bend core's (`bend/tree.bend`, `Tr.core.step`): its state is the live
//! tree (ids, parents and value indexes) and the journal; an event is a
//! record, or a question about the tree after the first records of the
//! journal. Each call reads only the change it is given.

use std::collections::{BTreeMap, BTreeSet};

use super::{Node, NodeId, RewindEffect, TreeOp, TreeRecord};

/// A node value as the rule sees it: its index in the journal's values.
pub(super) type Index = u64;

/// The answer to a record.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Taken {
    /// The tree rejected the record and did not change.
    Kept,
    /// The tree took a put or a rewind: its own changes apply.
    Took,
    /// The tree took a delete: these nodes went, in id order.
    Cut(Vec<NodeId>),
}

/// The live tree and the journal of the rule.
#[derive(Clone, Debug, Default)]
pub(super) struct Rule {
    nodes: BTreeMap<NodeId, Node<Index>>,
    log: Vec<TreeRecord<Index>>,
}

impl Rule {
    /// Take one record into the journal and answer what it did.
    pub(super) fn note(&mut self, record: TreeRecord<Index>) -> Taken {
        let taken = self.apply(&record);
        self.log.push(record);
        taken
    }

    /// What a rewind from the live tree to the tree after the first `n`
    /// records does, in the order of its ops: first a stop for each node
    /// the target does not have, then a start or a restore for each node
    /// of the target the live tree does not have the same.
    pub(super) fn plan(&self, n: usize) -> Vec<RewindEffect> {
        let target = self.replay(n);
        let stops = self
            .nodes
            .keys()
            .filter(|id| !target.contains_key(id))
            .map(|id| RewindEffect::Stop(*id));
        let puts = target
            .iter()
            .filter(|(id, node)| self.nodes.get(id) != Some(*node))
            .map(|(id, _)| {
                if self.nodes.contains_key(id) {
                    RewindEffect::Restore(*id)
                } else {
                    RewindEffect::Start(*id)
                }
            });
        stops.chain(puts).collect()
    }

    /// The nodes of the tree after the first `n` records, in id order.
    pub(super) fn snap(&self, n: usize) -> Vec<(NodeId, Node<Index>)> {
        self.replay(n).into_iter().collect()
    }

    fn replay(&self, n: usize) -> BTreeMap<NodeId, Node<Index>> {
        let mut rule = Self::default();
        for record in self.log.iter().take(n) {
            rule.apply(record);
        }
        rule.nodes
    }

    fn apply(&mut self, record: &TreeRecord<Index>) -> Taken {
        match record {
            TreeRecord::Do(TreeOp::Put { id, parent, value }) => {
                if !may_hang(&self.nodes, *id, *parent) {
                    return Taken::Kept;
                }
                self.nodes.insert(
                    *id,
                    Node {
                        parent: *parent,
                        value: *value,
                    },
                );
                Taken::Took
            }
            TreeRecord::Do(TreeOp::Del { id }) => {
                if *id == NodeId::ROOT {
                    return Taken::Kept;
                }
                // One pass in id order: a node goes when its id or its
                // parent is gone, and then its id is gone.
                let mut gone = BTreeSet::from([*id]);
                let mut cut = Vec::new();
                self.nodes.retain(|key, node| {
                    let goes = gone.contains(key) || gone.contains(&node.parent);
                    if goes {
                        gone.insert(*key);
                        cut.push(*key);
                    }
                    !goes
                });
                Taken::Cut(cut)
            }
            TreeRecord::Rewind(ops) => {
                let mut next = self.nodes.clone();
                for op in ops {
                    match op {
                        TreeOp::Put { id, parent, value } => {
                            next.insert(
                                *id,
                                Node {
                                    parent: *parent,
                                    value: *value,
                                },
                            );
                        }
                        TreeOp::Del { id } => {
                            next.remove(id);
                        }
                    }
                }
                if !next
                    .iter()
                    .all(|(id, node)| may_hang(&next, *id, node.parent))
                {
                    return Taken::Kept;
                }
                self.nodes = next;
                Taken::Took
            }
        }
    }
}

/// A node `id` may hang under `parent`: the parent is less than the id,
/// and it is the root or a node.
fn may_hang(nodes: &BTreeMap<NodeId, Node<Index>>, id: NodeId, parent: NodeId) -> bool {
    parent < id && (parent == NodeId::ROOT || nodes.contains_key(&parent))
}
