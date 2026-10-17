//! The session tree: one tree holds all the state of a session. Each node
//! has an id, a parent and a value. The id of a node is more than the id
//! of its parent, so the tree has no cycles. [`NodeId::ROOT`] is the
//! parent of the top nodes; it is not a node.
//!
//! A [`TreeRecord`] changes the tree. A [`Journal`] keeps the records and
//! the live tree. A replay of the records makes the tree again; a replay
//! of a prefix is a snapshot.
//!
//! The Bend model `bend/tree.bend` is the specification. `LAWS.bend`
//! section (S1) states its laws and `PROOF.bend` proves them. The bridge
//! test (`bridge.rs`, with `bend/bridge_tree.bend`) runs this code and the
//! model on the same scenarios and requires the same transcript.
//!
//! [`StateTree`] (`state.rs`) is the session tree of a storage: the
//! commits make its records.
//!
//! This module does no I/O.

#[cfg(test)]
mod bridge;
mod diff;
mod journal;
mod state;

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

pub use diff::RewindEffect;
pub use journal::Journal;
pub use state::{CursorAhead, StateError, StateKey, StateKind, StateNode, StateTree};

/// The id of a node. The ids of a tree are unique.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(transparent)]
pub struct NodeId(pub u64);

impl NodeId {
    /// The root. It is the parent of the top nodes. It is not a node.
    pub const ROOT: Self = Self(0);
}

/// A node of the tree: its parent and its value.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Node<V> {
    /// The parent: [`NodeId::ROOT`] or a node with a smaller id.
    pub parent: NodeId,
    /// The value of the node.
    pub value: V,
}

/// One change to the tree.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "op", rename_all = "snake_case")]
pub enum TreeOp<V> {
    /// Set node `id`: insert it, or replace the node with this id.
    Put {
        /// The id of the node.
        id: NodeId,
        /// The parent of the node.
        parent: NodeId,
        /// The value of the node.
        value: V,
    },
    /// Remove node `id`.
    Del {
        /// The id of the node.
        id: NodeId,
    },
}

/// One record of the journal.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "record", content = "body", rename_all = "snake_case")]
pub enum TreeRecord<V> {
    /// One checked change. A `Put` is rejected when its parent is not
    /// less than its id, or when its parent is not the root and not a
    /// node. A `Del` removes the node and every node below it. A `Del` of
    /// [`NodeId::ROOT`] is rejected: the root is not a node.
    Do(TreeOp<V>),
    /// Exact changes, in order, to go back to an earlier tree. A `Put`
    /// sets the node and a `Del` removes only that node. The rewind is
    /// rejected when the result is not a sound tree.
    Rewind(Vec<TreeOp<V>>),
}

/// The result of [`SessionTree::apply`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Applied {
    /// The tree accepted the record and applied it.
    Accepted,
    /// The tree rejected the record and did not change.
    Rejected,
}

/// The tree of a session: nodes in ascending id order.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(transparent)]
pub struct SessionTree<V> {
    nodes: BTreeMap<NodeId, Node<V>>,
}

impl<V> Default for SessionTree<V> {
    fn default() -> Self {
        Self {
            nodes: BTreeMap::new(),
        }
    }
}

impl<V: Clone + Eq> SessionTree<V> {
    /// An empty tree.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Apply one record. A rejected record does not change the tree.
    pub fn apply(&mut self, record: &TreeRecord<V>) -> Applied {
        match record {
            TreeRecord::Do(TreeOp::Put { id, parent, value }) => {
                if !self.may_hang(*id, *parent) {
                    return Applied::Rejected;
                }
                self.nodes.insert(
                    *id,
                    Node {
                        parent: *parent,
                        value: value.clone(),
                    },
                );
                Applied::Accepted
            }
            TreeRecord::Do(TreeOp::Del { id }) => {
                if *id == NodeId::ROOT {
                    return Applied::Rejected;
                }
                self.prune(*id);
                Applied::Accepted
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
                                    value: value.clone(),
                                },
                            );
                        }
                        TreeOp::Del { id } => {
                            next.remove(id);
                        }
                    }
                }
                let next = Self { nodes: next };
                if !next.is_sound() {
                    return Applied::Rejected;
                }
                *self = next;
                Applied::Accepted
            }
        }
    }

    /// Remove node `id` and every node below it. One pass in id order: a
    /// node goes when its id or its parent is gone, and then its id is
    /// gone. A parent comes before its children in id order. When `id`
    /// is not a node, the nodes whose parent is `id` go all the same.
    fn prune(&mut self, id: NodeId) {
        let mut gone = BTreeSet::from([id]);
        self.nodes.retain(|key, node| {
            if gone.contains(key) || gone.contains(&node.parent) {
                gone.insert(*key);
                false
            } else {
                true
            }
        });
    }
}

impl<V> SessionTree<V> {
    /// The node `id`, if the tree has it.
    #[must_use]
    pub fn get(&self, id: NodeId) -> Option<&Node<V>> {
        self.nodes.get(&id)
    }

    /// The tree has node `id`.
    #[must_use]
    pub fn contains(&self, id: NodeId) -> bool {
        self.nodes.contains_key(&id)
    }

    /// The nodes whose parent is `id`, in id order.
    pub fn children(&self, id: NodeId) -> impl Iterator<Item = (NodeId, &Node<V>)> {
        self.iter().filter(move |(_, node)| node.parent == id)
    }

    /// All the nodes, in id order.
    pub fn iter(&self) -> impl Iterator<Item = (NodeId, &Node<V>)> {
        self.nodes.iter().map(|(id, node)| (*id, node))
    }

    /// The number of nodes.
    #[must_use]
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// The tree has no nodes.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Every node hangs under the root or a node with a smaller id. The
    /// ids are in ascending order by construction.
    #[must_use]
    pub fn is_sound(&self) -> bool {
        self.nodes
            .iter()
            .all(|(id, node)| self.may_hang(*id, node.parent))
    }

    /// A node `id` may hang under `parent`: the parent is less than the
    /// id, and it is the root or a node.
    fn may_hang(&self, id: NodeId, parent: NodeId) -> bool {
        parent < id && (parent == NodeId::ROOT || self.nodes.contains_key(&parent))
    }
}
