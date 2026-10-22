//! The session tree: one tree holds all the state of a session. Each node
//! has an id, a parent and a value. The id of a node is more than the id
//! of its parent, so the tree has no cycles. [`NodeId::ROOT`] is the
//! parent of the top nodes; it is not a node.
//!
//! A [`TreeRecord`] changes the tree. A [`Journal`] keeps the records and
//! the live tree. A replay of the records makes the tree again; a replay
//! of a prefix is a snapshot.
//!
//! The rule (which record the tree takes, what a delete removes, what a
//! rewind does) is the Bend model `bend/tree.bend`: `LAWS.bend` section
//! (S1) states its laws and `PROOF.bend` proves them. The journal's core
//! (`rule.rs`) runs that rule as a stepper whose state is the live tree and
//! the journal, so a record costs its change and a lookup, not the tree;
//! node values reach the core as the journal's value indexes. The
//! [`SessionTree`] here is the journal's copy of the live tree with its
//! values: the journal changes it only as the core answers.
//!
//! [`StateTree`] (`state.rs`) is the session tree of a storage: the
//! commits make its records.
//!
//! This module does no I/O.

mod journal;
mod rule;
mod state;

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

pub use journal::{CoreError, Journal};
pub use state::{CursorAhead, CursorError, StateError, StateKey, StateKind, StateNode, StateTree};

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

/// The result of [`Journal::push`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Applied {
    /// The tree accepted the record and applied it.
    Accepted,
    /// The tree rejected the record and did not change.
    Rejected,
}

/// What a rewind does to the work of one node.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RewindEffect {
    /// The node is new: start its work.
    Start(NodeId),
    /// The node goes: stop its work.
    Stop(NodeId),
    /// The node changes: restore its earlier state.
    Restore(NodeId),
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

    /// Set node `id` (the journal, as the core took a record).
    fn insert(&mut self, id: NodeId, node: Node<V>) {
        self.nodes.insert(id, node);
    }

    /// Remove node `id` (the journal, as the core took a record).
    fn remove(&mut self, id: NodeId) {
        self.nodes.remove(&id);
    }
}
