//! Rewind: the ops that turn one tree into another, and what a rewind
//! does to the work that hangs on the nodes.

use super::{NodeId, SessionTree, TreeOp, TreeRecord};

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

impl<V: Clone + Eq> SessionTree<V> {
    /// The ops that turn this tree into `target`: first a `Del` for each
    /// node that `target` does not have, in id order; then a `Put` for
    /// each node of `target` that this tree does not have the same, in id
    /// order.
    #[must_use]
    pub fn diff(&self, target: &Self) -> Vec<TreeOp<V>> {
        let dels = self
            .iter()
            .filter(|(id, _)| !target.contains(*id))
            .map(|(id, _)| TreeOp::Del { id });
        let puts = target
            .iter()
            .filter(|(id, node)| self.get(*id) != Some(*node))
            .map(|(id, node)| TreeOp::Put {
                id,
                parent: node.parent,
                value: node.value.clone(),
            });
        dels.chain(puts).collect()
    }

    /// The record that rewinds this tree to `target`:
    /// `Rewind(self.diff(target))`.
    #[must_use]
    pub fn rewind_to(&self, target: &Self) -> TreeRecord<V> {
        TreeRecord::Rewind(self.diff(target))
    }

    /// What the rewind to `target` does, in the order of
    /// [`Self::diff`]: a `Del` stops a node; a `Put` starts a node that
    /// this tree does not have, and restores a node that it has.
    #[must_use]
    pub fn rewind_effects(&self, target: &Self) -> Vec<RewindEffect> {
        self.diff(target)
            .iter()
            .map(|op| match op {
                TreeOp::Del { id } => RewindEffect::Stop(*id),
                TreeOp::Put { id, .. } if self.contains(*id) => RewindEffect::Restore(*id),
                TreeOp::Put { id, .. } => RewindEffect::Start(*id),
            })
            .collect()
    }
}
