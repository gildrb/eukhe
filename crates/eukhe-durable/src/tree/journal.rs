//! The journal: the records of a session tree, in order, and the live
//! tree they make.

use super::{Applied, SessionTree, TreeRecord};

/// The records of a session tree and the live tree. The journal keeps
/// every record, also a rejected one: a replay rejects it again.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Journal<V> {
    records: Vec<TreeRecord<V>>,
    tree: SessionTree<V>,
}

impl<V> Default for Journal<V> {
    fn default() -> Self {
        Self {
            records: Vec::new(),
            tree: SessionTree::default(),
        }
    }
}

impl<V: Clone + Eq> Journal<V> {
    /// An empty journal with an empty tree.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Apply `record` to the live tree and keep it.
    pub fn push(&mut self, record: TreeRecord<V>) -> Applied {
        let applied = self.tree.apply(&record);
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

    /// The tree that `records` make, in order, from the empty tree.
    pub fn replay<'a>(records: impl IntoIterator<Item = &'a TreeRecord<V>>) -> SessionTree<V>
    where
        V: 'a,
    {
        let mut tree = SessionTree::new();
        for record in records {
            tree.apply(record);
        }
        tree
    }

    /// The snapshot after the first `n` records: their replay. All the
    /// records when `n` is more than their count.
    #[must_use]
    pub fn snapshot_at(&self, n: usize) -> SessionTree<V> {
        Self::replay(self.records.iter().take(n))
    }
}
