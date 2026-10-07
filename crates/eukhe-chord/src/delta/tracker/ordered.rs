//! An insertion-ordered map with JS `Map` semantics: setting an existing key
//! keeps its position, deleting and re-adding moves it to the end. Deletion
//! is O(1) through tombstones.

use std::collections::HashMap;
use std::hash::Hash;

#[derive(Clone, Debug)]
pub(crate) struct OrderedMap<K, V> {
    slots: Vec<Option<(K, V)>>,
    positions: HashMap<K, usize>,
}

impl<K, V> Default for OrderedMap<K, V> {
    fn default() -> Self {
        Self {
            slots: Vec::new(),
            positions: HashMap::new(),
        }
    }
}

impl<K: Clone + Eq + Hash, V> OrderedMap<K, V> {
    pub(crate) fn is_empty(&self) -> bool {
        self.positions.is_empty()
    }

    pub(crate) fn contains_key(&self, key: &K) -> bool {
        self.positions.contains_key(key)
    }

    pub(crate) fn get(&self, key: &K) -> Option<&V> {
        let position = *self.positions.get(key)?;
        self.slots[position].as_ref().map(|(_, value)| value)
    }

    pub(crate) fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        let position = *self.positions.get(key)?;
        self.slots[position].as_mut().map(|(_, value)| value)
    }

    /// `Map.set`: an existing key keeps its position.
    pub(crate) fn insert(&mut self, key: K, value: V) {
        if let Some(&position) = self.positions.get(&key) {
            if let Some((_, slot)) = self.slots[position].as_mut() {
                *slot = value;
            }
            return;
        }
        self.positions.insert(key.clone(), self.slots.len());
        self.slots.push(Some((key, value)));
    }

    /// `Map.delete`.
    pub(crate) fn remove(&mut self, key: &K) -> Option<V> {
        let position = self.positions.remove(key)?;
        let removed = self.slots[position].take().map(|(_, value)| value);
        if self.slots.len() > 32 && self.positions.len() * 2 < self.slots.len() {
            self.compact();
        }
        removed
    }

    fn compact(&mut self) {
        self.slots.retain(Option::is_some);
        for (position, slot) in self.slots.iter().enumerate() {
            if let Some((key, _)) = slot {
                self.positions.insert(key.clone(), position);
            }
        }
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = (&K, &V)> + '_ {
        self.slots
            .iter()
            .filter_map(|slot| slot.as_ref().map(|(key, value)| (key, value)))
    }

    pub(crate) fn keys(&self) -> impl Iterator<Item = &K> + '_ {
        self.iter().map(|(key, _)| key)
    }
}

/// An insertion-ordered set with JS `Set` semantics.
pub(crate) type OrderedSet<K> = OrderedMap<K, ()>;
