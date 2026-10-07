//! JSON objects with JS own-property order.

use std::sync::Arc;

use indexmap::IndexMap;

use super::JsonValue;

/// The canonical array index a property key names, if any: `"0"` or a decimal
/// without leading zeros below `4294967295`. JS orders these keys first,
/// ascending, in every object.
#[must_use]
pub fn canonical_array_index(key: &str) -> Option<u32> {
    let bytes = key.as_bytes();
    if bytes.is_empty() || bytes.len() > 10 {
        return None;
    }
    if key == "0" {
        return Some(0);
    }
    if !(b'1'..=b'9').contains(&bytes[0]) {
        return None;
    }
    let mut index: u64 = 0;
    for byte in bytes {
        if !byte.is_ascii_digit() {
            return None;
        }
        index = index * 10 + u64::from(byte - b'0');
        if index >= 4_294_967_295 {
            return None;
        }
    }
    u32::try_from(index).ok()
}

/// A JSON object whose key order is JS own-property order: canonical array
/// index keys ascending first, then every other key in insertion order.
/// Overwriting a key keeps its position; removing and re-adding a string key
/// moves it to the end.
///
/// ```
/// use eukhe_chord::json::{JsonObject, JsonValue};
/// let mut object = JsonObject::new();
/// object.insert("label", JsonValue::from("x"));
/// object.insert("2", JsonValue::from(2));
/// object.insert("1", JsonValue::from(1));
/// assert_eq!(object.keys().collect::<Vec<_>>(), ["1", "2", "label"]);
/// ```
#[derive(Clone, Default)]
pub struct JsonObject {
    entries: IndexMap<Arc<str>, JsonValue>,
    /// The leading entries that are canonical array indices.
    index_keys: usize,
}

impl JsonObject {
    /// An empty object.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// An empty object with room for `capacity` keys.
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            entries: IndexMap::with_capacity(capacity),
            index_keys: 0,
        }
    }

    /// Number of own keys.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the object has no keys.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// The value of an own key.
    #[must_use]
    pub fn get(&self, key: &str) -> Option<&JsonValue> {
        self.entries.get(key)
    }

    /// The value of an own key, mutably.
    pub fn get_mut(&mut self, key: &str) -> Option<&mut JsonValue> {
        self.entries.get_mut(key)
    }

    /// Whether `key` is an own key (`Object.hasOwn`).
    #[must_use]
    pub fn contains_key(&self, key: &str) -> bool {
        self.entries.contains_key(key)
    }

    /// Define `key` as an own data property (JS `defineProperty`): an existing
    /// key keeps its position, a new one is placed in JS order. Returns the
    /// previous value.
    pub fn insert(&mut self, key: impl Into<Arc<str>>, value: JsonValue) -> Option<JsonValue> {
        let key = key.into();
        if let Some(slot) = self.entries.get_mut(&*key) {
            return Some(std::mem::replace(slot, value));
        }
        if let Some(index) = canonical_array_index(&key) {
            let position =
                self.entries.as_slice()[..self.index_keys].partition_point(|existing, _| {
                    canonical_array_index(existing).is_some_and(|other| other < index)
                });
            self.entries.shift_insert(position, key, value);
            self.index_keys += 1;
        } else {
            self.entries.insert(key, value);
        }
        None
    }

    /// Delete an own key (JS `delete`), keeping the order of the others.
    pub fn remove(&mut self, key: &str) -> Option<JsonValue> {
        let (_, removed_key, value) = self.entries.shift_remove_full(key)?;
        if canonical_array_index(&removed_key).is_some() {
            self.index_keys -= 1;
        }
        Some(value)
    }

    /// Keys in JS own-property order (`Object.keys`).
    #[must_use]
    pub fn keys(&self) -> impl ExactSizeIterator<Item = &str> + '_ {
        self.entries.keys().map(|key| &**key)
    }

    /// Values in key order.
    #[must_use]
    pub fn values(&self) -> impl ExactSizeIterator<Item = &JsonValue> + '_ {
        self.entries.values()
    }

    /// Entries in key order.
    #[must_use]
    pub fn iter(&self) -> impl ExactSizeIterator<Item = (&str, &JsonValue)> + '_ {
        self.entries.iter().map(|(key, value)| (&**key, value))
    }

    /// Entries in key order with shared key strings.
    pub(crate) fn shared_iter(
        &self,
    ) -> impl ExactSizeIterator<Item = (&Arc<str>, &JsonValue)> + '_ {
        self.entries.iter()
    }
}

impl PartialEq for JsonObject {
    /// Deep equality ignoring key order.
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len()
            && self.entries.iter().all(|(key, value)| {
                other
                    .entries
                    .get(key)
                    .is_some_and(|candidate| candidate == value)
            })
    }
}

impl std::fmt::Debug for JsonObject {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut text = String::new();
        super::display::write_object(&mut text, self);
        formatter.write_str(&text)
    }
}

impl<K: Into<Arc<str>>, V: Into<JsonValue>> FromIterator<(K, V)> for JsonObject {
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        let mut object = Self::new();
        for (key, value) in iter {
            object.insert(key, value.into());
        }
        object
    }
}

impl<K: Into<Arc<str>>, V: Into<JsonValue>> Extend<(K, V)> for JsonObject {
    fn extend<I: IntoIterator<Item = (K, V)>>(&mut self, iter: I) {
        for (key, value) in iter {
            self.insert(key, value.into());
        }
    }
}

impl<'a> IntoIterator for &'a JsonObject {
    type Item = (&'a str, &'a JsonValue);
    type IntoIter = Box<dyn ExactSizeIterator<Item = (&'a str, &'a JsonValue)> + 'a>;

    fn into_iter(self) -> Self::IntoIter {
        Box::new(self.iter())
    }
}
