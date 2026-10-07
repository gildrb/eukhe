//! Draft handles: the Rust form of the TS overlay proxies (`Draft<T>` of
//! `delta/draft.ts` and the proxy traps of `tracker.ts`).

use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;

use super::ops::Seg;
use super::tracker::overlay::{ContextState, Item, NodeId, Supplied};
use super::tracker::{ContextCell, TrackerError};
use crate::json::JsonValue;

/// A mutable, change-scoped view of one object or array of a draft. Cloning
/// is cheap; two handles are equal when they are the same proxy (same change,
/// same container).
///
/// Every method fails with [`TrackerError::SettledOverlay`] once the change is
/// prepared, aborted, or made stale. Writes through a handle whose element was
/// removed from the draft are accepted and ignored.
///
/// ```
/// use eukhe_chord::delta::{track, DraftItem};
/// use eukhe_chord::json::JsonValue;
/// let tracker = track(JsonValue::parse(r#"{"rows":[{"v":1},{"v":2}]}"#).unwrap()).unwrap();
/// let change = tracker.begin_change();
/// let rows = change.state().unwrap().child("rows").unwrap();
/// let held = rows.child(1).unwrap();
/// rows.unshift([JsonValue::parse(r#"{"v":0}"#).unwrap()]).unwrap();
/// held.set("v", 9).unwrap(); // follows the element to index 2
/// assert_eq!(rows.value().unwrap().to_string(), r#"[{"v":0},{"v":1},{"v":9}]"#);
/// assert!(matches!(rows.get(0).unwrap(), Some(DraftItem::Draft(_))));
/// ```
#[derive(Clone)]
pub struct Draft {
    context: Arc<ContextCell>,
    node: NodeId,
    is_array: bool,
}

/// A value read from a draft: primitives by value, containers as handles.
#[derive(Clone, Debug, PartialEq)]
pub enum DraftItem {
    /// `null`, a boolean, number, or string.
    Value(JsonValue),
    /// An object or array of the draft.
    Draft(Draft),
}

impl DraftItem {
    /// The handle, for containers.
    #[must_use]
    pub fn as_draft(&self) -> Option<&Draft> {
        match self {
            Self::Draft(draft) => Some(draft),
            Self::Value(_) => None,
        }
    }

    /// The handle, for containers.
    #[must_use]
    pub fn into_draft(self) -> Option<Draft> {
        match self {
            Self::Draft(draft) => Some(draft),
            Self::Value(_) => None,
        }
    }

    /// The primitive value.
    #[must_use]
    pub fn as_value(&self) -> Option<&JsonValue> {
        match self {
            Self::Value(value) => Some(value),
            Self::Draft(_) => None,
        }
    }

    /// The current JSON content.
    ///
    /// # Errors
    ///
    /// [`TrackerError::SettledOverlay`] once the change settled, [`TrackerError::PreparedReadOnly`] for writes during preparation, and the operation's own TS errors.
    pub fn to_value(&self) -> Result<JsonValue, TrackerError> {
        match self {
            Self::Value(value) => Ok(value.clone()),
            Self::Draft(draft) => draft.value(),
        }
    }
}

/// A value placed into a draft. External values are copied (alias-free);
/// draft handles place a copy of their current content.
#[derive(Clone, Debug)]
pub enum Placement {
    /// An external value.
    Value(JsonValue),
    /// A draft handle (of this or another change).
    Draft(Draft),
}

impl<T: Into<JsonValue>> From<T> for Placement {
    fn from(value: T) -> Self {
        Self::Value(value.into())
    }
}

impl From<Draft> for Placement {
    fn from(draft: Draft) -> Self {
        Self::Draft(draft)
    }
}

impl From<&Draft> for Placement {
    fn from(draft: &Draft) -> Self {
        Self::Draft(draft.clone())
    }
}

impl From<DraftItem> for Placement {
    fn from(item: DraftItem) -> Self {
        match item {
            DraftItem::Value(value) => Self::Value(value),
            DraftItem::Draft(draft) => Self::Draft(draft),
        }
    }
}

impl From<&DraftItem> for Placement {
    fn from(item: &DraftItem) -> Self {
        Self::from(item.clone())
    }
}

impl PartialEq for Draft {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.context, &other.context) && self.node == other.node
    }
}

impl Eq for Draft {}

impl fmt::Debug for Draft {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("Draft")
            .field("node", &self.node)
            .field("is_array", &self.is_array)
            .finish_non_exhaustive()
    }
}

impl Draft {
    pub(crate) fn new(context: Arc<ContextCell>, node: NodeId, is_array: bool) -> Self {
        Self {
            context,
            node,
            is_array,
        }
    }

    fn wrap(&self, state: &ContextState, item: Item) -> DraftItem {
        match item {
            Item::Value(value) => DraftItem::Value(value),
            Item::Node(node) => DraftItem::Draft(Self::new(
                Arc::clone(&self.context),
                node,
                state.is_array(node),
            )),
        }
    }

    fn same_context(&self, other: &Draft) -> bool {
        Arc::ptr_eq(&self.context, &other.context)
    }

    /// Resolve placements; drafts of other changes are copied now, after
    /// `precheck` has run this handle's own checks (TS check order).
    fn supplied(
        &self,
        placements: Vec<Placement>,
        precheck: impl FnOnce(&mut ContextState) -> Result<(), TrackerError>,
    ) -> Result<Vec<Supplied>, TrackerError> {
        let foreign = placements.iter().any(
            |placement| matches!(placement, Placement::Draft(draft) if !self.same_context(draft)),
        );
        if foreign {
            precheck(&mut self.context.lock())?;
        }
        placements
            .into_iter()
            .map(|placement| match placement {
                Placement::Value(value) => Ok(Supplied::Value(value)),
                Placement::Draft(draft) if self.same_context(&draft) => {
                    Ok(Supplied::Node(draft.node))
                }
                Placement::Draft(draft) => {
                    let mut state = draft.context.lock();
                    state.assert_node(draft.node)?;
                    Ok(Supplied::Copied(state.clone_placement_node(draft.node)))
                }
            })
            .collect()
    }

    /// Whether this is an array (`Array.isArray(proxy)`; works after settle).
    #[must_use]
    pub fn is_array(&self) -> bool {
        self.is_array
    }

    /// `proxy[key]`: a primitive, a child handle, or `None` when absent. On
    /// arrays, `"length"` reads the length; inherited members (functions)
    /// read as `None`.
    ///
    /// # Errors
    ///
    /// [`TrackerError::SettledOverlay`] once the change settled, [`TrackerError::PreparedReadOnly`] for writes during preparation, and the operation's own TS errors.
    pub fn get(&self, key: impl Into<Seg>) -> Result<Option<DraftItem>, TrackerError> {
        let key = key.into();
        let mut state = self.context.lock();
        let item = state.get_property(self.node, &key)?;
        Ok(item.map(|item| self.wrap(&state, item)))
    }

    /// The child object or array handle at `key`.
    ///
    /// # Errors
    ///
    /// [`TrackerError::SettledOverlay`] once the change settled, [`TrackerError::PreparedReadOnly`] for writes during preparation, and the operation's own TS errors.
    pub fn child(&self, key: impl Into<Seg>) -> Result<Draft, TrackerError> {
        let key = key.into();
        match self.get(key.clone())? {
            Some(DraftItem::Draft(draft)) => Ok(draft),
            _ => Err(TrackerError::NotAContainer(key.to_string())),
        }
    }

    /// The current content (what `JSON.stringify(proxy)` serializes). Clean
    /// subtrees are shared with the base revision.
    ///
    /// # Errors
    ///
    /// [`TrackerError::SettledOverlay`] once the change settled, [`TrackerError::PreparedReadOnly`] for writes during preparation, and the operation's own TS errors.
    pub fn value(&self) -> Result<JsonValue, TrackerError> {
        let mut state = self.context.lock();
        state.assert_node(self.node)?;
        Ok(state.clone_node(self.node))
    }

    /// `proxy[key] = value`. Arrays accept indices up to the length and
    /// `"length"` (coerced like JS `Number(value)`).
    ///
    /// # Errors
    ///
    /// [`TrackerError::SettledOverlay`] once the change settled, [`TrackerError::PreparedReadOnly`] for writes during preparation, and the operation's own TS errors.
    pub fn set(
        &self,
        key: impl Into<Seg>,
        value: impl Into<Placement>,
    ) -> Result<(), TrackerError> {
        let key = key.into();
        let check_key = key.clone();
        let node = self.node;
        let mut supplied = self.supplied(vec![value.into()], |state| {
            state.check_set_property(node, &check_key)
        })?;
        let Some(supplied) = supplied.pop() else {
            return Ok(());
        };
        self.context.lock().set_property(self.node, &key, supplied)
    }

    /// `delete proxy[key]` (objects; arrays reject holes).
    ///
    /// # Errors
    ///
    /// [`TrackerError::SettledOverlay`] once the change settled, [`TrackerError::PreparedReadOnly`] for writes during preparation, and the operation's own TS errors.
    pub fn delete(&self, key: impl Into<Seg>) -> Result<(), TrackerError> {
        self.context.lock().delete_property(self.node, &key.into())
    }

    /// `key in proxy`: own keys of objects; arrays also report `length` and
    /// their prototype members.
    ///
    /// # Errors
    ///
    /// [`TrackerError::SettledOverlay`] once the change settled, [`TrackerError::PreparedReadOnly`] for writes during preparation, and the operation's own TS errors.
    pub fn has(&self, key: impl Into<Seg>) -> Result<bool, TrackerError> {
        self.context.lock().has_property(self.node, &key.into())
    }

    /// `Object.keys(proxy)`: array indices, or object keys in JS order.
    ///
    /// # Errors
    ///
    /// [`TrackerError::SettledOverlay`] once the change settled, [`TrackerError::PreparedReadOnly`] for writes during preparation, and the operation's own TS errors.
    pub fn keys(&self) -> Result<Vec<String>, TrackerError> {
        let keys = self.context.lock().keys(self.node)?;
        Ok(keys.iter().map(ToString::to_string).collect())
    }

    /// Array length, or number of object keys.
    ///
    /// # Errors
    ///
    /// [`TrackerError::SettledOverlay`] once the change settled, [`TrackerError::PreparedReadOnly`] for writes during preparation, and the operation's own TS errors.
    pub fn len(&self) -> Result<usize, TrackerError> {
        let mut state = self.context.lock();
        state.assert_node(self.node)?;
        if self.is_array {
            return Ok(state.array_length(self.node));
        }
        Ok(state.own_keys(self.node).len())
    }

    /// Whether [`Draft::len`] is zero.
    ///
    /// # Errors
    ///
    /// [`TrackerError::SettledOverlay`] once the change settled, [`TrackerError::PreparedReadOnly`] for writes during preparation, and the operation's own TS errors.
    pub fn is_empty(&self) -> Result<bool, TrackerError> {
        Ok(self.len()? == 0)
    }

    /// `proxy.length = length`: shrink, or grow with `null`s.
    ///
    /// # Errors
    ///
    /// [`TrackerError::SettledOverlay`] once the change settled, [`TrackerError::PreparedReadOnly`] for writes during preparation, and the operation's own TS errors.
    #[allow(clippy::cast_precision_loss)] // JS converts the length to a double too
    pub fn set_len(&self, length: usize) -> Result<(), TrackerError> {
        let number = JsonValue::try_from(length as f64).unwrap_or_default();
        self.context
            .lock()
            .set_property(self.node, &Seg::from("length"), Supplied::Value(number))
    }

    /// `push(...items)`; returns the new length. Nothing is inserted when a
    /// placement fails.
    ///
    /// # Errors
    ///
    /// [`TrackerError::SettledOverlay`] once the change settled, [`TrackerError::PreparedReadOnly`] for writes during preparation, and the operation's own TS errors.
    pub fn push<I>(&self, items: I) -> Result<usize, TrackerError>
    where
        I: IntoIterator,
        I::Item: Into<Placement>,
    {
        let node = self.node;
        let supplied = self.supplied(items.into_iter().map(Into::into).collect(), |state| {
            state.mutator_node(node)
        })?;
        self.context.lock().push(self.node, supplied)
    }

    /// `pop()`.
    ///
    /// # Errors
    ///
    /// [`TrackerError::SettledOverlay`] once the change settled, [`TrackerError::PreparedReadOnly`] for writes during preparation, and the operation's own TS errors.
    pub fn pop(&self) -> Result<Option<DraftItem>, TrackerError> {
        let mut state = self.context.lock();
        let item = state.pop(self.node)?;
        Ok(item.map(|item| self.wrap(&state, item)))
    }

    /// `shift()`.
    ///
    /// # Errors
    ///
    /// [`TrackerError::SettledOverlay`] once the change settled, [`TrackerError::PreparedReadOnly`] for writes during preparation, and the operation's own TS errors.
    pub fn shift(&self) -> Result<Option<DraftItem>, TrackerError> {
        let mut state = self.context.lock();
        let item = state.shift(self.node)?;
        Ok(item.map(|item| self.wrap(&state, item)))
    }

    /// `unshift(...items)`; returns the new length.
    ///
    /// # Errors
    ///
    /// [`TrackerError::SettledOverlay`] once the change settled, [`TrackerError::PreparedReadOnly`] for writes during preparation, and the operation's own TS errors.
    pub fn unshift<I>(&self, items: I) -> Result<usize, TrackerError>
    where
        I: IntoIterator,
        I::Item: Into<Placement>,
    {
        let node = self.node;
        let supplied = self.supplied(items.into_iter().map(Into::into).collect(), |state| {
            state.mutator_node(node)
        })?;
        self.context.lock().unshift(self.node, supplied)
    }

    /// `splice(start, deleteCount, ...items)` with JS index semantics
    /// (negative `start` counts from the end; `i64::MAX` removes to the end;
    /// `splice(0, 0, [])` is the zero-argument form). Returns the removed
    /// entries.
    ///
    /// # Errors
    ///
    /// [`TrackerError::SettledOverlay`] once the change settled, [`TrackerError::PreparedReadOnly`] for writes during preparation, and the operation's own TS errors.
    pub fn splice<I>(
        &self,
        start: i64,
        delete_count: i64,
        items: I,
    ) -> Result<Vec<DraftItem>, TrackerError>
    where
        I: IntoIterator,
        I::Item: Into<Placement>,
    {
        let node = self.node;
        let supplied = self.supplied(items.into_iter().map(Into::into).collect(), |state| {
            state.mutator_node(node)
        })?;
        let mut state = self.context.lock();
        let removed = state.splice(self.node, start, delete_count, supplied)?;
        Ok(removed
            .into_iter()
            .map(|item| self.wrap(&state, item))
            .collect())
    }

    /// `reverse()`; returns this handle.
    ///
    /// # Errors
    ///
    /// [`TrackerError::SettledOverlay`] once the change settled, [`TrackerError::PreparedReadOnly`] for writes during preparation, and the operation's own TS errors.
    pub fn reverse(&self) -> Result<Draft, TrackerError> {
        self.context.lock().reverse(self.node)?;
        Ok(self.clone())
    }

    /// `sort()` with the JS default order: `String(value)` compared by UTF-16
    /// code units. Stable.
    ///
    /// # Errors
    ///
    /// [`TrackerError::SettledOverlay`] once the change settled, [`TrackerError::PreparedReadOnly`] for writes during preparation, and the operation's own TS errors.
    pub fn sort(&self) -> Result<Draft, TrackerError> {
        let mut state = self.context.lock();
        let mut plan = state.sort_prepare(self.node)?;
        let mut strings: HashMap<i64, String> = HashMap::with_capacity(plan.order.len());
        for &token in &plan.order {
            if let Some(item) = plan.value(token) {
                let item = match item {
                    Item::Value(value) => Item::Value(value.clone()),
                    Item::Node(node) => Item::Node(*node),
                };
                strings.insert(token, state.item_string(&item));
            }
        }
        let empty = String::new();
        let mut order = std::mem::take(&mut plan.order);
        merge_sort(&mut order, &mut |left: i64, right: i64| {
            let left = strings.get(&left).unwrap_or(&empty);
            let right = strings.get(&right).unwrap_or(&empty);
            left.encode_utf16().cmp(right.encode_utf16())
        });
        plan.order = order;
        state.sort_finish(self.node, &plan)?;
        Ok(self.clone())
    }

    /// `sort(comparator)`. Stable. The comparator runs without the draft
    /// locked, so it may read (or, out of contract, write) the draft.
    ///
    /// # Errors
    ///
    /// [`TrackerError::SettledOverlay`] once the change settled, [`TrackerError::PreparedReadOnly`] for writes during preparation, and the operation's own TS errors.
    pub fn sort_by<F>(&self, mut compare: F) -> Result<Draft, TrackerError>
    where
        F: FnMut(&DraftItem, &DraftItem) -> Ordering,
    {
        let (mut plan, items) = {
            let mut state = self.context.lock();
            let plan = state.sort_prepare(self.node)?;
            let mut items: HashMap<i64, DraftItem> = HashMap::with_capacity(plan.order.len());
            for &token in &plan.order {
                if let Some(item) = plan.value(token) {
                    let item = match item {
                        Item::Value(value) => DraftItem::Value(value.clone()),
                        Item::Node(node) => DraftItem::Draft(Self::new(
                            Arc::clone(&self.context),
                            *node,
                            state.is_array(*node),
                        )),
                    };
                    items.insert(token, item);
                }
            }
            (plan, items)
        };
        let null = DraftItem::Value(JsonValue::Null);
        let mut order = std::mem::take(&mut plan.order);
        merge_sort(&mut order, &mut |left: i64, right: i64| {
            compare(
                items.get(&left).unwrap_or(&null),
                items.get(&right).unwrap_or(&null),
            )
        });
        plan.order = order;
        self.context.lock().sort_finish(self.node, &plan)?;
        Ok(self.clone())
    }

    /// `fill(value, start, end)` with JS index semantics (pass `0, i64::MAX`
    /// for the whole array). Each filled entry is an independent copy.
    ///
    /// # Errors
    ///
    /// [`TrackerError::SettledOverlay`] once the change settled, [`TrackerError::PreparedReadOnly`] for writes during preparation, and the operation's own TS errors.
    pub fn fill(
        &self,
        value: impl Into<Placement>,
        start: i64,
        end: i64,
    ) -> Result<Draft, TrackerError> {
        let node = self.node;
        let mut supplied = self.supplied(vec![value.into()], |state| state.mutator_node(node))?;
        let Some(supplied) = supplied.pop() else {
            return Ok(self.clone());
        };
        self.context.lock().fill(self.node, &supplied, start, end)?;
        Ok(self.clone())
    }

    /// `copyWithin(target, start, end)` by value, with JS index semantics.
    ///
    /// # Errors
    ///
    /// [`TrackerError::SettledOverlay`] once the change settled, [`TrackerError::PreparedReadOnly`] for writes during preparation, and the operation's own TS errors.
    pub fn copy_within(&self, target: i64, start: i64, end: i64) -> Result<Draft, TrackerError> {
        self.context
            .lock()
            .copy_within(self.node, target, start, end)?;
        Ok(self.clone())
    }

    /// The node's base container (for retention tests).
    #[cfg(test)]
    pub(crate) fn base_for_test(&self) -> Option<JsonValue> {
        let state = self.context.lock();
        state.nodes.get(self.node).map(|node| node.base.clone())
    }
}

/// Stable merge sort that never panics on inconsistent comparators. Small
/// runs use insertion sort comparing `(later, earlier)` like V8's binary
/// insertion.
fn merge_sort<T: Copy, F: FnMut(T, T) -> Ordering>(items: &mut [T], compare: &mut F) {
    let length = items.len();
    if length <= 1 {
        return;
    }
    if length <= 16 {
        for index in 1..length {
            let mut at = index;
            while at > 0 && compare(items[at], items[at - 1]) == Ordering::Less {
                items.swap(at, at - 1);
                at -= 1;
            }
        }
        return;
    }
    let middle = length / 2;
    merge_sort(&mut items[..middle], compare);
    merge_sort(&mut items[middle..], compare);
    let left = items[..middle].to_vec();
    let right = items[middle..].to_vec();
    let (mut left_at, mut right_at) = (0, 0);
    for slot in items.iter_mut() {
        let take_right = left_at == left.len()
            || (right_at < right.len()
                && compare(right[right_at], left[left_at]) == Ordering::Less);
        if take_right {
            *slot = right[right_at];
            right_at += 1;
        } else {
            *slot = left[left_at];
            left_at += 1;
        }
    }
}
