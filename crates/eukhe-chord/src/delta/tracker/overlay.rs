//! The overlay draft of one change: nodes over base containers, object write
//! and delete sets, array piece overlays, and the proxy-trap operations
//! (`getProperty`, `setProperty`, `deleteProperty`, `hasProperty`,
//! `ownKeys`, cloning) of `tracker.ts`.

use std::collections::HashMap;
use std::sync::Arc;

use super::ordered::{OrderedMap, OrderedSet};
use super::pieces::{ArrayOverlay, Piece, PieceKind, SourceId};
use super::TrackerError;
use crate::delta::ops::{Path, Seg};
use crate::json::{canonical_array_index, copy_json, js_string, JsonNumber, JsonObject, JsonValue};

/// Index of a node in its context.
pub(crate) type NodeId = usize;

/// Where a node's base container sits: under an object key, or at a source
/// index of a base array or an inserted source. Together with the container
/// identity it keys the node, so held handles follow their element through
/// reindexing.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Slot {
    Root,
    Key(NodeId, Arc<str>),
    Entry(NodeId, PieceKind, usize),
}

impl Slot {
    pub(crate) fn parent(&self) -> Option<NodeId> {
        match self {
            Self::Root => None,
            Self::Key(parent, _) | Self::Entry(parent, ..) => Some(*parent),
        }
    }
}

#[derive(Debug)]
pub(crate) struct OverlayNode {
    pub(crate) base: JsonValue,
    pub(crate) slot: Slot,
    pub(crate) parent_placement: bool,
    pub(crate) writes: OrderedMap<Arc<str>, JsonValue>,
    pub(crate) deletes: OrderedSet<Arc<str>>,
    pub(crate) readded: OrderedSet<Arc<str>>,
    pub(crate) array: Option<ArrayOverlay>,
    pub(crate) dirty: bool,
    pub(crate) subtree_dirty: bool,
    pub(crate) prepared_path: Option<Path>,
}

/// The lifecycle of a context.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Status {
    Open,
    Prepared,
    Consumed,
    Aborted,
    Stale,
}

/// A value being placed into the draft.
pub(crate) enum Supplied {
    /// An external value: copied on placement.
    Value(JsonValue),
    /// A draft of another context, already copied.
    Copied(JsonValue),
    /// A draft node of this context: its current content is copied.
    Node(NodeId),
}

/// A property read: a primitive, or the node of a container.
pub(crate) enum Item {
    Value(JsonValue),
    Node(NodeId),
}

/// Property names on the array prototype chain (`property in Array.prototype`).
const ARRAY_PROTOTYPE_KEYS: [&str; 49] = [
    "__defineGetter__",
    "__defineSetter__",
    "__lookupGetter__",
    "__lookupSetter__",
    "__proto__",
    "at",
    "concat",
    "constructor",
    "copyWithin",
    "entries",
    "every",
    "fill",
    "filter",
    "find",
    "findIndex",
    "findLast",
    "findLastIndex",
    "flat",
    "flatMap",
    "forEach",
    "hasOwnProperty",
    "includes",
    "indexOf",
    "isPrototypeOf",
    "join",
    "keys",
    "lastIndexOf",
    "length",
    "map",
    "pop",
    "propertyIsEnumerable",
    "push",
    "reduce",
    "reduceRight",
    "reverse",
    "shift",
    "slice",
    "some",
    "sort",
    "splice",
    "toLocaleString",
    "toReversed",
    "toSorted",
    "toSpliced",
    "toString",
    "unshift",
    "valueOf",
    "values",
    "with",
];

#[derive(Debug)]
#[allow(clippy::struct_excessive_bools)] // the independent flags of the TS overlay context
pub(crate) struct ContextState {
    pub(crate) owner: u64,
    pub(crate) base_revision: u64,
    pub(crate) status: Status,
    pub(crate) root: Option<NodeId>,
    pub(crate) nodes: Vec<OverlayNode>,
    node_index: HashMap<(Slot, usize), NodeId>,
    pub(crate) sources: Vec<Vec<JsonValue>>,
    pub(crate) dirty: Vec<NodeId>,
    pub(crate) ops: Option<Arc<Vec<crate::delta::Op>>>,
    pub(crate) replacement: bool,
    pub(crate) base_value: Option<JsonValue>,
    pub(crate) overlay_released: bool,
    pub(crate) simple_object_materialization: bool,
    /// Whether the tracker's registry still lists this context
    /// (`registryRef`).
    pub(crate) registered: bool,
}

/// `arrayIndex(property)` for a segment.
pub(crate) fn array_index(segment: &Seg) -> Option<usize> {
    match segment {
        Seg::Index(index) => (*index < 4_294_967_295).then_some(*index),
        Seg::Key(key) => canonical_array_index(key).and_then(|index| usize::try_from(index).ok()),
    }
}

impl ContextState {
    pub(crate) fn new(
        owner: u64,
        base_revision: u64,
        root: JsonValue,
        replacement: bool,
        base: JsonValue,
    ) -> Self {
        let mut state = Self {
            owner,
            base_revision,
            status: Status::Open,
            root: None,
            nodes: Vec::new(),
            node_index: HashMap::new(),
            sources: Vec::new(),
            dirty: Vec::new(),
            ops: None,
            replacement,
            base_value: Some(base),
            overlay_released: false,
            simple_object_materialization: false,
            registered: false,
        };
        state.root = Some(state.create_node(root, Slot::Root, /*placement*/ false));
        state
    }

    pub(crate) fn is_settled(&self) -> bool {
        self.overlay_released
            || matches!(
                self.status,
                Status::Consumed | Status::Aborted | Status::Stale
            )
    }

    pub(crate) fn assert_readable(&self) -> Result<(), TrackerError> {
        if self.is_settled() {
            return Err(TrackerError::SettledOverlay);
        }
        Ok(())
    }

    pub(crate) fn assert_writable(&self) -> Result<(), TrackerError> {
        self.assert_readable()?;
        if self.status != Status::Open {
            return Err(TrackerError::PreparedReadOnly);
        }
        Ok(())
    }

    /// Readable and the node exists (a released overlay has no nodes).
    pub(crate) fn assert_node(&self, node: NodeId) -> Result<(), TrackerError> {
        self.assert_readable()?;
        if node >= self.nodes.len() {
            return Err(TrackerError::SettledOverlay);
        }
        Ok(())
    }

    /// Drop every overlay reference (`clearContext` /
    /// `releaseOverlayReferences`): held handles see a settled overlay.
    pub(crate) fn release(&mut self) {
        self.registered = false;
        self.overlay_released = true;
        self.dirty = Vec::new();
        self.nodes = Vec::new();
        self.node_index = HashMap::new();
        self.sources = Vec::new();
        self.ops = None;
        self.root = None;
        self.base_value = None;
    }

    pub(crate) fn is_array(&self, node: NodeId) -> bool {
        self.nodes[node].base.is_array()
    }

    pub(crate) fn parent(&self, node: NodeId) -> Option<NodeId> {
        self.nodes[node].slot.parent()
    }

    pub(crate) fn create_node(&mut self, base: JsonValue, slot: Slot, placement: bool) -> NodeId {
        let address = base.container_address().unwrap_or(0);
        let key = (slot, address);
        if let Some(existing) = self.node_index.get(&key) {
            return *existing;
        }
        let id = self.nodes.len();
        self.nodes.push(OverlayNode {
            base,
            slot: key.0.clone(),
            parent_placement: placement,
            writes: OrderedMap::default(),
            deletes: OrderedSet::default(),
            readded: OrderedSet::default(),
            array: None,
            dirty: false,
            subtree_dirty: false,
            prepared_path: None,
        });
        self.node_index.insert(key, id);
        id
    }

    /// The node holding `value` at `slot`, if one was created.
    pub(crate) fn find_node(&self, slot: Slot, value: &JsonValue) -> Option<NodeId> {
        let address = value.container_address()?;
        self.node_index.get(&(slot, address)).copied()
    }

    pub(crate) fn array(&mut self, node: NodeId) -> &mut ArrayOverlay {
        let length = self.nodes[node]
            .base
            .as_array()
            .map_or(0, <[JsonValue]>::len);
        self.nodes[node]
            .array
            .get_or_insert_with(|| ArrayOverlay::new(length))
    }

    pub(crate) fn array_length(&mut self, node: NodeId) -> usize {
        self.array(node).length()
    }

    fn base_has(&self, node: NodeId, key: &str) -> bool {
        self.nodes[node]
            .base
            .as_object()
            .is_some_and(|object| object.contains_key(key))
    }

    fn base_get(&self, node: NodeId, key: &str) -> Option<&JsonValue> {
        self.nodes[node]
            .base
            .as_object()
            .and_then(|object| object.get(key))
    }

    pub(crate) fn has_object_write(&self, node: NodeId, key: &Arc<str>) -> bool {
        self.nodes[node].writes.contains_key(key)
    }

    pub(crate) fn is_object_deleted(&self, node: NodeId, key: &Arc<str>) -> bool {
        self.nodes[node].deletes.contains_key(key)
    }

    pub(crate) fn object_has(&self, node: NodeId, key: &Arc<str>) -> bool {
        if self.is_object_deleted(node, key) {
            return false;
        }
        self.has_object_write(node, key) || self.base_has(node, key)
    }

    /// The written or base value of `key` (`undefined` → `None`).
    pub(crate) fn object_value(&self, node: NodeId, key: &Arc<str>) -> Option<JsonValue> {
        if let Some(value) = self.nodes[node].writes.get(key) {
            return Some(value.clone());
        }
        self.base_get(node, key).cloned()
    }

    pub(crate) fn mark_dirty(&mut self, node: NodeId) {
        if self.nodes[node].dirty {
            return;
        }
        self.nodes[node].dirty = true;
        self.dirty.push(node);
        let mut parent = self.parent(node);
        while let Some(current) = parent {
            self.nodes[current].subtree_dirty = true;
            parent = self.parent(current);
        }
    }

    /// The current value of a source entry.
    pub(crate) fn entry_value_at(
        &mut self,
        node: NodeId,
        kind: PieceKind,
        source_index: usize,
    ) -> JsonValue {
        match kind {
            PieceKind::Base => {
                if let Some(value) = self.array(node).base_overrides.get(&source_index) {
                    return value.clone();
                }
                self.nodes[node]
                    .base
                    .get_index(source_index)
                    .cloned()
                    .unwrap_or_default()
            }
            PieceKind::Insert(source) => {
                if let Some(value) = self
                    .array(node)
                    .insert_overrides
                    .get(&source)
                    .and_then(|overrides| overrides.get(&source_index))
                {
                    return value.clone();
                }
                self.sources[source]
                    .get(source_index)
                    .cloned()
                    .unwrap_or_default()
            }
        }
    }

    pub(crate) fn has_entry_override_at(
        &mut self,
        node: NodeId,
        kind: PieceKind,
        source_index: usize,
    ) -> bool {
        let overlay = self.array(node);
        match kind {
            PieceKind::Base => overlay.base_overrides.contains_key(&source_index),
            PieceKind::Insert(source) => overlay
                .insert_overrides
                .get(&source)
                .is_some_and(|overrides| overrides.contains_key(&source_index)),
        }
    }

    pub(crate) fn locate(
        &mut self,
        node: NodeId,
        index: usize,
    ) -> Result<(Piece, usize), TrackerError> {
        self.array(node)
            .locate(index)
            .ok_or(TrackerError::OverlayIndexOutOfRange)
    }

    /// `getProperty`.
    pub(crate) fn get_property(
        &mut self,
        node: NodeId,
        property: &Seg,
    ) -> Result<Option<Item>, TrackerError> {
        self.assert_node(node)?;
        if self.is_array(node) {
            if matches!(property, Seg::Key(key) if &**key == "length") {
                return Ok(Some(Item::Value(length_json(self.array_length(node)))));
            }
            return match array_index(property) {
                Some(index) => self.get_array_index(node, index),
                // Inherited array members are functions: no JSON value.
                None => Ok(None),
            };
        }
        let key = property.object_key();
        if !self.object_has(node, &key) {
            return Ok(None);
        }
        let Some(value) = self.object_value(node, &key) else {
            return Ok(None);
        };
        if !value.is_container() {
            return Ok(Some(Item::Value(value)));
        }
        let placement = self.has_object_write(node, &key);
        Ok(Some(Item::Node(self.create_node(
            value,
            Slot::Key(node, key),
            placement,
        ))))
    }

    /// `getArrayIndex`.
    pub(crate) fn get_array_index(
        &mut self,
        node: NodeId,
        index: usize,
    ) -> Result<Option<Item>, TrackerError> {
        if index >= self.array_length(node) {
            return Ok(None);
        }
        let (piece, offset) = self.locate(node, index)?;
        let source_index = piece.at(offset);
        let value = self.entry_value_at(node, piece.kind, source_index);
        if !value.is_container() {
            return Ok(Some(Item::Value(value)));
        }
        let placement = piece.kind != PieceKind::Base
            || self.has_entry_override_at(node, piece.kind, source_index);
        Ok(Some(Item::Node(self.create_node(
            value,
            Slot::Entry(node, piece.kind, source_index),
            placement,
        ))))
    }

    /// The pre-placement checks of `setProperty`, in order, for callers that
    /// must copy a draft of another context before placing it.
    pub(crate) fn check_set_property(
        &mut self,
        node: NodeId,
        property: &Seg,
    ) -> Result<(), TrackerError> {
        self.assert_node(node)?;
        self.assert_writable()?;
        if self.is_array(node) && !matches!(property, Seg::Key(key) if &**key == "length") {
            let Some(index) = array_index(property) else {
                return Err(TrackerError::OnlyIndicesAndLength);
            };
            if index > self.array_length(node) {
                return Err(TrackerError::ArrayHoles);
            }
        }
        Ok(())
    }

    /// `setProperty`.
    pub(crate) fn set_property(
        &mut self,
        node: NodeId,
        property: &Seg,
        supplied: Supplied,
    ) -> Result<(), TrackerError> {
        self.assert_node(node)?;
        self.assert_writable()?;
        if self.is_array(node) {
            if matches!(property, Seg::Key(key) if &**key == "length") {
                let number = self.supplied_number(&supplied)?;
                let length = to_array_length(number)?;
                self.set_array_length(node, length);
                return Ok(());
            }
            let Some(index) = array_index(property) else {
                return Err(TrackerError::OnlyIndicesAndLength);
            };
            if index > self.array_length(node) {
                return Err(TrackerError::ArrayHoles);
            }
            let stored = self.clone_placement(supplied)?;
            self.set_array_index(node, index, stored)?;
            return Ok(());
        }
        let key = property.object_key();
        let stored = self.clone_placement(supplied)?;
        let current = self.object_value(node, &key);
        let was_deleted = self.is_object_deleted(node, &key);
        if !was_deleted
            && !stored.is_container()
            && current
                .as_ref()
                .is_some_and(|current| current.strict_equals(&stored))
        {
            return Ok(());
        }
        self.nodes[node].writes.insert(Arc::clone(&key), stored);
        if was_deleted && self.base_has(node, &key) {
            self.nodes[node].readded.insert(Arc::clone(&key), ());
        }
        self.nodes[node].deletes.remove(&key);
        self.mark_dirty(node);
        Ok(())
    }

    /// `deleteProperty`.
    pub(crate) fn delete_property(
        &mut self,
        node: NodeId,
        property: &Seg,
    ) -> Result<(), TrackerError> {
        self.assert_node(node)?;
        self.assert_writable()?;
        if self.is_array(node) {
            return Err(TrackerError::ArrayHoles);
        }
        let key = property.object_key();
        if !self.object_has(node, &key) {
            return Ok(());
        }
        self.nodes[node].writes.remove(&key);
        self.nodes[node].readded.remove(&key);
        self.nodes[node].deletes.insert(key, ());
        self.mark_dirty(node);
        Ok(())
    }

    /// `hasProperty`.
    pub(crate) fn has_property(
        &mut self,
        node: NodeId,
        property: &Seg,
    ) -> Result<bool, TrackerError> {
        self.assert_node(node)?;
        if self.is_array(node) {
            if matches!(property, Seg::Key(key) if &**key == "length") {
                return Ok(true);
            }
            if let Some(index) = array_index(property) {
                return Ok(index < self.array_length(node));
            }
            return Ok(match property {
                Seg::Key(key) => ARRAY_PROTOTYPE_KEYS.contains(&&**key),
                Seg::Index(_) => false,
            });
        }
        Ok(self.object_has(node, &property.object_key()))
    }

    /// `Object.keys(proxy)`: array indices, or object keys in JS order.
    pub(crate) fn keys(&mut self, node: NodeId) -> Result<Vec<Arc<str>>, TrackerError> {
        self.assert_node(node)?;
        if self.is_array(node) {
            let length = self.array_length(node);
            return Ok((0..length)
                .map(|index| Arc::from(index.to_string()))
                .collect());
        }
        Ok(self.own_keys(node))
    }

    /// `ownKeys` of an object node.
    pub(crate) fn own_keys(&self, node: NodeId) -> Vec<Arc<str>> {
        let entry = &self.nodes[node];
        let base = entry.base.as_object();
        let base_keys = || {
            base.into_iter()
                .flat_map(|object| object.shared_iter().map(|(key, _)| Arc::clone(key)))
        };
        let existing_keys_only = entry.deletes.is_empty()
            && entry.readded.is_empty()
            && entry.writes.keys().all(|key| self.base_has(node, key));
        if existing_keys_only {
            return base_keys().collect();
        }
        let mut keys: Vec<Arc<str>> = base_keys()
            .filter(|key| !entry.deletes.contains_key(key) && !entry.readded.contains_key(key))
            .collect();
        let mut seen: std::collections::HashSet<Arc<str>> = keys.iter().cloned().collect();
        for key in entry.writes.keys() {
            if seen.insert(Arc::clone(key)) {
                keys.push(Arc::clone(key));
            }
        }
        let mut indices: Vec<(u32, Arc<str>)> = Vec::new();
        let mut strings = Vec::new();
        for key in keys {
            match canonical_array_index(&key) {
                Some(index) => indices.push((index, key)),
                None => strings.push(key),
            }
        }
        indices.sort_by_key(|(index, _)| *index);
        indices
            .into_iter()
            .map(|(_, key)| key)
            .chain(strings)
            .collect()
    }

    /// The number a placement coerces to (`Number(value)`).
    fn supplied_number(&mut self, supplied: &Supplied) -> Result<f64, TrackerError> {
        Ok(match supplied {
            Supplied::Value(value) | Supplied::Copied(value) => js_to_number(value),
            Supplied::Node(node) => {
                self.assert_node(*node)?;
                js_to_number(&self.clone_node(*node))
            }
        })
    }

    /// `clonePlacement`.
    pub(crate) fn clone_placement(
        &mut self,
        supplied: Supplied,
    ) -> Result<JsonValue, TrackerError> {
        match supplied {
            Supplied::Value(value) => Ok(copy_json(&value)),
            Supplied::Copied(value) => Ok(value),
            Supplied::Node(node) => {
                self.assert_node(node)?;
                Ok(self.clone_placement_node(node))
            }
        }
    }

    /// `cloneNode`: the node's current content, sharing clean subtrees.
    pub(crate) fn clone_node(&mut self, node: NodeId) -> JsonValue {
        self.clone_with(node, /*placement*/ false)
    }

    /// `clonePlacementNode`: a fresh alias-free copy of the node's content.
    pub(crate) fn clone_placement_node(&mut self, node: NodeId) -> JsonValue {
        self.clone_with(node, /*placement*/ true)
    }

    fn clone_with(&mut self, node: NodeId, placement: bool) -> JsonValue {
        if self.is_array(node) {
            let pieces = self.array(node).pieces().to_vec();
            let mut result = Vec::with_capacity(pieces.iter().map(|piece| piece.length).sum());
            for piece in pieces {
                for offset in 0..piece.length {
                    let source_index = piece.at(offset);
                    let value = self.entry_value_at(node, piece.kind, source_index);
                    result.push(self.clone_slot(
                        Slot::Entry(node, piece.kind, source_index),
                        value,
                        placement,
                    ));
                }
            }
            return JsonValue::Array(Arc::new(result));
        }
        let keys = self.own_keys(node);
        let mut result = JsonObject::with_capacity(keys.len());
        for key in keys {
            let value = self.object_value(node, &key).unwrap_or_default();
            let cloned = self.clone_slot(Slot::Key(node, Arc::clone(&key)), value, placement);
            result.insert(key, cloned);
        }
        JsonValue::Object(Arc::new(result))
    }

    /// `cloneStored` / `clonePlacementStored` of the value at `slot`.
    pub(crate) fn clone_slot(
        &mut self,
        slot: Slot,
        value: JsonValue,
        placement: bool,
    ) -> JsonValue {
        if !value.is_container() {
            return value;
        }
        let child = self.find_node(slot, &value);
        match child {
            Some(child) if placement => self.clone_placement_node(child),
            None if placement => copy_json(&value),
            Some(child) if self.nodes[child].dirty || self.nodes[child].subtree_dirty => {
                self.clone_node(child)
            }
            _ => value,
        }
    }

    /// Store `items` as a new inserted source (`insertPiece`).
    pub(crate) fn insert_piece(&mut self, items: Vec<JsonValue>) -> Vec<Piece> {
        if items.is_empty() {
            return Vec::new();
        }
        let length = items.len();
        let source: SourceId = self.sources.len();
        self.sources.push(items);
        vec![Piece::insert(source, 0, length)]
    }

    /// `replacePieceRange`.
    pub(crate) fn replace_piece_range(
        &mut self,
        node: NodeId,
        index: usize,
        remove: usize,
        inserted: Vec<Piece>,
    ) {
        if remove == 0 && inserted.is_empty() {
            return;
        }
        let length = self.array_length(node);
        if remove == 0 && index == length && inserted.len() == 1 {
            if let (Some(tail), PieceKind::Insert(addition_source)) =
                (self.array(node).tail_piece(), inserted[0].kind)
            {
                if let PieceKind::Insert(tail_source) = tail.kind {
                    if tail.step == 1 && tail.start + tail.length == self.sources[tail_source].len()
                    {
                        let addition = inserted[0];
                        let moved: Vec<JsonValue> = (0..addition.length)
                            .map(|offset| {
                                self.sources[addition_source][addition.start + offset].clone()
                            })
                            .collect();
                        self.sources[tail_source].extend(moved);
                        let overlay = self.array(node);
                        overlay.extend_rightmost(addition.length);
                        overlay.invalidate_caches();
                        overlay.structural = true;
                        overlay.generation += 1;
                        self.mark_dirty(node);
                        return;
                    }
                }
            }
        }
        let overlay = self.array(node);
        let root = overlay.root.take();
        let (left, rest) = overlay.split(root, index);
        let (_, right) = overlay.split(rest, remove);
        let middle = overlay.tree_from_pieces(inserted);
        let joined = overlay.join_normalized(left, middle);
        overlay.root = overlay.join_normalized(joined, right);
        overlay.invalidate_caches();
        overlay.structural = true;
        overlay.generation += 1;
        self.mark_dirty(node);
    }

    /// `setArrayIndex`.
    pub(crate) fn set_array_index(
        &mut self,
        node: NodeId,
        index: usize,
        stored: JsonValue,
    ) -> Result<(), TrackerError> {
        let length = self.array_length(node);
        if index == length {
            let pieces = self.insert_piece(vec![stored]);
            self.replace_piece_range(node, length, 0, pieces);
            return Ok(());
        }
        let (piece, offset) = self.locate(node, index)?;
        let source_index = piece.at(offset);
        let current = self.entry_value_at(node, piece.kind, source_index);
        if !stored.is_container() && current.strict_equals(&stored) {
            return Ok(());
        }
        match piece.kind {
            PieceKind::Base => {
                let original = self.nodes[node]
                    .base
                    .get_index(source_index)
                    .cloned()
                    .unwrap_or_default();
                let overlay = self.array(node);
                if !stored.is_container() && stored.strict_equals(&original) {
                    overlay.base_overrides.remove(&source_index);
                } else {
                    overlay.base_overrides.insert(source_index, stored);
                }
            }
            PieceKind::Insert(source) => {
                let original = self.sources[source]
                    .get(source_index)
                    .cloned()
                    .unwrap_or_default();
                let overlay = self.array(node);
                if !stored.is_container() && stored.strict_equals(&original) {
                    if let Some(overrides) = overlay.insert_overrides.get_mut(&source) {
                        overrides.remove(&source_index);
                        if overrides.is_empty() {
                            overlay.insert_overrides.remove(&source);
                        }
                    }
                } else {
                    if !overlay.insert_overrides.contains_key(&source) {
                        overlay
                            .insert_overrides
                            .insert(source, OrderedMap::default());
                    }
                    if let Some(overrides) = overlay.insert_overrides.get_mut(&source) {
                        overrides.insert(source_index, stored);
                    }
                }
            }
        }
        self.mark_dirty(node);
        Ok(())
    }

    /// `setArrayLength`: shrink, or grow with `null`s.
    pub(crate) fn set_array_length(&mut self, node: NodeId, next: usize) {
        let current = self.array_length(node);
        if next == current {
            return;
        }
        if next < current {
            self.replace_piece_range(node, next, current - next, Vec::new());
        } else {
            let pieces = self.insert_piece(vec![JsonValue::Null; next - current]);
            self.replace_piece_range(node, current, 0, pieces);
        }
    }

    /// The current string form of an item (`String(value)` for sorting).
    pub(crate) fn item_string(&mut self, item: &Item) -> String {
        match item {
            Item::Value(value) => js_string(value),
            Item::Node(node) => js_string(&self.clone_node(*node)),
        }
    }
}

#[allow(clippy::cast_precision_loss)] // array lengths stay below 2^32
pub(crate) fn length_json(length: usize) -> JsonValue {
    JsonValue::Number(JsonNumber::new(length as f64).unwrap_or_default())
}

/// `toArrayLength`.
pub(crate) fn to_array_length(number: f64) -> Result<usize, TrackerError> {
    if number.is_nan() || number.fract() != 0.0 || number < 0.0 || number >= 4_294_967_296.0 {
        return Err(TrackerError::InvalidArrayLength);
    }
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    // checked integral in [0, 2^32)
    Ok(number as usize)
}

/// JS `Number(value)` for a JSON value.
pub(crate) fn js_to_number(value: &JsonValue) -> f64 {
    match value {
        JsonValue::Null => 0.0,
        JsonValue::Bool(flag) => f64::from(u8::from(*flag)),
        JsonValue::Number(number) => number.get(),
        JsonValue::String(text) => string_to_number(text),
        JsonValue::Array(_) => string_to_number(&js_string(value)),
        JsonValue::Object(_) => f64::NAN,
    }
}

fn is_js_whitespace(character: char) -> bool {
    matches!(
        character,
        '\u{9}' | '\u{a}' | '\u{b}' | '\u{c}' | '\u{d}' | ' ' | '\u{a0}' | '\u{1680}' | '\u{2000}'
            ..='\u{200a}'
                | '\u{2028}'
                | '\u{2029}'
                | '\u{202f}'
                | '\u{205f}'
                | '\u{3000}'
                | '\u{feff}'
    )
}

/// ECMA-262 `StringToNumber`.
fn string_to_number(text: &str) -> f64 {
    let trimmed = text.trim_matches(is_js_whitespace);
    if trimmed.is_empty() {
        return 0.0;
    }
    for (prefix, radix) in [
        ("0x", 16),
        ("0X", 16),
        ("0o", 8),
        ("0O", 8),
        ("0b", 2),
        ("0B", 2),
    ] {
        if let Some(digits) = trimmed.strip_prefix(prefix) {
            if digits.is_empty() || !digits.chars().all(|digit| digit.is_digit(radix)) {
                return f64::NAN;
            }
            return digits
                .chars()
                .filter_map(|digit| digit.to_digit(radix))
                .fold(0.0, |total, digit| {
                    total * f64::from(radix) + f64::from(digit)
                });
        }
    }
    let unsigned = trimmed.strip_prefix(['+', '-']).unwrap_or(trimmed);
    if unsigned == "Infinity" {
        return if trimmed.starts_with('-') {
            f64::NEG_INFINITY
        } else {
            f64::INFINITY
        };
    }
    if !is_decimal_literal(unsigned) {
        return f64::NAN;
    }
    trimmed.parse().unwrap_or(f64::NAN)
}

/// `StrUnsignedDecimalLiteral` without `Infinity`.
fn is_decimal_literal(text: &str) -> bool {
    let (mantissa, exponent) = match text.find(['e', 'E']) {
        Some(at) => (&text[..at], Some(&text[at + 1..])),
        None => (text, None),
    };
    let (whole, fraction) = mantissa.split_once('.').unwrap_or((mantissa, ""));
    let digits = |part: &str| part.chars().all(|digit| digit.is_ascii_digit());
    if !digits(whole) || !digits(fraction) || (whole.is_empty() && fraction.is_empty()) {
        return false;
    }
    match exponent {
        None => true,
        Some(exponent) => {
            let exponent = exponent.strip_prefix(['+', '-']).unwrap_or(exponent);
            !exponent.is_empty() && digits(exponent)
        }
    }
}
