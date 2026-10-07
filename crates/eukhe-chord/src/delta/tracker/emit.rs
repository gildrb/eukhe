//! Operation emission for a prepared overlay (`emitOperations` and helpers of
//! `tracker.ts`): object writes and deletes, string append/front-truncate,
//! array splices and permutations, dense-region folds, reserved-key folds, and
//! the root-replacement fallback.

use std::collections::HashSet;
use std::sync::Arc;

use super::ordered::OrderedMap;
use super::overlay::{ContextState, NodeId, Slot};
use super::pieces::{build_plan, PieceKind};
use crate::delta::ops::{is_reserved_segment, Op, Path, Seg};
use crate::delta::overlap::overlap;
use crate::json::{utf16_len, utf16_skip, JsonValue};

const MAX_DELTA_OPERATIONS: usize = 4_096;
const MAX_SIMPLE_OBJECT_NODES: usize = 128;
const OVERLAP_SCAN: usize = 65_536;

/// Dirty base-array indices; switches to a bitmap at 256 entries.
struct DenseCandidates {
    indices: Vec<usize>,
    bits: Option<Vec<bool>>,
    length: usize,
}

impl DenseCandidates {
    fn new(length: usize) -> Self {
        Self {
            indices: Vec::new(),
            bits: None,
            length,
        }
    }

    fn add(&mut self, index: usize) {
        if let Some(bits) = self.bits.as_mut() {
            bits[index] = true;
            return;
        }
        self.indices.push(index);
        if self.indices.len() < 256 {
            return;
        }
        let mut bits = vec![false; self.length];
        for existing in self.indices.drain(..) {
            bits[existing] = true;
        }
        self.bits = Some(bits);
    }

    /// Runs with at least 256 dirty entries covering half their span, allowing
    /// single-entry gaps (`buildDenseRegions`).
    fn regions(&self) -> Vec<(usize, usize)> {
        let Some(bits) = self.bits.as_ref() else {
            return Vec::new();
        };
        let mut regions = Vec::new();
        let mut at = 0;
        while at < bits.len() {
            while at < bits.len() && !bits[at] {
                at += 1;
            }
            if at == bits.len() {
                break;
            }
            let start = at;
            let mut end = at;
            let mut count = 0;
            let mut gap = 0;
            while at < bits.len() {
                if bits[at] {
                    count += 1;
                    end = at;
                    gap = 0;
                } else {
                    gap += 1;
                    if gap > 1 {
                        break;
                    }
                }
                at += 1;
            }
            let length = end - start + 1;
            if count >= 256 && count * 2 >= length {
                regions.push((start, length));
            }
        }
        regions
    }
}

fn region_containing(regions: &[(usize, usize)], index: usize) -> bool {
    regions
        .iter()
        .any(|(start, length)| index >= *start && index < start + length)
}

fn has_reserved_segment(path: &[Seg]) -> bool {
    reserved_position(path).is_some()
}

fn reserved_position(path: &[Seg]) -> Option<usize> {
    path.iter()
        .position(|segment| matches!(segment, Seg::Key(key) if is_reserved_segment(key)))
}

fn extend(path: &[Seg], segment: Seg) -> Path {
    let mut next = Vec::with_capacity(path.len() + 1);
    next.extend_from_slice(path);
    next.push(segment);
    next
}

fn emit_set(operations: &mut Vec<Op>, path: Path, value: JsonValue) {
    if path.is_empty() {
        operations.push(Op::Replace(value));
    } else {
        operations.push(Op::Set(path, value));
    }
}

/// Emit the narrowest op for a changed leaf; `false` when nothing changed
/// (`emitChangedValue`).
fn emit_changed_value(
    operations: &mut Vec<Op>,
    path: Path,
    before: Option<&JsonValue>,
    after: JsonValue,
) -> bool {
    if !after.is_container() && before.is_some_and(|before| before.strict_equals(&after)) {
        return false;
    }
    if let Some(before) = before {
        if before.is_container() && after.is_container() && *before == after {
            return false;
        }
        if let (Some(old), Some(new)) = (before.as_str(), after.as_str()) {
            if new.len() > old.len() && new.starts_with(old) {
                operations.push(Op::Append(path, new[old.len()..].to_owned()));
                return true;
            }
            let shared = overlap(old, new, OVERLAP_SCAN);
            if shared > 0 {
                operations.push(Op::Truncate(path.clone(), utf16_len(old) - shared));
                if utf16_len(new) > shared {
                    operations.push(Op::Append(path, utf16_skip(new, shared).to_owned()));
                }
                return true;
            }
        }
    }
    operations.push(Op::Set(path, after));
    true
}

impl ContextState {
    /// `emitOperations`.
    #[allow(clippy::too_many_lines)] // one TS function; splitting it would obscure the pass order
    pub(crate) fn emit_operations(&mut self) -> Vec<Op> {
        if let Some(simple) = self.emit_simple_object_operations() {
            return simple;
        }
        let mut operations = Vec::new();
        let mut forced_folds: OrderedMap<NodeId, Path> = OrderedMap::default();
        let mut emission_paths: OrderedMap<NodeId, Path> = OrderedMap::default();
        let mut dense_indices: OrderedMap<NodeId, DenseCandidates> = OrderedMap::default();
        let dirty = self.dirty.clone();
        for &node in &dirty {
            if let Some((array, index)) = self.locate_dense_array_position(node) {
                let length = self.base_length(array);
                if !dense_indices.contains_key(&array) {
                    dense_indices.insert(array, DenseCandidates::new(length));
                }
                if let Some(candidates) = dense_indices.get_mut(&array) {
                    candidates.add(index);
                }
            }
            if self.is_array(node) {
                let length = self.base_length(node);
                let overlay = self.array(node);
                if !overlay.structural && !overlay.base_overrides.is_empty() {
                    let indices: Vec<usize> = overlay.base_overrides.keys().copied().collect();
                    if !dense_indices.contains_key(&node) {
                        dense_indices.insert(node, DenseCandidates::new(length));
                    }
                    if let Some(candidates) = dense_indices.get_mut(&node) {
                        for index in indices {
                            candidates.add(index);
                        }
                    }
                }
            }
        }
        let mut dense_regions: OrderedMap<NodeId, Vec<(usize, usize)>> = OrderedMap::default();
        for (array, candidates) in dense_indices.iter() {
            let Some(path) = self.resolve_path(*array) else {
                continue;
            };
            if has_reserved_segment(&path) {
                continue;
            }
            let regions = candidates.regions();
            if !regions.is_empty() {
                dense_regions.insert(*array, regions);
            }
        }
        for &node in &dirty {
            let Some(path) = self.resolve_path(node) else {
                continue;
            };
            if self.has_covering_dense_region(node, &path, &dense_regions) {
                continue;
            }
            emission_paths.insert(node, path.clone());
            if !self.is_array(node) && self.has_reserved_mutation(node) {
                forced_folds.insert(node, path.clone());
            }
            if let Some(reserved_at) = reserved_position(&path) {
                let mut ancestor = node;
                for _ in reserved_at..path.len() {
                    if let Some(parent) = self.parent(ancestor) {
                        ancestor = parent;
                    }
                }
                forced_folds.insert(ancestor, path[..reserved_at].to_vec());
            }
        }
        for (node, path) in forced_folds.iter() {
            emission_paths.insert(*node, path.clone());
        }
        let dense_nodes: Vec<NodeId> = dense_regions.keys().copied().collect();
        for node in dense_nodes {
            if let Some(path) = self.resolve_path(node) {
                if !self.has_covering_dense_region(node, &path, &dense_regions) {
                    emission_paths.insert(node, path);
                }
            }
        }
        let max_depth = emission_paths
            .iter()
            .map(|(_, path)| path.len())
            .max()
            .unwrap_or(0);
        let mut buckets: Vec<Vec<NodeId>> = vec![Vec::new(); max_depth + 1];
        for (node, path) in emission_paths.iter() {
            buckets[path.len()].push(*node);
        }
        let mut folded: HashSet<NodeId> = HashSet::new();
        for bucket in buckets {
            for node in bucket {
                let Some(path) = emission_paths.get(&node).cloned() else {
                    continue;
                };
                if self.has_placement_ancestor(node) || self.has_folded_ancestor(node, &folded) {
                    continue;
                }
                if forced_folds.contains_key(&node) {
                    let value = self.clone_node(node);
                    emit_set(&mut operations, path, value);
                    folded.insert(node);
                    continue;
                }
                if self.is_array(node) {
                    let regions = dense_regions.get(&node).cloned();
                    self.emit_array_operations(node, &path, &mut operations, regions.as_deref());
                } else {
                    self.emit_object_operations(node, &path, &mut operations);
                }
                if operations.len() > MAX_DELTA_OPERATIONS {
                    return vec![Op::Replace(self.clone_root())];
                }
            }
        }
        operations
    }

    fn clone_root(&mut self) -> JsonValue {
        match self.root {
            Some(root) => self.clone_node(root),
            None => JsonValue::Null,
        }
    }

    fn base_length(&self, node: NodeId) -> usize {
        self.nodes[node]
            .base
            .as_array()
            .map_or(0, <[JsonValue]>::len)
    }

    /// `emitSimpleObjectOperations`: the fast path for dirty objects outside
    /// arrays.
    fn emit_simple_object_operations(&mut self) -> Option<Vec<Op>> {
        let mut nodes: Vec<(NodeId, Path)> = Vec::new();
        let dirty = self.dirty.clone();
        for node in dirty {
            if self.is_array(node)
                || self.has_reserved_mutation(node)
                || self.has_placement_ancestor(node)
            {
                return None;
            }
            let mut parent = self.parent(node);
            while let Some(current) = parent {
                if self.is_array(current) {
                    return None;
                }
                parent = self.parent(current);
            }
            let Some(path) = self.resolve_path(node) else {
                continue;
            };
            if has_reserved_segment(&path) {
                return None;
            }
            nodes.push((node, path));
            if nodes.len() > MAX_SIMPLE_OBJECT_NODES {
                return None;
            }
        }
        // Stable by depth.
        nodes.sort_by_key(|(_, path)| path.len());
        let mut operations = Vec::new();
        let mut can_materialize_directly = true;
        for (node, path) in nodes {
            if self.emit_object_operations(node, &path, &mut operations) {
                can_materialize_directly = false;
            }
            if operations.len() > MAX_DELTA_OPERATIONS {
                return Some(vec![Op::Replace(self.clone_root())]);
            }
        }
        self.simple_object_materialization = can_materialize_directly;
        Some(operations)
    }

    /// The base array and index a dirty node sits in, when every array on its
    /// way is unstructured and still holds it (`locateDenseArrayPosition`).
    fn locate_dense_array_position(&mut self, node: NodeId) -> Option<(NodeId, usize)> {
        let mut child = node;
        while let Some(parent) = self.parent(child) {
            if self.is_array(parent) {
                let Slot::Entry(_, PieceKind::Base, source_index) = self.nodes[child].slot else {
                    return None;
                };
                if self.array(parent).structural {
                    return None;
                }
                let current = match self.array(parent).base_overrides.get(&source_index) {
                    Some(value) => value.clone(),
                    None => self.nodes[parent]
                        .base
                        .get_index(source_index)
                        .cloned()
                        .unwrap_or_default(),
                };
                if !current.strict_equals(&self.nodes[child].base) {
                    return None;
                }
                return Some((parent, source_index));
            }
            child = parent;
        }
        None
    }

    fn has_covering_dense_region(
        &mut self,
        node: NodeId,
        path: &[Seg],
        regions: &OrderedMap<NodeId, Vec<(usize, usize)>>,
    ) -> bool {
        let mut parent = self.parent(node);
        while let Some(current) = parent {
            parent = self.parent(current);
            let Some(current_regions) = regions.get(&current) else {
                continue;
            };
            let Some(parent_path) = self.resolve_path(current) else {
                continue;
            };
            if path.len() <= parent_path.len() || path[..parent_path.len()] != parent_path[..] {
                continue;
            }
            if let Seg::Index(index) = path[parent_path.len()] {
                if region_containing(current_regions, index) {
                    return true;
                }
            }
        }
        false
    }

    fn has_reserved_mutation(&self, node: NodeId) -> bool {
        let entry = &self.nodes[node];
        entry.writes.keys().any(|key| is_reserved_segment(key))
            || entry.deletes.keys().any(|key| is_reserved_segment(key))
    }

    fn has_folded_ancestor(&self, node: NodeId, folded: &HashSet<NodeId>) -> bool {
        let mut parent = self.parent(node);
        while let Some(current) = parent {
            if folded.contains(&current) {
                return true;
            }
            parent = self.parent(current);
        }
        false
    }

    /// Whether the node lies inside a value placed during this change, whose
    /// payload already carries its edits.
    fn has_placement_ancestor(&self, node: NodeId) -> bool {
        let mut current = Some(node);
        while let Some(id) = current {
            let parent = self.parent(id);
            if parent.is_some() && self.nodes[id].parent_placement {
                return true;
            }
            current = parent;
        }
        false
    }

    fn emit_object_write(
        &mut self,
        node: NodeId,
        path: &[Seg],
        operations: &mut Vec<Op>,
        key: &Arc<str>,
    ) -> bool {
        let next_path = extend(path, Seg::Key(Arc::clone(key)));
        let before = if self.nodes[node].readded.contains_key(key) {
            None
        } else {
            self.nodes[node].base.get(key).cloned()
        };
        let value = self.object_value(node, key).unwrap_or_default();
        let after = self.clone_slot(
            Slot::Key(node, Arc::clone(key)),
            value,
            /*placement*/ false,
        );
        let both_containers =
            before.as_ref().is_some_and(JsonValue::is_container) && after.is_container();
        let emitted = emit_changed_value(operations, next_path, before.as_ref(), after);
        both_containers && !emitted
    }

    /// `emitObjectOperations`; returns whether a container write normalized
    /// away (the candidate must then be materialized from the ops).
    fn emit_object_operations(
        &mut self,
        node: NodeId,
        path: &[Seg],
        operations: &mut Vec<Op>,
    ) -> bool {
        // Delete-and-readd is explicit so replicas reproduce the key order.
        let readded: Vec<Arc<str>> = self.nodes[node].readded.keys().cloned().collect();
        for key in readded {
            if self.nodes[node].base.get(&key).is_some() {
                operations.push(Op::Delete(extend(path, Seg::Key(key))));
            }
        }
        let mut normalized_container_write = false;
        let writes: Vec<Arc<str>> = self.nodes[node].writes.keys().cloned().collect();
        for key in writes {
            if operations.len() > MAX_DELTA_OPERATIONS {
                return normalized_container_write;
            }
            if self.emit_object_write(node, path, operations, &key) {
                normalized_container_write = true;
            }
        }
        let deletes: Vec<Arc<str>> = self.nodes[node].deletes.keys().cloned().collect();
        for key in deletes {
            if operations.len() > MAX_DELTA_OPERATIONS {
                return normalized_container_write;
            }
            if self.nodes[node].base.get(&key).is_some() {
                operations.push(Op::Delete(extend(path, Seg::Key(key))));
            }
        }
        normalized_container_write
    }

    fn emit_array_operations(
        &mut self,
        node: NodeId,
        path: &[Seg],
        operations: &mut Vec<Op>,
        dense_regions: Option<&[(usize, usize)]>,
    ) {
        if let Some(regions) = dense_regions {
            for &(start, length) in regions {
                if operations.len() > MAX_DELTA_OPERATIONS {
                    return;
                }
                let items = self.clone_array_region(node, start, length);
                operations.push(Op::Splice(path.to_vec(), start, length, items));
            }
        }
        if self.array(node).structural {
            let base_length = self.base_length(node);
            let overlay = self.array(node);
            let plan = if let Some(plan) = overlay.plan.clone() {
                plan
            } else {
                let plan = build_plan(overlay.pieces(), base_length);
                overlay.plan = Some(plan.clone());
                plan
            };
            for &(start, length) in &plan.remove_runs {
                if operations.len() > MAX_DELTA_OPERATIONS {
                    return;
                }
                operations.push(Op::Splice(path.to_vec(), start, length, Vec::new()));
            }
            if let Some(permutation) = plan.permutation {
                operations.push(Op::Move(path.to_vec(), permutation));
            }
            let pieces = self.array(node).pieces().to_vec();
            for &(logical_index, first, end) in &plan.insert_runs {
                if operations.len() > MAX_DELTA_OPERATIONS {
                    return;
                }
                let mut items = Vec::new();
                for piece in &pieces[first..end] {
                    for offset in 0..piece.length {
                        let source_index = piece.at(offset);
                        let value = self.entry_value_at(node, piece.kind, source_index);
                        items.push(self.clone_slot(
                            Slot::Entry(node, piece.kind, source_index),
                            value,
                            false,
                        ));
                    }
                }
                operations.push(Op::Splice(path.to_vec(), logical_index, 0, items));
            }
        }
        let overrides: Vec<(usize, JsonValue)> = self
            .array(node)
            .base_overrides
            .iter()
            .map(|(index, value)| (*index, value.clone()))
            .collect();
        for (base_index, value) in overrides {
            if operations.len() > MAX_DELTA_OPERATIONS {
                return;
            }
            let Some(index) = self
                .array(node)
                .find_entry_index(PieceKind::Base, base_index)
            else {
                continue;
            };
            if dense_regions.is_some_and(|regions| region_containing(regions, index)) {
                continue;
            }
            let before = self.nodes[node].base.get_index(base_index).cloned();
            let after =
                self.clone_slot(Slot::Entry(node, PieceKind::Base, base_index), value, false);
            emit_changed_value(
                operations,
                extend(path, Seg::Index(index)),
                before.as_ref(),
                after,
            );
        }
    }

    fn clone_array_region(&mut self, node: NodeId, start: usize, length: usize) -> Vec<JsonValue> {
        let mut result = Vec::with_capacity(length);
        for index in start..start + length {
            let Some((piece, offset)) = self.array(node).locate(index) else {
                continue;
            };
            let source_index = piece.at(offset);
            let value = self.entry_value_at(node, piece.kind, source_index);
            result.push(self.clone_slot(Slot::Entry(node, piece.kind, source_index), value, false));
        }
        result
    }

    /// The node's path in the candidate, or `None` when it was detached
    /// (`resolvePath`; cached per prepare).
    pub(crate) fn resolve_path(&mut self, node: NodeId) -> Option<Path> {
        if let Some(path) = &self.nodes[node].prepared_path {
            return Some(path.clone());
        }
        let slot = self.nodes[node].slot.clone();
        let path = match slot {
            Slot::Root => Vec::new(),
            Slot::Key(parent, key) => {
                let parent_path = self.resolve_path(parent)?;
                if !self.object_has(parent, &key) {
                    return None;
                }
                let current = self.object_value(parent, &key)?;
                if !current.strict_equals(&self.nodes[node].base) {
                    return None;
                }
                extend(&parent_path, Seg::Key(key))
            }
            Slot::Entry(parent, kind, source_index) => {
                let parent_path = self.resolve_path(parent)?;
                let index = self.array(parent).find_entry_index(kind, source_index)?;
                let (piece, _) = self.array(parent).locate(index)?;
                let current = self.entry_value_at(parent, piece.kind, source_index);
                if !current.strict_equals(&self.nodes[node].base) {
                    return None;
                }
                extend(&parent_path, Seg::Index(index))
            }
        };
        self.nodes[node].prepared_path = Some(path.clone());
        Some(path)
    }
}
