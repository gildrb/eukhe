//! Array mutators of the overlay (`arrayMutators` of `tracker.ts`).

use std::collections::{HashMap, HashSet};

use super::ordered::OrderedMap;
use super::overlay::{ContextState, Item, NodeId, Slot, Supplied};
use super::pieces::{append_merged, Piece, PieceKind, SourceId};
use super::TrackerError;
use crate::json::JsonValue;

/// `clampIndex(ToIntegerOrInfinity(value), length)`.
pub(crate) fn clamp_index(value: i64, length: usize) -> usize {
    let length = i128::try_from(length).unwrap_or(i128::MAX);
    let value = i128::from(value);
    let clamped = if value < 0 {
        (length + value).max(0)
    } else {
        value.min(length)
    };
    usize::try_from(clamped).unwrap_or(0)
}

/// A sort token: a base source index, or `-(k + 1)` for the k-th inserted
/// entry.
pub(crate) type SortToken = i64;

/// The sort state captured before the comparator runs.
pub(crate) struct SortPlan {
    pub(crate) order: Vec<SortToken>,
    inserted_sources: Vec<SourceId>,
    inserted_indices: Vec<usize>,
    pub(crate) base_values: HashMap<usize, Item>,
    pub(crate) inserted_values: Vec<Item>,
    base_snapshot: HashMap<usize, JsonValue>,
    insert_snapshots: HashMap<SourceId, HashMap<usize, JsonValue>>,
    generation: u64,
}

impl SortPlan {
    /// The value a token compares as.
    pub(crate) fn value(&self, token: SortToken) -> Option<&Item> {
        if let Ok(index) = usize::try_from(token) {
            self.base_values.get(&index)
        } else {
            self.inserted_values.get(token_slot(token))
        }
    }

    fn token_entry(&self, token: SortToken) -> (PieceKind, usize) {
        if let Ok(index) = usize::try_from(token) {
            (PieceKind::Base, index)
        } else {
            let slot = token_slot(token);
            (
                PieceKind::Insert(self.inserted_sources[slot]),
                self.inserted_indices[slot],
            )
        }
    }
}

fn token_slot(token: SortToken) -> usize {
    usize::try_from(-token - 1).unwrap_or(0)
}

impl ContextState {
    /// Array mutators require a writable array node (`mutatorNode`).
    pub(crate) fn mutator_node(&self, node: NodeId) -> Result<(), TrackerError> {
        self.assert_node(node)?;
        if !self.is_array(node) {
            return Err(TrackerError::IncompatibleReceiver);
        }
        self.assert_writable()
    }

    /// Copy placements into a new inserted source; nothing changes on error
    /// (`insertPlacementPiece`).
    fn insert_placement_piece(&mut self, items: Vec<Supplied>) -> Result<Vec<Piece>, TrackerError> {
        let mut stored = Vec::with_capacity(items.len());
        for item in items {
            stored.push(self.clone_placement(item)?);
        }
        Ok(self.insert_piece(stored))
    }

    /// The item a held entry reads as (`publicSortValue` / `getArrayIndex`).
    fn entry_item(&mut self, node: NodeId, kind: PieceKind, source_index: usize) -> Item {
        let value = self.entry_value_at(node, kind, source_index);
        if !value.is_container() {
            return Item::Value(value);
        }
        let placement =
            kind != PieceKind::Base || self.has_entry_override_at(node, kind, source_index);
        Item::Node(self.create_node(value, Slot::Entry(node, kind, source_index), placement))
    }

    pub(crate) fn push(
        &mut self,
        node: NodeId,
        items: Vec<Supplied>,
    ) -> Result<usize, TrackerError> {
        self.mutator_node(node)?;
        let length = self.array_length(node);
        let count = items.len();
        let pieces = self.insert_placement_piece(items)?;
        self.replace_piece_range(node, length, 0, pieces);
        Ok(length + count)
    }

    pub(crate) fn pop(&mut self, node: NodeId) -> Result<Option<Item>, TrackerError> {
        self.mutator_node(node)?;
        let length = self.array_length(node);
        if length == 0 {
            return Ok(None);
        }
        let value = self.get_array_index(node, length - 1)?;
        self.replace_piece_range(node, length - 1, 1, Vec::new());
        Ok(value)
    }

    pub(crate) fn shift(&mut self, node: NodeId) -> Result<Option<Item>, TrackerError> {
        self.mutator_node(node)?;
        if self.array_length(node) == 0 {
            return Ok(None);
        }
        let value = self.get_array_index(node, 0)?;
        self.replace_piece_range(node, 0, 1, Vec::new());
        Ok(value)
    }

    pub(crate) fn unshift(
        &mut self,
        node: NodeId,
        items: Vec<Supplied>,
    ) -> Result<usize, TrackerError> {
        self.mutator_node(node)?;
        let pieces = self.insert_placement_piece(items)?;
        self.replace_piece_range(node, 0, 0, pieces);
        Ok(self.array_length(node))
    }

    pub(crate) fn splice(
        &mut self,
        node: NodeId,
        start: i64,
        delete_count: i64,
        items: Vec<Supplied>,
    ) -> Result<Vec<Item>, TrackerError> {
        self.mutator_node(node)?;
        let length = self.array_length(node);
        let start = clamp_index(start, length);
        let remove = usize::try_from(delete_count.max(0))
            .unwrap_or(usize::MAX)
            .min(length - start);
        let mut removed = Vec::with_capacity(remove);
        for offset in 0..remove {
            if let Some(item) = self.get_array_index(node, start + offset)? {
                removed.push(item);
            }
        }
        let count = items.len();
        let pieces = self.insert_placement_piece(items)?;
        self.replace_piece_range(node, start, remove, pieces);
        self.set_array_length(node, length - remove + count);
        Ok(removed)
    }

    pub(crate) fn reverse(&mut self, node: NodeId) -> Result<(), TrackerError> {
        self.mutator_node(node)?;
        if self.array_length(node) < 2 {
            return Ok(());
        }
        let overlay = self.array(node);
        let mut pieces = overlay.pieces().to_vec();
        pieces.reverse();
        for piece in &mut pieces {
            piece.start = piece.at(piece.length - 1);
            piece.step = -piece.step;
        }
        overlay.replace_all_pieces(pieces);
        overlay.structural = true;
        overlay.generation += 1;
        overlay.plan = None;
        self.mark_dirty(node);
        Ok(())
    }

    pub(crate) fn fill(
        &mut self,
        node: NodeId,
        supplied: &Supplied,
        start: i64,
        end: i64,
    ) -> Result<(), TrackerError> {
        self.mutator_node(node)?;
        let length = self.array_length(node);
        let start = clamp_index(start, length);
        let end = clamp_index(end, length);
        if end <= start {
            return Ok(());
        }
        let mut items = Vec::with_capacity(end - start);
        for _ in start..end {
            // Every item is an independent copy.
            let item = match supplied {
                Supplied::Value(value) | Supplied::Copied(value) => Supplied::Value(value.clone()),
                Supplied::Node(child) => Supplied::Node(*child),
            };
            items.push(self.clone_placement(item)?);
        }
        let pieces = self.insert_piece(items);
        self.replace_piece_range(node, start, end - start, pieces);
        Ok(())
    }

    pub(crate) fn copy_within(
        &mut self,
        node: NodeId,
        target: i64,
        start: i64,
        end: i64,
    ) -> Result<(), TrackerError> {
        self.mutator_node(node)?;
        let length = self.array_length(node);
        let target = clamp_index(target, length);
        let start = clamp_index(start, length);
        let end = clamp_index(end, length);
        let count = end.saturating_sub(start).min(length - target);
        let mut values = Vec::with_capacity(count);
        for offset in 0..count {
            let supplied = match self.get_array_index(node, start + offset)? {
                Some(Item::Node(child)) => Supplied::Node(child),
                Some(Item::Value(value)) => Supplied::Value(value),
                None => Supplied::Value(JsonValue::Null),
            };
            values.push(self.clone_placement(supplied)?);
        }
        let pieces = self.insert_piece(values);
        self.replace_piece_range(node, target, count, pieces);
        Ok(())
    }

    /// Capture the order and values `sort` compares.
    pub(crate) fn sort_prepare(&mut self, node: NodeId) -> Result<SortPlan, TrackerError> {
        self.mutator_node(node)?;
        let pieces = self.array(node).pieces().to_vec();
        let mut plan = SortPlan {
            order: Vec::new(),
            inserted_sources: Vec::new(),
            inserted_indices: Vec::new(),
            base_values: HashMap::new(),
            inserted_values: Vec::new(),
            base_snapshot: HashMap::new(),
            insert_snapshots: HashMap::new(),
            generation: 0,
        };
        for piece in pieces {
            for offset in 0..piece.length {
                let source_index = piece.at(offset);
                match piece.kind {
                    PieceKind::Base => {
                        plan.order
                            .push(i64::try_from(source_index).unwrap_or(i64::MAX));
                        let item = self.entry_item(node, piece.kind, source_index);
                        plan.base_values.insert(source_index, item);
                    }
                    PieceKind::Insert(source) => {
                        plan.inserted_sources.push(source);
                        plan.inserted_indices.push(source_index);
                        plan.order
                            .push(-i64::try_from(plan.inserted_sources.len()).unwrap_or(i64::MAX));
                        let item = self.entry_item(node, piece.kind, source_index);
                        plan.inserted_values.push(item);
                    }
                }
            }
        }
        let overlay = self.array(node);
        for (index, value) in overlay.base_overrides.iter() {
            plan.base_snapshot.insert(*index, value.clone());
        }
        for (source, overrides) in overlay.insert_overrides.iter() {
            let snapshot = overrides
                .iter()
                .map(|(index, value)| (*index, value.clone()))
                .collect();
            plan.insert_snapshots.insert(*source, snapshot);
        }
        plan.generation = overlay.generation;
        Ok(plan)
    }

    /// Apply a sorted token order captured by [`Self::sort_prepare`].
    pub(crate) fn sort_finish(
        &mut self,
        node: NodeId,
        plan: &SortPlan,
    ) -> Result<(), TrackerError> {
        self.assert_node(node)?;
        let overlay = self.array(node);
        if !plan.base_snapshot.is_empty()
            || !plan.insert_snapshots.is_empty()
            || !overlay.base_overrides.is_empty()
            || !overlay.insert_overrides.is_empty()
        {
            for &token in &plan.order {
                self.restore_sort_override(node, plan, token);
            }
        }
        let comparator_was_structural = self.array(node).generation != plan.generation;
        let current_length = self.array_length(node);
        let mut same_prefix = current_length >= plan.order.len();
        if same_prefix {
            for (index, &token) in plan.order.iter().enumerate() {
                let (piece, offset) = self.locate(node, index)?;
                let (kind, source_index) = plan.token_entry(token);
                if piece.at(offset) != source_index || piece.kind != kind {
                    same_prefix = false;
                    break;
                }
            }
        }
        if !same_prefix {
            let pieces = pieces_from_sort_order(plan);
            self.replace_piece_range(node, 0, plan.order.len().min(current_length), pieces);
        }
        if comparator_was_structural {
            self.deduplicate_array_entries(node);
        }
        Ok(())
    }

    fn restore_sort_override(&mut self, node: NodeId, plan: &SortPlan, token: SortToken) {
        let (kind, source_index) = plan.token_entry(token);
        let overlay = self.array(node);
        match kind {
            PieceKind::Base => match plan.base_snapshot.get(&source_index) {
                Some(snapshot) => overlay
                    .base_overrides
                    .insert(source_index, snapshot.clone()),
                None => {
                    overlay.base_overrides.remove(&source_index);
                }
            },
            PieceKind::Insert(source) => {
                match plan
                    .insert_snapshots
                    .get(&source)
                    .and_then(|snapshot| snapshot.get(&source_index))
                {
                    Some(snapshot) => {
                        if !overlay.insert_overrides.contains_key(&source) {
                            overlay
                                .insert_overrides
                                .insert(source, OrderedMap::default());
                        }
                        if let Some(overrides) = overlay.insert_overrides.get_mut(&source) {
                            overrides.insert(source_index, snapshot.clone());
                        }
                    }
                    None => {
                        if let Some(overrides) = overlay.insert_overrides.get_mut(&source) {
                            overrides.remove(&source_index);
                            if overrides.is_empty() {
                                overlay.insert_overrides.remove(&source);
                            }
                        }
                    }
                }
            }
        }
    }

    /// Replace entries a reentrant comparator duplicated with copies
    /// (`deduplicateArrayEntries`).
    fn deduplicate_array_entries(&mut self, node: NodeId) {
        let pieces = self.array(node).pieces().to_vec();
        let mut seen: HashSet<(PieceKind, usize)> = HashSet::new();
        let mut next: Vec<Piece> = Vec::new();
        let mut duplicated = false;
        for piece in pieces {
            for offset in 0..piece.length {
                let source_index = piece.at(offset);
                if seen.insert((piece.kind, source_index)) {
                    append_merged(
                        &mut next,
                        Piece {
                            kind: piece.kind,
                            start: source_index,
                            length: 1,
                            step: 1,
                        },
                    );
                } else {
                    duplicated = true;
                    let value = self.entry_value_at(node, piece.kind, source_index);
                    let copy = self.clone_slot(
                        Slot::Entry(node, piece.kind, source_index),
                        value,
                        /*placement*/ true,
                    );
                    let inserted = self.insert_piece(vec![copy]);
                    if let Some(piece) = inserted.into_iter().next() {
                        append_merged(&mut next, piece);
                    }
                }
            }
        }
        if !duplicated {
            return;
        }
        let overlay = self.array(node);
        overlay.replace_all_pieces(next);
        overlay.structural = true;
        overlay.generation += 1;
        overlay.plan = None;
        self.mark_dirty(node);
    }
}

/// `piecesFromSortOrder`.
fn pieces_from_sort_order(plan: &SortPlan) -> Vec<Piece> {
    let mut pieces: Vec<Piece> = Vec::new();
    for &token in &plan.order {
        let (kind, source_index) = plan.token_entry(token);
        if let Some(previous) = pieces.last_mut() {
            if previous.kind == kind {
                if previous.length == 1 {
                    #[allow(clippy::cast_possible_wrap)] // indices stay far below isize::MAX
                    let step = source_index as isize - previous.start as isize;
                    if step == 1 || step == -1 {
                        previous.step = step;
                        previous.length = 2;
                        continue;
                    }
                } else if previous.end_position()
                    == isize::try_from(source_index).unwrap_or(isize::MAX)
                {
                    previous.length += 1;
                    continue;
                }
            }
        }
        pieces.push(Piece {
            kind,
            start: source_index,
            length: 1,
            step: 1,
        });
    }
    pieces
}
