//! The array overlay: a piece table over base entries and inserted sources,
//! kept in a treap with a deterministic priority sequence.

use std::collections::HashMap;

use super::ordered::OrderedMap;
use crate::json::JsonValue;

/// Index of an inserted-value source in its context.
pub(crate) type SourceId = usize;

/// Where a piece's entries come from.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum PieceKind {
    /// Entries of the node's base array.
    Base,
    /// Entries of an inserted source.
    Insert(SourceId),
}

/// A run of `length` entries of one source, starting at `start` and moving by
/// `step` (`1` or `-1`).
#[derive(Clone, Copy, Debug)]
pub(crate) struct Piece {
    pub(crate) kind: PieceKind,
    pub(crate) start: usize,
    pub(crate) length: usize,
    pub(crate) step: isize,
}

#[allow(clippy::cast_possible_wrap, clippy::cast_sign_loss)] // array indices stay far below isize::MAX
impl Piece {
    pub(crate) fn base(start: usize, length: usize) -> Self {
        Self {
            kind: PieceKind::Base,
            start,
            length,
            step: 1,
        }
    }

    pub(crate) fn insert(source: SourceId, start: usize, length: usize) -> Self {
        Self {
            kind: PieceKind::Insert(source),
            start,
            length,
            step: 1,
        }
    }

    /// The source index of the entry `offset` into the piece.
    pub(crate) fn at(&self, offset: usize) -> usize {
        (self.start as isize + self.step * offset as isize) as usize
    }

    /// `start + step * length` as a signed position (may be `-1`).
    pub(crate) fn end_position(&self) -> isize {
        self.start as isize + self.step * self.length as isize
    }
}

#[derive(Debug)]
pub(crate) struct PieceNode {
    pub(crate) piece: Piece,
    left: Tree,
    right: Tree,
    priority: u32,
    elements: usize,
}

pub(crate) type Tree = Option<Box<PieceNode>>;

/// A piece's logical start and source-index bounds, for locating held entries.
#[derive(Clone, Copy, Debug)]
pub(crate) struct PieceLocation {
    piece: Piece,
    logical_start: usize,
    minimum: usize,
    maximum: usize,
}

/// The cached diff of the overlay against its base array.
#[derive(Clone, Debug)]
pub(crate) struct ArrayPlan {
    /// `(start, length)` runs of removed base entries, from the end.
    pub(crate) remove_runs: Vec<(usize, usize)>,
    pub(crate) permutation: Option<Vec<usize>>,
    /// `(logical index, first piece, end piece)` runs of inserted pieces.
    pub(crate) insert_runs: Vec<(usize, usize, usize)>,
}

#[derive(Debug)]
pub(crate) struct ArrayOverlay {
    pub(crate) root: Tree,
    pub(crate) pieces: Option<Vec<Piece>>,
    pub(crate) base_overrides: OrderedMap<usize, JsonValue>,
    pub(crate) insert_overrides: OrderedMap<SourceId, OrderedMap<usize, JsonValue>>,
    pub(crate) structural: bool,
    pub(crate) generation: u64,
    pub(crate) plan: Option<ArrayPlan>,
    seed: u32,
    base_locations: Option<Vec<PieceLocation>>,
    insert_locations: Option<HashMap<SourceId, Vec<PieceLocation>>>,
}

impl ArrayOverlay {
    pub(crate) fn new(base_length: usize) -> Self {
        let mut overlay = Self {
            root: None,
            pieces: None,
            base_overrides: OrderedMap::default(),
            insert_overrides: OrderedMap::default(),
            structural: false,
            generation: 0,
            plan: None,
            seed: 0x9e37_79b9,
            base_locations: None,
            insert_locations: None,
        };
        if base_length > 0 {
            overlay.root = Some(overlay.create_node(Piece::base(0, base_length)));
        }
        overlay
    }

    /// xorshift32 with shifts 13, 17, 5 from seed `0x9e3779b9`.
    fn next_priority(&mut self) -> u32 {
        let mut value = self.seed;
        value ^= value << 13;
        value ^= value >> 17;
        value ^= value << 5;
        self.seed = value;
        value
    }

    /// A one-piece node with the next priority.
    #[allow(clippy::unnecessary_box_returns)] // nodes only ever live boxed in a parent link
    fn create_node(&mut self, piece: Piece) -> Box<PieceNode> {
        Box::new(PieceNode {
            piece,
            left: None,
            right: None,
            priority: self.next_priority(),
            elements: piece.length,
        })
    }

    pub(crate) fn length(&self) -> usize {
        elements(&self.root)
    }

    pub(crate) fn split(&mut self, root: Tree, index: usize) -> (Tree, Tree) {
        let Some(mut node) = root else {
            return (None, None);
        };
        let left_length = elements(&node.left);
        if index < left_length {
            let (left, right) = self.split(node.left.take(), index);
            node.left = right;
            update(&mut node);
            return (left, Some(node));
        }
        let piece_end = left_length + node.piece.length;
        if index > piece_end {
            let (left, right) = self.split(node.right.take(), index - piece_end);
            node.right = left;
            update(&mut node);
            return (Some(node), right);
        }
        if index == left_length {
            let left = node.left.take();
            update(&mut node);
            return (left, Some(node));
        }
        if index == piece_end {
            let right = node.right.take();
            update(&mut node);
            return (Some(node), right);
        }
        let offset = index - left_length;
        let first = Piece {
            length: offset,
            ..node.piece
        };
        let second = Piece {
            start: node.piece.at(offset),
            length: node.piece.length - offset,
            ..node.piece
        };
        let PieceNode { left, right, .. } = *node;
        let first_node = Some(self.create_node(first));
        let second_node = Some(self.create_node(second));
        (merge(left, first_node), merge(second_node, right))
    }

    pub(crate) fn join_normalized(&mut self, left: Tree, right: Tree) -> Tree {
        let Some(left_tree) = left else {
            return right;
        };
        let Some(right_tree) = right else {
            return Some(left_tree);
        };
        let left_piece = rightmost(&left_tree).piece;
        let right_piece = leftmost(&right_tree).piece;
        if !mergeable(&left_piece, &right_piece) {
            return merge(Some(left_tree), Some(right_tree));
        }
        let left_total = left_tree.elements;
        let (left_rest, _) = self.split(Some(left_tree), left_total - left_piece.length);
        let (_, right_rest) = self.split(Some(right_tree), right_piece.length);
        #[allow(clippy::cast_possible_wrap)] // indices stay far below isize::MAX
        let step = if left_piece.length == 1 {
            right_piece.start as isize - left_piece.start as isize
        } else {
            left_piece.step
        };
        let combined = Piece {
            kind: left_piece.kind,
            start: left_piece.start,
            length: left_piece.length + right_piece.length,
            step,
        };
        let middle = Some(self.create_node(combined));
        let joined = self.join_normalized(left_rest, middle);
        self.join_normalized(joined, right_rest)
    }

    /// The pieces in order (cached until the tree changes).
    pub(crate) fn pieces(&mut self) -> &[Piece] {
        if self.pieces.is_none() {
            let mut output = Vec::new();
            flatten(&self.root, &mut output);
            self.pieces = Some(output);
        }
        self.pieces.as_deref().unwrap_or_default()
    }

    pub(crate) fn tree_from_pieces(&mut self, mut pieces: Vec<Piece>) -> Tree {
        merge_pieces(&mut pieces);
        let mut root = None;
        for piece in pieces {
            let node = Some(self.create_node(piece));
            root = merge(root, node);
        }
        root
    }

    pub(crate) fn replace_all_pieces(&mut self, pieces: Vec<Piece>) {
        self.root = self.tree_from_pieces(pieces);
        self.pieces = None;
        self.base_locations = None;
        self.insert_locations = None;
    }

    pub(crate) fn invalidate_caches(&mut self) {
        self.pieces = None;
        self.base_locations = None;
        self.insert_locations = None;
        self.plan = None;
    }

    /// The piece holding logical `index` and the offset into it.
    pub(crate) fn locate(&self, mut index: usize) -> Option<(Piece, usize)> {
        let mut node = self.root.as_deref();
        while let Some(current) = node {
            let left_length = elements(&current.left);
            if index < left_length {
                node = current.left.as_deref();
            } else if index >= left_length + current.piece.length {
                index -= left_length + current.piece.length;
                node = current.right.as_deref();
            } else {
                return Some((current.piece, index - left_length));
            }
        }
        None
    }

    /// The rightmost piece.
    pub(crate) fn tail_piece(&self) -> Option<Piece> {
        self.root.as_deref().map(|root| rightmost(root).piece)
    }

    pub(crate) fn extend_rightmost(&mut self, amount: usize) {
        if let Some(root) = self.root.as_deref_mut() {
            extend_rightmost(root, amount);
        }
    }

    fn ensure_locations(&mut self) {
        if self.base_locations.is_some() {
            return;
        }
        let mut base = Vec::new();
        let mut inserted: HashMap<SourceId, Vec<PieceLocation>> = HashMap::new();
        let mut logical_start = 0;
        for piece in self.pieces().to_vec() {
            let last = piece.at(piece.length - 1);
            let location = PieceLocation {
                piece,
                logical_start,
                minimum: piece.start.min(last),
                maximum: piece.start.max(last),
            };
            match piece.kind {
                PieceKind::Base => base.push(location),
                PieceKind::Insert(source) => inserted.entry(source).or_default().push(location),
            }
            logical_start += piece.length;
        }
        base.sort_by_key(|location| location.minimum);
        for locations in inserted.values_mut() {
            locations.sort_by_key(|location| location.minimum);
        }
        self.base_locations = Some(base);
        self.insert_locations = Some(inserted);
    }

    /// The logical index of a source entry, if it is still in the array.
    pub(crate) fn find_entry_index(
        &mut self,
        kind: PieceKind,
        source_index: usize,
    ) -> Option<usize> {
        if kind == PieceKind::Base && !self.structural {
            return Some(source_index);
        }
        self.ensure_locations();
        let locations = match kind {
            PieceKind::Base => self.base_locations.as_ref()?,
            PieceKind::Insert(source) => self.insert_locations.as_ref()?.get(&source)?,
        };
        let low = locations.partition_point(|location| location.minimum <= source_index);
        let location = locations.get(low.checked_sub(1)?)?;
        if source_index > location.maximum {
            return None;
        }
        #[allow(clippy::cast_possible_wrap, clippy::cast_sign_loss)]
        // indices stay far below isize::MAX
        let offset = (source_index as isize - location.piece.start as isize) / location.piece.step;
        #[allow(clippy::cast_sign_loss)] // checked non-negative
        (offset >= 0 && (offset as usize) < location.piece.length)
            .then(|| location.logical_start + offset as usize)
    }
}

fn elements(tree: &Tree) -> usize {
    tree.as_ref().map_or(0, |node| node.elements)
}

fn update(node: &mut PieceNode) {
    node.elements = elements(&node.left) + node.piece.length + elements(&node.right);
}

pub(crate) fn merge(left: Tree, right: Tree) -> Tree {
    match (left, right) {
        (None, right) => right,
        (left, None) => left,
        (Some(mut left), Some(mut right)) => {
            if left.priority >= right.priority {
                left.right = merge(left.right.take(), Some(right));
                update(&mut left);
                Some(left)
            } else {
                right.left = merge(Some(left), right.left.take());
                update(&mut right);
                Some(right)
            }
        }
    }
}

fn leftmost(mut node: &PieceNode) -> &PieceNode {
    while let Some(left) = node.left.as_deref() {
        node = left;
    }
    node
}

fn rightmost(mut node: &PieceNode) -> &PieceNode {
    while let Some(right) = node.right.as_deref() {
        node = right;
    }
    node
}

fn extend_rightmost(node: &mut PieceNode, amount: usize) {
    match node.right.as_deref_mut() {
        Some(right) => extend_rightmost(right, amount),
        None => node.piece.length += amount,
    }
    update(node);
}

fn flatten(tree: &Tree, output: &mut Vec<Piece>) {
    if let Some(node) = tree {
        flatten(&node.left, output);
        output.push(node.piece);
        flatten(&node.right, output);
    }
}

#[allow(clippy::cast_possible_wrap)] // indices stay far below isize::MAX
pub(crate) fn mergeable(left: &Piece, right: &Piece) -> bool {
    if left.kind != right.kind {
        return false;
    }
    if left.length == 1 && right.length == 1 {
        return (right.start as isize - left.start as isize).abs() == 1;
    }
    left.step == right.step && left.end_position() == right.start as isize
}

#[allow(clippy::cast_possible_wrap)] // indices stay far below isize::MAX
pub(crate) fn merge_pieces(pieces: &mut Vec<Piece>) {
    let mut index = 1;
    while index < pieces.len() {
        let left = pieces[index - 1];
        let right = pieces[index];
        let same_source = left.kind == right.kind;
        let distance = right.start as isize - left.start as isize;
        if same_source && left.length == 1 && right.length == 1 && distance.abs() == 1 {
            pieces[index - 1].step = distance;
            pieces[index - 1].length = 2;
            pieces.remove(index);
        } else if same_source
            && left.step == right.step
            && left.end_position() == right.start as isize
        {
            pieces[index - 1].length += right.length;
            pieces.remove(index);
        } else {
            index += 1;
        }
    }
}

/// `appendMergedPiece`.
#[allow(clippy::cast_possible_wrap)] // indices stay far below isize::MAX
pub(crate) fn append_merged(pieces: &mut Vec<Piece>, piece: Piece) {
    if let Some(previous) = pieces.last_mut() {
        let same_source = previous.kind == piece.kind;
        if same_source && previous.length == 1 && piece.length == 1 {
            let step = piece.start as isize - previous.start as isize;
            if step == 1 || step == -1 {
                previous.step = step;
                previous.length = 2;
                return;
            }
        }
        if same_source
            && previous.step == piece.step
            && previous.end_position() == piece.start as isize
        {
            previous.length += piece.length;
            return;
        }
    }
    pieces.push(piece);
}

/// Build the plan: removed base runs, the permutation of retained base
/// entries, and the runs of inserted pieces (`buildArrayPlan`).
pub(crate) fn build_plan(pieces: &[Piece], base_length: usize) -> ArrayPlan {
    let mut retained = vec![false; base_length];
    let mut target_base = Vec::new();
    for piece in pieces {
        if piece.kind != PieceKind::Base {
            continue;
        }
        for offset in 0..piece.length {
            let index = piece.at(offset);
            retained[index] = true;
            target_base.push(index);
        }
    }
    let mut remove_runs = Vec::new();
    let mut end = base_length;
    while end > 0 {
        if retained[end - 1] {
            end -= 1;
            continue;
        }
        let mut start = end - 1;
        while start > 0 && !retained[start - 1] {
            start -= 1;
        }
        remove_runs.push((start, end - start));
        end = start;
    }
    let retained_base: Vec<usize> = (0..base_length).filter(|index| retained[*index]).collect();
    let permutation = if target_base
        .iter()
        .zip(&retained_base)
        .any(|(target, kept)| target != kept)
        || target_base.len() != retained_base.len()
    {
        let mut positions = vec![0usize; base_length];
        for (position, value) in retained_base.iter().enumerate() {
            positions[*value] = position;
        }
        Some(target_base.iter().map(|value| positions[*value]).collect())
    } else {
        None
    };
    let mut insert_runs = Vec::new();
    let mut logical_index = 0;
    let mut piece_index = 0;
    while piece_index < pieces.len() {
        if pieces[piece_index].kind == PieceKind::Base {
            logical_index += pieces[piece_index].length;
            piece_index += 1;
            continue;
        }
        let start_piece = piece_index;
        let run_start = logical_index;
        while piece_index < pieces.len() && pieces[piece_index].kind != PieceKind::Base {
            logical_index += pieces[piece_index].length;
            piece_index += 1;
        }
        insert_runs.push((run_start, start_piece, piece_index));
    }
    ArrayPlan {
        remove_runs,
        permutation,
        insert_runs,
    }
}
