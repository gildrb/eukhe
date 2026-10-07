//! Compact operation batches between two immutable revisions
//! (`delta/diff.ts`). Container identity (shared `Arc`s) anchors array
//! alignment, as object identity does in TS.

use std::collections::HashMap;
use std::sync::Arc;

use super::ops::{is_reserved_segment, Op, Path, Seg};
use super::overlap::overlap;
use crate::json::{utf16_len, utf16_skip, write_js_number, JsonValue};

const DEFAULT_OVERLAP_SCAN: usize = 65_536;
const MAX_DELTA_OPERATIONS: usize = 4_096;
const MAX_IDENTITY_CANDIDATES: usize = 200_000;
const MAX_SEMANTIC_CELLS: usize = 65_536;

/// JS `SameValueZero` identity of a value, usable as a map key.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Identity {
    Null,
    Bool(bool),
    Number(u64),
    String(Arc<str>),
    Container(usize),
}

fn identity(value: &JsonValue) -> Identity {
    match value {
        JsonValue::Null => Identity::Null,
        JsonValue::Bool(flag) => Identity::Bool(*flag),
        // -0 and 0 are the same key.
        JsonValue::Number(number) => Identity::Number((number.get() + 0.0).to_bits()),
        JsonValue::String(text) => Identity::String(Arc::clone(text)),
        container => Identity::Container(container.container_address().unwrap_or(0)),
    }
}

struct Batch {
    operations: Vec<Op>,
    overflowed: bool,
}

impl Batch {
    fn emit(&mut self, operation: Op) {
        if self.overflowed {
            return;
        }
        if self.operations.len() >= MAX_DELTA_OPERATIONS {
            self.overflowed = true;
            return;
        }
        self.operations.push(operation);
    }

    fn emit_set(&mut self, path: Path, value: JsonValue) {
        if path.is_empty() {
            self.emit(Op::Replace(value));
        } else {
            self.emit(Op::Set(path, value));
        }
    }
}

fn extend(path: &[Seg], segment: Seg) -> Path {
    let mut next = Vec::with_capacity(path.len() + 1);
    next.extend_from_slice(path);
    next.push(segment);
    next
}

fn same_value(left: &JsonValue, right: &JsonValue) -> bool {
    left.strict_equals(right) || left == right
}

fn permutation(before: &[JsonValue], after: &[JsonValue]) -> Option<Vec<usize>> {
    if before.len() != after.len() {
        return None;
    }
    let mut positions: HashMap<Identity, (Vec<usize>, usize)> = HashMap::new();
    for (index, value) in before.iter().enumerate() {
        positions.entry(identity(value)).or_default().0.push(index);
    }
    let mut result = Vec::with_capacity(after.len());
    for value in after {
        let (indices, used) = positions.get_mut(&identity(value))?;
        if *used == indices.len() {
            return None;
        }
        result.push(indices[*used]);
        *used += 1;
    }
    Some(result)
}

fn emit_string(before: &str, after: &str, path: Path, batch: &mut Batch) {
    if before == after {
        return;
    }
    if after.len() > before.len() && after.starts_with(before) {
        batch.emit(Op::Append(path, after[before.len()..].to_owned()));
        return;
    }
    let shared = overlap(before, after, DEFAULT_OVERLAP_SCAN);
    if shared == 0 {
        batch.emit(Op::Set(path, JsonValue::from(after)));
        return;
    }
    batch.emit(Op::Truncate(path.clone(), utf16_len(before) - shared));
    if utf16_len(after) > shared {
        batch.emit(Op::Append(path, utf16_skip(after, shared).to_owned()));
    }
}

type ArrayMatch = (usize, usize);

fn lcs_matches(
    before: &[JsonValue],
    after: &[JsonValue],
    equal: fn(&JsonValue, &JsonValue) -> bool,
    max_cells: usize,
) -> Option<Vec<ArrayMatch>> {
    if before.is_empty() || after.is_empty() {
        return Some(Vec::new());
    }
    if before.len().saturating_mul(after.len()) > max_cells {
        return None;
    }
    let width = after.len() + 1;
    let mut lengths = vec![0u32; (before.len() + 1) * width];
    for left in (0..before.len()).rev() {
        for right in (0..after.len()).rev() {
            let at = left * width + right;
            lengths[at] = if equal(&before[left], &after[right]) {
                lengths[(left + 1) * width + right + 1] + 1
            } else {
                lengths[(left + 1) * width + right].max(lengths[left * width + right + 1])
            };
        }
    }
    let mut matches = Vec::new();
    let (mut left, mut right) = (0, 0);
    while left < before.len() && right < after.len() {
        if equal(&before[left], &after[right])
            && lengths[left * width + right] == lengths[(left + 1) * width + right + 1] + 1
        {
            matches.push((left, right));
            left += 1;
            right += 1;
        } else if lengths[(left + 1) * width + right] >= lengths[left * width + right + 1] {
            left += 1;
        } else {
            right += 1;
        }
    }
    Some(matches)
}

fn semantically_aligned(left: &JsonValue, right: &JsonValue) -> bool {
    if same_value(left, right) {
        return true;
    }
    match (left, right) {
        (JsonValue::Array(left), JsonValue::Array(right)) => {
            left.len() == right.len()
                && left
                    .iter()
                    .zip(right.iter())
                    .any(|(value, other)| value.is_container() && value.strict_equals(other))
        }
        (JsonValue::Object(left), JsonValue::Object(right)) => left.iter().any(|(key, value)| {
            value.is_container()
                && right
                    .get(key)
                    .is_some_and(|other| value.strict_equals(other))
        }),
        _ => false,
    }
}

fn identity_subsequence(
    before: &[JsonValue],
    (before_start, before_end): (usize, usize),
    after: &[JsonValue],
    (after_start, after_end): (usize, usize),
) -> Option<Vec<ArrayMatch>> {
    let before_count = before_end - before_start;
    let after_count = after_end - after_start;
    let mut matches = Vec::new();
    if after_count < before_count {
        let mut before_index = before_start;
        for (after_index, value) in after.iter().enumerate().take(after_end).skip(after_start) {
            while before_index < before_end && !before[before_index].strict_equals(value) {
                before_index += 1;
            }
            if before_index == before_end {
                return None;
            }
            matches.push((before_index, after_index));
            before_index += 1;
        }
        return Some(matches);
    }
    if before_count < after_count {
        let mut after_index = after_start;
        for (before_index, value) in before
            .iter()
            .enumerate()
            .take(before_end)
            .skip(before_start)
        {
            while after_index < after_end && !value.strict_equals(&after[after_index]) {
                after_index += 1;
            }
            if after_index == after_end {
                return None;
            }
            matches.push((before_index, after_index));
            after_index += 1;
        }
        return Some(matches);
    }
    None
}

fn greedy_identity_anchors(
    positions: &HashMap<Identity, Vec<usize>>,
    after: &[JsonValue],
    (after_start, after_end): (usize, usize),
) -> Vec<ArrayMatch> {
    let mut matches = Vec::new();
    let mut previous: Option<usize> = None;
    for (after_index, value) in after.iter().enumerate().take(after_end).skip(after_start) {
        let Some(candidates) = positions.get(&identity(value)) else {
            continue;
        };
        let minimum = previous.map_or(0, |previous| previous + 1);
        let at = candidates.partition_point(|candidate| *candidate < minimum);
        let Some(&before_index) = candidates.get(at) else {
            continue;
        };
        matches.push((before_index, after_index));
        previous = Some(before_index);
    }
    matches
}

/// A patience-sorting candidate of [`identity_anchors`].
struct Candidate {
    before: usize,
    after: usize,
    previous: Option<usize>,
}

fn identity_anchors(
    before: &[JsonValue],
    (before_start, before_end): (usize, usize),
    after: &[JsonValue],
    (after_start, after_end): (usize, usize),
) -> Vec<ArrayMatch> {
    let mut positions: HashMap<Identity, Vec<usize>> = HashMap::new();
    for (index, value) in before
        .iter()
        .enumerate()
        .take(before_end)
        .skip(before_start)
    {
        positions.entry(identity(value)).or_default().push(index);
    }
    let mut candidate_count = 0;
    for value in &after[after_start..after_end] {
        candidate_count += positions.get(&identity(value)).map_or(0, Vec::len);
        if candidate_count > MAX_IDENTITY_CANDIDATES {
            return greedy_identity_anchors(&positions, after, (after_start, after_end));
        }
    }
    if candidate_count == 0 {
        return Vec::new();
    }
    // Longest increasing subsequence of before-indices over after order.
    let mut candidates: Vec<Candidate> = Vec::new();
    let mut tails: Vec<usize> = Vec::new();
    let mut tail_values: Vec<usize> = Vec::new();
    for (after_index, value) in after.iter().enumerate().take(after_end).skip(after_start) {
        let Some(before_positions) = positions.get(&identity(value)) else {
            continue;
        };
        for &before_index in before_positions.iter().rev() {
            let at = tail_values.partition_point(|tail| *tail < before_index);
            let candidate_index = candidates.len();
            candidates.push(Candidate {
                before: before_index,
                after: after_index,
                previous: at.checked_sub(1).map(|previous| tails[previous]),
            });
            if at == tails.len() {
                tails.push(candidate_index);
                tail_values.push(before_index);
            } else {
                tails[at] = candidate_index;
                tail_values[at] = before_index;
            }
        }
    }
    let mut matches = Vec::new();
    let mut candidate_index = tails.last().copied();
    while let Some(index) = candidate_index {
        let candidate = &candidates[index];
        matches.push((candidate.before, candidate.after));
        candidate_index = candidate.previous;
    }
    matches.reverse();
    matches
}

/// One aligned region of `before[before_start..before_end]` against
/// `after[after_start..after_end]`, whose first entry sits at `output_start`.
#[derive(Clone, Copy)]
struct Region {
    before_start: usize,
    before_end: usize,
    after_start: usize,
    after_end: usize,
    output_start: usize,
}

fn process_array_matches(
    before: &[JsonValue],
    after: &[JsonValue],
    path: &[Seg],
    batch: &mut Batch,
    region: Region,
    matches: &[ArrayMatch],
) {
    let mut before_at = region.before_start;
    let mut after_at = region.after_start;
    let mut output_at = region.output_start;
    for &(before_match, after_match) in matches {
        if batch.overflowed {
            return;
        }
        diff_array_region(
            before,
            after,
            path,
            batch,
            Region {
                before_start: before_at,
                before_end: before_match,
                after_start: after_at,
                after_end: after_match,
                output_start: output_at,
            },
        );
        output_at += after_match - after_at;
        if !same_value(&before[before_match], &after[after_match]) {
            diff_value(
                &before[before_match],
                &after[after_match],
                &extend(path, Seg::Index(output_at)),
                batch,
            );
        }
        output_at += 1;
        before_at = before_match + 1;
        after_at = after_match + 1;
    }
    if !batch.overflowed {
        diff_array_region(
            before,
            after,
            path,
            batch,
            Region {
                before_start: before_at,
                before_end: region.before_end,
                after_start: after_at,
                after_end: region.after_end,
                output_start: output_at,
            },
        );
    }
}

#[allow(clippy::too_many_lines)] // one TS function: the alignment strategies in their fallback order
fn diff_array_region(
    before: &[JsonValue],
    after: &[JsonValue],
    path: &[Seg],
    batch: &mut Batch,
    region: Region,
) {
    if batch.overflowed {
        return;
    }
    let Region {
        mut before_start,
        mut before_end,
        mut after_start,
        mut after_end,
        mut output_start,
    } = region;
    while before_start < before_end
        && after_start < after_end
        && same_value(&before[before_start], &after[after_start])
    {
        before_start += 1;
        after_start += 1;
        output_start += 1;
    }
    while before_start < before_end
        && after_start < after_end
        && same_value(&before[before_end - 1], &after[after_end - 1])
    {
        before_end -= 1;
        after_end -= 1;
    }
    let before_count = before_end - before_start;
    let after_count = after_end - after_start;
    if before_count == 0 && after_count == 0 {
        return;
    }
    let trimmed = Region {
        before_start,
        before_end,
        after_start,
        after_end,
        output_start,
    };
    if before_count == 0 || after_count == 0 {
        batch.emit(Op::Splice(
            path.to_vec(),
            output_start,
            before_count,
            after[after_start..after_end].to_vec(),
        ));
        return;
    }
    if before_count == after_count {
        let positional: Vec<ArrayMatch> = (0..before_count)
            .filter(|offset| {
                same_value(&before[before_start + offset], &after[after_start + offset])
            })
            .map(|offset| (before_start + offset, after_start + offset))
            .collect();
        if !positional.is_empty() {
            process_array_matches(before, after, path, batch, trimmed, &positional);
            return;
        }
    }
    if let Some(subsequence) = identity_subsequence(
        before,
        (before_start, before_end),
        after,
        (after_start, after_end),
    ) {
        if !subsequence.is_empty() {
            process_array_matches(before, after, path, batch, trimmed, &subsequence);
            return;
        }
    }
    let anchors = identity_anchors(
        before,
        (before_start, before_end),
        after,
        (after_start, after_end),
    );
    if !anchors.is_empty() {
        process_array_matches(before, after, path, batch, trimmed, &anchors);
        return;
    }
    if let Some(semantic) = lcs_matches(
        &before[before_start..before_end],
        &after[after_start..after_end],
        semantically_aligned,
        MAX_SEMANTIC_CELLS,
    ) {
        if !semantic.is_empty() {
            let absolute: Vec<ArrayMatch> = semantic
                .into_iter()
                .map(|(before_index, after_index)| {
                    (before_start + before_index, after_start + after_index)
                })
                .collect();
            process_array_matches(before, after, path, batch, trimmed, &absolute);
            return;
        }
    }
    if before_count == 1 && after_count == 1 {
        diff_value(
            &before[before_start],
            &after[after_start],
            &extend(path, Seg::Index(output_start)),
            batch,
        );
        return;
    }
    batch.emit(Op::Splice(
        path.to_vec(),
        output_start,
        before_count,
        after[after_start..after_end].to_vec(),
    ));
}

fn diff_array(before: &JsonValue, after: &JsonValue, path: &[Seg], batch: &mut Batch) {
    if before.strict_equals(after) || before == after {
        return;
    }
    let (Some(before_items), Some(after_items)) = (before.as_array(), after.as_array()) else {
        return;
    };
    let length = before_items.len();
    if length == after_items.len()
        && length > 1
        && !same_value(&before_items[0], &after_items[0])
        && !same_value(&before_items[length - 1], &after_items[length - 1])
    {
        if let Some(order) = permutation(before_items, after_items) {
            batch.emit(Op::Move(path.to_vec(), order));
            return;
        }
    }
    diff_array_region(
        before_items,
        after_items,
        path,
        batch,
        Region {
            before_start: 0,
            before_end: length,
            after_start: 0,
            after_end: after_items.len(),
            output_start: 0,
        },
    );
}

fn diff_object(before: &JsonValue, after: &JsonValue, path: &[Seg], batch: &mut Batch) {
    let (Some(before_object), Some(after_object)) = (before.as_object(), after.as_object()) else {
        return;
    };
    if before_object
        .keys()
        .chain(after_object.keys())
        .any(is_reserved_segment)
    {
        if before != after {
            batch.emit_set(path.to_vec(), after.clone());
        }
        return;
    }
    for (key, after_value) in after_object.shared_iter() {
        if batch.overflowed {
            return;
        }
        let next = extend(path, Seg::Key(Arc::clone(key)));
        match before_object.get(key) {
            Some(before_value) => diff_value(before_value, after_value, &next, batch),
            None => batch.emit_set(next, after_value.clone()),
        }
    }
    for (key, _) in before_object.shared_iter() {
        if batch.overflowed {
            return;
        }
        if !after_object.contains_key(key) {
            batch.emit(Op::Delete(extend(path, Seg::Key(Arc::clone(key)))));
        }
    }
}

fn diff_value(before: &JsonValue, after: &JsonValue, path: &[Seg], batch: &mut Batch) {
    if before.strict_equals(after) || batch.overflowed {
        return;
    }
    match (before, after) {
        (JsonValue::String(old), JsonValue::String(new)) if !path.is_empty() => {
            emit_string(old, new, path.to_vec(), batch);
        }
        (JsonValue::Array(_), JsonValue::Array(_)) => diff_array(before, after, path, batch),
        (JsonValue::Object(_), JsonValue::Object(_)) => diff_object(before, after, path, batch),
        _ => batch.emit_set(path.to_vec(), after.clone()),
    }
}

fn number_length(value: f64) -> usize {
    let mut text = String::new();
    write_js_number(&mut text, value);
    text.len()
}

#[allow(clippy::cast_precision_loss)] // counts and indices stay below 2^53
fn usize_length(value: usize) -> usize {
    number_length(value as f64)
}

fn json_cost(value: &JsonValue) -> usize {
    match value {
        JsonValue::Null | JsonValue::Bool(true) => 4,
        JsonValue::Bool(false) => 5,
        JsonValue::String(text) => utf16_len(text) + 2,
        JsonValue::Number(number) => number_length(number.get()),
        JsonValue::Array(items) => {
            let mut cost = 2;
            for (index, item) in items.iter().enumerate() {
                cost += json_cost(item) + usize::from(index != 0);
            }
            cost
        }
        JsonValue::Object(object) => {
            let mut cost = 2;
            for (index, (key, item)) in object.iter().enumerate() {
                cost += utf16_len(key) + 3 + json_cost(item) + usize::from(index != 0);
            }
            cost
        }
    }
}

fn path_cost(path: &[Seg]) -> usize {
    let mut cost = 2;
    for (index, segment) in path.iter().enumerate() {
        cost += match segment {
            Seg::Key(key) => utf16_len(key) + 2,
            Seg::Index(index) => usize_length(*index),
        } + usize::from(index != 0);
    }
    cost
}

fn operation_cost(operation: &Op) -> usize {
    match operation {
        Op::Replace(value) => 6 + json_cost(value),
        Op::Set(path, value) => 7 + path_cost(path) + json_cost(value),
        Op::Delete(path) => 6 + path_cost(path),
        Op::Append(path, text) => 7 + path_cost(path) + utf16_len(text) + 2,
        Op::Truncate(path, count) => 7 + path_cost(path) + usize_length(*count),
        Op::Splice(path, index, remove, items) => {
            let mut items_cost = 2;
            for (at, item) in items.iter().enumerate() {
                items_cost += json_cost(item) + usize::from(at != 0);
            }
            10 + path_cost(path) + usize_length(*index) + usize_length(*remove) + items_cost
        }
        Op::Move(path, permutation) => {
            let mut cost = 2;
            for (at, index) in permutation.iter().enumerate() {
                cost += usize_length(*index) + usize::from(at != 0);
            }
            7 + path_cost(path) + cost
        }
    }
}

/// Compute a compact operation batch from two immutable revisions
/// (`diffRevisions`). Applying it to `before` yields a value equal to
/// `after`; oversized batches fold to `[r(after)]`.
///
/// ```
/// use eukhe_chord::delta::{diff_revisions, Op};
/// use eukhe_chord::json::JsonValue;
/// let before = JsonValue::parse(r#"{"text":"hello"}"#).unwrap();
/// let after = JsonValue::parse(r#"{"text":"hello world"}"#).unwrap();
/// assert_eq!(diff_revisions(&before, &after), [Op::Append(vec!["text".into()], " world".into())]);
/// ```
#[must_use]
pub fn diff_revisions(before: &JsonValue, after: &JsonValue) -> Vec<Op> {
    let mut batch = Batch {
        operations: Vec::new(),
        overflowed: false,
    };
    diff_value(before, after, &[], &mut batch);
    if batch.overflowed {
        return vec![Op::Replace(after.clone())];
    }
    let operations = batch.operations;
    if operations.first().is_none_or(Op::is_replace) {
        return operations;
    }
    let mut delta_cost = 2;
    for operation in &operations {
        delta_cost += operation_cost(operation) + 1;
    }
    if delta_cost < 65_536 {
        return operations;
    }
    let snapshot_cost = json_cost(after) + 6;
    if delta_cost >= snapshot_cost {
        vec![Op::Replace(after.clone())]
    } else {
        operations
    }
}
