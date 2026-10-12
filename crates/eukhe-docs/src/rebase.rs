//! Byte-level three-way rebase: map a session's base-to-proposed edits onto a
//! newer head only through uniquely unchanged bytes.
//!
//! Ported from omp `crates/envd/src/docserver/rebase.rs`.

use std::time::{Duration, Instant};

use similar::{capture_diff_slices_deadline, Algorithm, DiffOp};

// `similar` falls back to a coarse but valid diff at the deadline, preventing
// adversarial whole-content replacements from monopolizing a request worker.
const MAX_DIFF_TIME: Duration = Duration::from_millis(50);

fn diff_ops(old: &[u8], new: &[u8]) -> Vec<DiffOp> {
    capture_diff_slices_deadline(
        Algorithm::Myers,
        old,
        new,
        Instant::now().checked_add(MAX_DIFF_TIME),
    )
}

/// A zero-based half-open byte interval.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ByteRange {
    start: u64,
    end: u64,
}

impl ByteRange {
    /// Creates a half-open range, rejecting a reversed interval.
    ///
    /// # Errors
    /// [`ByteEditError::InvalidRange`] when `start > end`.
    pub const fn new(start: u64, end: u64) -> Result<Self, ByteEditError> {
        if start > end {
            return Err(ByteEditError::InvalidRange {
                start,
                end,
                upper_bound: None,
            });
        }
        Ok(Self { start, end })
    }

    /// Returns the inclusive start coordinate.
    #[must_use]
    pub const fn start(self) -> u64 {
        self.start
    }

    /// Returns the exclusive end coordinate.
    #[must_use]
    pub const fn end(self) -> u64 {
        self.end
    }

    /// Returns the number of bytes covered by the range.
    #[must_use]
    pub const fn len(self) -> u64 {
        self.end - self.start
    }

    /// Reports whether the range is empty.
    #[must_use]
    pub const fn is_empty(self) -> bool {
        self.start == self.end
    }

    /// Validates this range against the available byte length.
    ///
    /// # Errors
    /// [`ByteEditError::InvalidRange`] when the range ends past `upper_bound`.
    pub const fn validate(self, upper_bound: u64) -> Result<Self, ByteEditError> {
        if self.end > upper_bound {
            return Err(ByteEditError::InvalidRange {
                start: self.start,
                end: self.end,
                upper_bound: Some(upper_bound),
            });
        }
        Ok(self)
    }
}

/// An edit list or coordinate that cannot be applied.
#[derive(Clone, Debug, Eq, PartialEq, thiserror::Error)]
pub enum ByteEditError {
    /// A half-open range is reversed or extends past the available content.
    #[error("invalid byte range {start}..{end} for upper bound {upper_bound:?}")]
    InvalidRange {
        /// The inclusive start coordinate.
        start: u64,
        /// The exclusive end coordinate.
        end: u64,
        /// The available length, when the range was checked against one.
        upper_bound: Option<u64>,
    },
    /// The edits are unordered, overlapping, or overflow their coordinates.
    #[error("invalid content: {reason}")]
    InvalidContent {
        /// Why the edits were rejected.
        reason: &'static str,
    },
}

/// A replacement of one half-open range in base-revision byte coordinates.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ByteEdit {
    range: ByteRange,
    replacement: Vec<u8>,
}

impl ByteEdit {
    /// Creates an edit from its base-coordinate range and exact replacement
    /// bytes.
    #[must_use]
    pub const fn new(range: ByteRange, replacement: Vec<u8>) -> Self {
        Self { range, replacement }
    }

    /// Returns the half-open range replaced by this edit.
    #[must_use]
    pub const fn range(&self) -> ByteRange {
        self.range
    }

    /// Returns the exact replacement bytes.
    #[must_use]
    pub fn replacement(&self) -> &[u8] {
        &self.replacement
    }
}

/// Base-coordinate ranges which could not be mapped uniquely onto a newer head.
#[derive(Clone, Debug, Eq, PartialEq, thiserror::Error)]
#[error("text proposal overlaps the transaction-local head")]
pub struct RebaseConflict {
    ranges: Vec<ByteRange>,
}

impl RebaseConflict {
    /// Returns the sorted conflicting ranges in base coordinates.
    #[must_use]
    pub fn ranges(&self) -> &[ByteRange] {
        &self.ranges
    }

    /// Consumes this conflict and returns its base-coordinate ranges.
    #[must_use]
    pub fn into_ranges(self) -> Vec<ByteRange> {
        self.ranges
    }
}

/// Exact content produced by edits and the affected finalized-coordinate
/// ranges.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AppliedEdits {
    content: Vec<u8>,
    changed_ranges: Vec<ByteRange>,
}

impl AppliedEdits {
    /// Returns the exact finalized bytes.
    #[must_use]
    pub fn content(&self) -> &[u8] {
        &self.content
    }

    /// Returns changed half-open ranges in finalized output coordinates.
    #[must_use]
    pub fn changed_ranges(&self) -> &[ByteRange] {
        &self.changed_ranges
    }

    /// Consumes the result into its exact bytes and finalized changed ranges.
    #[must_use]
    pub fn into_parts(self) -> (Vec<u8>, Vec<ByteRange>) {
        (self.content, self.changed_ranges)
    }
}

/// Validates that edits are sorted, non-overlapping, unambiguous, and in
/// bounds.
///
/// # Errors
/// [`ByteEditError`] for an out-of-bounds range or an unordered or overlapping
/// list.
pub fn validate_edits(base_len: u64, edits: &[ByteEdit]) -> Result<(), ByteEditError> {
    let mut previous: Option<&ByteEdit> = None;
    for edit in edits {
        let range = edit.range.validate(base_len)?;
        if let Some(prior) = previous {
            if byte_identical_duplicate(prior, edit) {
                continue;
            }
            let prior_range = prior.range;
            let starts_not_increasing = range.start() <= prior_range.start();
            let overlaps_prior = range.start() < prior_range.end();
            if starts_not_increasing || overlaps_prior {
                return Err(invalid_edits(
                    "byte edits must be sorted, non-overlapping, and have distinct starts",
                ));
            }
        }
        previous = Some(edit);
    }
    Ok(())
}

fn byte_identical_duplicate(previous: &ByteEdit, edit: &ByteEdit) -> bool {
    !edit.range.is_empty() && previous == edit
}

/// Applies validated base-coordinate edits with one allocation for the final
/// bytes.
///
/// # Errors
/// [`ByteEditError`] when the edits are invalid for `base`.
pub fn apply_edits(base: &[u8], edits: &[ByteEdit]) -> Result<AppliedEdits, ByteEditError> {
    let base_len = usize_to_u64(base.len())?;
    validate_edits(base_len, edits)?;
    let mapped = unique_edits(edits)
        .map(|edit| {
            Ok(MappedEdit {
                start: u64_to_usize(edit.range.start())?,
                end: u64_to_usize(edit.range.end())?,
                replacement: &edit.replacement,
            })
        })
        .collect::<Result<Vec<_>, ByteEditError>>()?;
    apply_mapped(base, &mapped)
}

/// Derives canonical byte edits which transform `base` into `proposed`.
///
/// # Errors
/// [`ByteEditError`] when a diff coordinate overflows.
pub fn canonical_edits(base: &[u8], proposed: &[u8]) -> Result<Vec<ByteEdit>, ByteEditError> {
    let mut edits = Vec::new();
    for operation in diff_ops(base, proposed) {
        let (old_start, old_len, new_start, new_len) = match operation {
            DiffOp::Equal { .. } => continue,
            DiffOp::Delete {
                old_index,
                old_len,
                new_index,
            } => (old_index, old_len, new_index, 0),
            DiffOp::Insert {
                old_index,
                new_index,
                new_len,
            } => (old_index, 0, new_index, new_len),
            DiffOp::Replace {
                old_index,
                old_len,
                new_index,
                new_len,
            } => (old_index, old_len, new_index, new_len),
        };
        let old_end = old_start
            .checked_add(old_len)
            .ok_or_else(|| invalid_edits("canonical edit range overflowed usize"))?;
        let new_end = new_start
            .checked_add(new_len)
            .ok_or_else(|| invalid_edits("canonical replacement range overflowed usize"))?;
        let range = ByteRange::new(usize_to_u64(old_start)?, usize_to_u64(old_end)?)?;
        edits.push(ByteEdit::new(range, proposed[new_start..new_end].to_vec()));
    }
    validate_edits(usize_to_u64(base.len())?, &edits)?;
    Ok(edits)
}

/// Rebases base-coordinate edits onto `head` only through uniquely unchanged
/// bytes.
///
/// Valid edits that overlap or ambiguously border a base-to-head change are
/// returned as the inner [`RebaseConflict`].
///
/// # Errors
/// [`ByteEditError`] when the edit list itself is invalid.
pub fn rebase_edits(
    base: &[u8],
    head: &[u8],
    edits: &[ByteEdit],
) -> Result<Result<AppliedEdits, RebaseConflict>, ByteEditError> {
    validate_edits(usize_to_u64(base.len())?, edits)?;
    if base == head {
        return apply_edits(head, edits).map(Ok);
    }
    let equal_regions = equal_regions(base, head)?;
    let mut mapped = Vec::with_capacity(edits.len());
    let mut conflicts = Vec::new();

    for edit in unique_edits(edits) {
        if let Some((start, end)) = map_range(edit.range, base, head, &equal_regions) {
            mapped.push(MappedEdit {
                start,
                end,
                replacement: &edit.replacement,
            });
        } else if conflicts.last() != Some(&edit.range) {
            conflicts.push(edit.range);
        }
    }

    if conflicts.is_empty() {
        Ok(Ok(apply_mapped(head, &mapped)?))
    } else {
        Ok(Err(RebaseConflict { ranges: conflicts }))
    }
}

/// Rebases exact proposed content, first deriving its canonical byte edits.
///
/// # Errors
/// [`ByteEditError`] when a diff coordinate overflows.
pub fn rebase_content(
    base: &[u8],
    head: &[u8],
    proposed: &[u8],
) -> Result<Result<AppliedEdits, RebaseConflict>, ByteEditError> {
    let edits = canonical_edits(base, proposed)?;
    rebase_edits(base, head, &edits)
}

fn unique_edits(edits: &[ByteEdit]) -> impl Iterator<Item = &ByteEdit> {
    let mut previous: Option<&ByteEdit> = None;
    edits.iter().filter(move |edit| {
        if previous.is_some_and(|prior| byte_identical_duplicate(prior, edit)) {
            return false;
        }
        previous = Some(edit);
        true
    })
}

#[derive(Clone, Copy)]
struct EqualRegion {
    base_start: usize,
    base_end: usize,
    head_start: usize,
    head_end: usize,
    unique: bool,
}

struct MappedEdit<'a> {
    start: usize,
    end: usize,
    replacement: &'a [u8],
}

fn equal_regions(base: &[u8], head: &[u8]) -> Result<Vec<EqualRegion>, ByteEditError> {
    let mut regions = Vec::new();
    for operation in diff_ops(base, head) {
        if let DiffOp::Equal {
            old_index,
            new_index,
            len,
        } = operation
        {
            let base_end = old_index
                .checked_add(len)
                .ok_or_else(|| invalid_edits("base mapping overflowed usize"))?;
            let head_end = new_index
                .checked_add(len)
                .ok_or_else(|| invalid_edits("head mapping overflowed usize"))?;
            let bytes = &base[old_index..base_end];
            regions.push(EqualRegion {
                base_start: old_index,
                base_end,
                head_start: new_index,
                head_end,
                unique: occurs_once(base, bytes) && occurs_once(head, bytes),
            });
        }
    }
    Ok(regions)
}

fn map_range(
    range: ByteRange,
    base: &[u8],
    head: &[u8],
    regions: &[EqualRegion],
) -> Option<(usize, usize)> {
    let start = u64_to_usize(range.start()).ok()?;
    let end = u64_to_usize(range.end()).ok()?;
    if start == end {
        return regions.iter().find_map(|region| {
            if !region.unique || start < region.base_start || start > region.base_end {
                return None;
            }
            let interior = start > region.base_start && start < region.base_end;
            let document_start = start == 0 && region.base_start == 0 && region.head_start == 0;
            let document_end = start == base.len()
                && region.base_end == base.len()
                && region.head_end == head.len();
            let offset = start.checked_sub(region.base_start)?;
            let mapped = region.head_start.checked_add(offset)?;
            (interior || document_start || document_end).then_some((mapped, mapped))
        });
    }

    regions.iter().find_map(|region| {
        if !region.unique || start < region.base_start || end > region.base_end {
            return None;
        }
        let start_offset = start.checked_sub(region.base_start)?;
        let end_offset = end.checked_sub(region.base_start)?;
        Some((
            region.head_start.checked_add(start_offset)?,
            region.head_start.checked_add(end_offset)?,
        ))
    })
}

fn apply_mapped(base: &[u8], edits: &[MappedEdit<'_>]) -> Result<AppliedEdits, ByteEditError> {
    if edits.is_empty() {
        return Ok(AppliedEdits {
            content: base.to_vec(),
            changed_ranges: Vec::new(),
        });
    }

    let mut final_len = base.len();
    for edit in edits {
        let removed = edit
            .end
            .checked_sub(edit.start)
            .ok_or_else(|| invalid_edits("mapped edit range was reversed"))?;
        final_len = final_len
            .checked_sub(removed)
            .and_then(|length| length.checked_add(edit.replacement.len()))
            .ok_or_else(|| invalid_edits("edited content length overflowed usize"))?;
    }

    let mut output = Vec::with_capacity(final_len);
    let mut source_cursor = 0usize;
    let mut changed_ranges = Vec::with_capacity(edits.len());
    for edit in edits {
        if edit.start < source_cursor || edit.end > base.len() {
            return Err(invalid_edits(
                "mapped edits were out of bounds or overlapping",
            ));
        }
        output.extend_from_slice(&base[source_cursor..edit.start]);
        let changed_start = output.len();
        output.extend_from_slice(edit.replacement);
        let changed_end = output.len();
        changed_ranges.push(ByteRange::new(
            usize_to_u64(changed_start)?,
            usize_to_u64(changed_end)?,
        )?);
        source_cursor = edit.end;
    }
    output.extend_from_slice(&base[source_cursor..]);
    if output.len() != final_len {
        return Err(invalid_edits(
            "edited content length did not match its checked size",
        ));
    }
    Ok(AppliedEdits {
        content: output,
        changed_ranges,
    })
}

fn occurs_once(haystack: &[u8], needle: &[u8]) -> bool {
    if needle.is_empty() || needle.len() > haystack.len() {
        return false;
    }
    let mut matches = haystack
        .windows(needle.len())
        .filter(|window| *window == needle);
    matches.next().is_some() && matches.next().is_none()
}

fn usize_to_u64(value: usize) -> Result<u64, ByteEditError> {
    u64::try_from(value).map_err(|_| invalid_edits("byte coordinate does not fit in u64"))
}

fn u64_to_usize(value: u64) -> Result<usize, ByteEditError> {
    usize::try_from(value).map_err(|_| invalid_edits("byte coordinate does not fit in usize"))
}

const fn invalid_edits(reason: &'static str) -> ByteEditError {
    ByteEditError::InvalidContent { reason }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn edit(start: u64, end: u64, replacement: &[u8]) -> ByteEdit {
        ByteEdit::new(
            ByteRange::new(start, end).expect("valid test range"),
            replacement.to_vec(),
        )
    }

    fn range(start: u64, end: u64) -> ByteRange {
        ByteRange::new(start, end).expect("valid test range")
    }

    #[test]
    fn direct_edits_preserve_exact_non_utf8_bytes_and_final_ranges() {
        let base = b"a\xffbcdef";
        let applied =
            apply_edits(base, &[edit(1, 4, b"\x00Z"), edit(6, 7, b"!")]).expect("edits apply");
        assert_eq!(
            applied,
            AppliedEdits {
                content: b"a\x00Zde!".to_vec(),
                changed_ranges: vec![range(1, 3), range(5, 6)],
            }
        );
    }

    #[test]
    fn canonical_edits_round_trip_exact_bytes() {
        let base = b"left\x80 middle right";
        let proposed = b"left\x80 M\x00 right!";
        let edits = canonical_edits(base, proposed).expect("canonical diff");
        let applied = apply_edits(base, &edits).expect("canonical edits apply");
        assert_eq!(applied.content(), proposed);
    }

    #[test]
    fn stale_disjoint_edit_maps_onto_head() {
        let rebased = rebase_edits(
            b"alpha beta gamma",
            b"ALPHA beta gamma",
            &[edit(11, 16, b"GAMMA")],
        )
        .expect("valid edits")
        .expect("disjoint edit");
        assert_eq!(
            rebased,
            AppliedEdits {
                content: b"ALPHA beta GAMMA".to_vec(),
                changed_ranges: vec![range(11, 16)],
            }
        );
    }

    #[test]
    fn changed_target_bytes_conflict_in_base_coordinates() {
        let conflict = rebase_edits(
            b"alpha beta gamma",
            b"alpha BETA gamma",
            &[edit(7, 9, b"xx")],
        )
        .expect("valid edits")
        .expect_err("overlap conflicts");
        assert_eq!(conflict.ranges(), &[range(7, 9)]);
    }

    #[test]
    fn insertions_at_same_changed_gap_conflict() {
        let conflict = rebase_edits(b"left-right", b"leftA-right", &[edit(4, 4, b"B")])
            .expect("valid edits")
            .expect_err("same-gap insertion conflicts");
        assert_eq!(conflict.ranges(), &[range(4, 4)]);
    }

    #[test]
    fn preceding_deletion_shifts_a_disjoint_edit() {
        let rebased = rebase_edits(
            b"remove|keep|target",
            b"keep|target",
            &[edit(12, 18, b"TARGET")],
        )
        .expect("valid edits")
        .expect("target has unique unchanged mapping");
        assert_eq!(
            rebased,
            AppliedEdits {
                content: b"keep|TARGET".to_vec(),
                changed_ranges: vec![range(5, 11)],
            }
        );
    }

    #[test]
    fn repeated_context_never_selects_an_arbitrary_alignment() {
        let conflict = rebase_edits(b"aaaa", b"aaaaa", &[edit(1, 2, b"Z")])
            .expect("valid edits")
            .expect_err("repeated alignment is ambiguous");
        assert_eq!(conflict.ranges(), &[range(1, 2)]);
    }

    #[test]
    fn duplicate_nonempty_edits_collapse_before_overlap_validation() {
        let duplicate = edit(1, 4, b"XYZ");
        let applied =
            apply_edits(b"abcdef", &[duplicate.clone(), duplicate]).expect("duplicates collapse");
        assert_eq!(
            applied,
            AppliedEdits {
                content: b"aXYZef".to_vec(),
                changed_ranges: vec![range(1, 4)],
            }
        );
    }

    #[test]
    fn duplicate_insertions_remain_ordered_distinct_edits() {
        assert!(apply_edits(b"ab", &[edit(1, 1, b"x"), edit(1, 1, b"x")]).is_err());
    }

    #[test]
    fn same_range_with_different_bytes_remains_a_conflicting_overlap() {
        assert!(validate_edits(6, &[edit(1, 4, b"x"), edit(1, 4, b"y")]).is_err());
    }

    #[test]
    fn validator_rejects_crossing_overlap() {
        assert!(validate_edits(6, &[edit(1, 4, b"x"), edit(3, 5, b"y")]).is_err());
    }

    #[test]
    fn invalid_ranges_ordering_and_overlap_are_rejected() {
        let base = b"abcdef";
        assert_eq!(
            apply_edits(base, &[edit(5, 7, b"x")]),
            Err(ByteEditError::InvalidRange {
                start: 5,
                end: 7,
                upper_bound: Some(6),
            })
        );
        assert!(apply_edits(base, &[edit(3, 5, b"x"), edit(2, 3, b"y")]).is_err());
        assert!(apply_edits(base, &[edit(1, 4, b"x"), edit(3, 5, b"y")]).is_err());
        assert!(apply_edits(base, &[edit(2, 2, b"x"), edit(2, 2, b"y")]).is_err());
    }

    #[test]
    fn content_rebase_applies_a_session_edit_over_a_disjoint_head_change() {
        let rebased = rebase_content(
            b"fn a() {}\nfn b() {}\nfn c() {}\n",
            b"fn a() { 1 }\nfn b() {}\nfn c() {}\n",
            b"fn a() {}\nfn b() {}\nfn c() { 3 }\n",
        )
        .expect("valid edits")
        .expect("disjoint rebase");
        assert_eq!(
            rebased.content(),
            b"fn a() { 1 }\nfn b() {}\nfn c() { 3 }\n"
        );
    }
}
