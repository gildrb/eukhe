//! Stale-tag anchor recovery (omp `modes/hashline/recovery.rs`).
//!
//! A section whose tag names an older snapshot is remapped onto the live
//! text through a line diff. The remap holds only when every anchor's
//! neighbours moved by the same offset (duplicated lines need both
//! neighbours) and all anchors share one offset.

use std::{
    collections::{HashMap, HashSet},
    path::Path,
    sync::Arc,
};

use super::{
    apply::apply_edits,
    messages::{
        RECOVERY_EXTERNAL_WARNING, RECOVERY_LINE_REMAP_WARNING, RECOVERY_SESSION_CHAIN_WARNING,
    },
    types::{Anchor, ApplyResult, Cursor, Edit, ParsedRange, PasteTarget},
};
use crate::store::{Clipboard, EditStore};

fn edit_anchors(edit: &Edit) -> Vec<Anchor> {
    match edit {
        Edit::Delete { anchor, .. } | Edit::Block { anchor, .. } => vec![*anchor],
        Edit::Cut { range, .. } => (range.start.line..=range.end.line)
            .map(|line| Anchor { line })
            .collect(),
        Edit::Paste {
            at: PasteTarget::Span { range },
            ..
        } => (range.start.line..=range.end.line)
            .map(|line| Anchor { line })
            .collect(),
        Edit::Paste {
            at: PasteTarget::Gap { cursor },
            ..
        }
        | Edit::Insert { cursor, .. } => match cursor {
            Cursor::BeforeAnchor(anchor) | Cursor::AfterAnchor(anchor) => vec![*anchor],
            Cursor::Bof | Cursor::Eof => Vec::new(),
        },
    }
}

fn build_line_map(previous: &str, current: &str) -> HashMap<u32, u32> {
    let mut map = HashMap::new();
    let mut previous_line = 1_u32;
    let mut current_line = 1_u32;
    for run in crate::diff::line_runs(previous, current) {
        if run.added {
            current_line += run.count;
        } else if run.removed {
            previous_line += run.count;
        } else {
            for offset in 0..run.count {
                map.insert(previous_line + offset, current_line + offset);
            }
            previous_line += run.count;
            current_line += run.count;
        }
    }
    map
}

fn duplicated_values(lines: &[&str]) -> HashSet<String> {
    let mut seen = HashSet::new();
    let mut duplicated = HashSet::new();
    for line in lines {
        if !seen.insert(*line) {
            duplicated.insert((*line).to_owned());
        }
    }
    duplicated
}

#[derive(Clone, Copy)]
struct Neighbors {
    before: Option<u32>,
    after: Option<u32>,
}

fn anchor_neighbors(anchor_lines: &HashSet<u32>, line_count: usize) -> HashMap<u32, Neighbors> {
    let mut sorted: Vec<_> = anchor_lines.iter().copied().collect();
    sorted.sort_unstable();
    let mut neighbors = HashMap::new();
    let mut i = 0;
    while i < sorted.len() {
        let mut j = i;
        while j + 1 < sorted.len() && sorted[j + 1] == sorted[j] + 1 {
            j += 1;
        }
        let start = sorted[i];
        let end = sorted[j];
        let before = (start > 1).then_some(start - 1);
        let after = ((end as usize) < line_count).then_some(end + 1);
        for &line in &sorted[i..=j] {
            neighbors.insert(line, Neighbors { before, after });
        }
        i = j + 1;
    }
    neighbors
}

fn validate_context(
    previous: &str,
    current: &str,
    line_map: &HashMap<u32, u32>,
    edits: &[Edit],
) -> bool {
    let previous_lines: Vec<_> = previous.split('\n').collect();
    let current_lines: Vec<_> = current.split('\n').collect();
    let anchors: HashSet<_> = edits
        .iter()
        .flat_map(edit_anchors)
        .map(|anchor| anchor.line)
        .collect();
    let previous_duplicates = duplicated_values(&previous_lines);
    let current_duplicates = duplicated_values(&current_lines);
    for (line, neighbors) in anchor_neighbors(&anchors, previous_lines.len()) {
        let Some(&mapped) = line_map.get(&line) else {
            return false;
        };
        let previous_value = previous_lines
            .get((line - 1) as usize)
            .copied()
            .unwrap_or("");
        let current_value = current_lines
            .get((mapped - 1) as usize)
            .copied()
            .unwrap_or("");
        if !previous_duplicates.contains(previous_value)
            && !current_duplicates.contains(current_value)
        {
            let offset = i64::from(mapped) - i64::from(line);
            let after_matches = neighbors.after.is_some_and(|after| {
                line_map
                    .get(&after)
                    .is_some_and(|&value| i64::from(value) == i64::from(after) + offset)
            });
            let before_matches = neighbors.before.is_some_and(|before| {
                line_map
                    .get(&before)
                    .is_some_and(|&value| i64::from(value) == i64::from(before) + offset)
            });
            if !after_matches && !before_matches {
                return false;
            }
        } else {
            let mut checked = false;
            if let Some(before) = neighbors.before {
                checked = true;
                if line_map.get(&before).copied() != mapped.checked_sub(line - before) {
                    return false;
                }
            }
            if let Some(after) = neighbors.after {
                checked = true;
                if line_map.get(&after).copied() != Some(mapped + (after - line)) {
                    return false;
                }
            }
            if !checked {
                return false;
            }
        }
    }
    true
}

fn map_line(line_map: &HashMap<u32, u32>, line: u32, offsets: &mut Vec<i64>) -> Option<u32> {
    let mapped = *line_map.get(&line)?;
    offsets.push(i64::from(mapped) - i64::from(line));
    Some(mapped)
}

fn remap_edits(previous: &str, current: &str, edits: &[Edit]) -> Option<(Vec<Edit>, i64)> {
    let line_map = build_line_map(previous, current);
    if !validate_context(previous, current, &line_map, edits) {
        return None;
    }
    let mut offsets = Vec::new();
    let mut remapped = edits.to_vec();
    for edit in &mut remapped {
        match edit {
            Edit::Delete { anchor, .. } | Edit::Block { anchor, .. } => {
                anchor.line = map_line(&line_map, anchor.line, &mut offsets)?;
            }
            Edit::Cut { range, .. }
            | Edit::Paste {
                at: PasteTarget::Span { range },
                ..
            } => {
                let start = map_line(&line_map, range.start.line, &mut offsets)?;
                let mut end = start;
                for line in range.start.line + 1..=range.end.line {
                    end = map_line(&line_map, line, &mut offsets)?;
                }
                *range = ParsedRange {
                    start: Anchor { line: start },
                    end: Anchor { line: end },
                };
            }
            Edit::Paste {
                at: PasteTarget::Gap { cursor },
                ..
            }
            | Edit::Insert { cursor, .. } => match cursor {
                Cursor::BeforeAnchor(anchor) | Cursor::AfterAnchor(anchor) => {
                    anchor.line = map_line(&line_map, anchor.line, &mut offsets)?;
                }
                Cursor::Bof | Cursor::Eof => {}
            },
        }
    }
    let (&first, rest) = offsets.split_first()?;
    if rest.iter().any(|offset| *offset != first) {
        return None;
    }
    Some((remapped, first))
}

/// Remap `edits`, authored against the snapshot `store` holds for
/// `file_hash`, onto `current_text` and apply them there.
///
/// `None` when no snapshot carries the tag, the remap does not hold, the
/// remapped edits do not apply, or they change nothing: the caller then
/// rejects the section as stale.
pub(crate) fn try_recover(
    store: &EditStore,
    path: &Path,
    current_text: &str,
    file_hash: &str,
    edits: &[Edit],
    clipboard: &mut Clipboard,
) -> Option<ApplyResult> {
    let snapshot = store.by_hash(path, file_hash)?;
    // The head snapshot is the last observed disk state, so its tag going
    // stale means another writer changed the file; an older one means this
    // session's own edits advanced the tag.
    let chain_warning = if store
        .head(path)
        .is_some_and(|head| Arc::ptr_eq(&head.text, &snapshot.text))
    {
        RECOVERY_EXTERNAL_WARNING
    } else {
        RECOVERY_SESSION_CHAIN_WARNING
    };
    let (edits, offset) = remap_edits(&snapshot.text, current_text, edits)?;
    // A remap that no longer applies is a failed recovery, not an error of
    // its own: the stale-tag rejection explains what happened.
    let applied = apply_edits(current_text, &edits, clipboard).ok()?;
    if applied.text == current_text {
        return None;
    }
    let mut warnings = vec![if offset == 0 {
        chain_warning.to_owned()
    } else {
        RECOVERY_LINE_REMAP_WARNING.to_owned()
    }];
    warnings.extend(applied.warnings);
    Some(ApplyResult {
        text: applied.text,
        first_changed_line: applied.first_changed_line,
        warnings,
    })
}
