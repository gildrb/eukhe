//! jsdiff-compatible line diff (port of omp `crates/edit/src/diff.rs`).
//!
//! The Myers O(ND) core keeps jsdiff v9's default tie-breaking and change
//! coalescing, so hashline diffs and stale-anchor remaps match omp line for
//! line.

// Myers positions are `isize` like jsdiff's, over token counts far below
// `isize::MAX`; run lengths and token ids fit `u32` because a text with more
// than `u32::MAX` lines cannot be held in memory.
#![allow(
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss
)]

use std::{collections::HashMap, rc::Rc};

/// A run of lines sharing one edit classification, in forward order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Run {
    /// Number of lines in this run.
    pub(crate) count: u32,
    /// The run exists only in the new text.
    pub(crate) added: bool,
    /// The run exists only in the old text.
    pub(crate) removed: bool,
}

/// One run joined back to its text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Change {
    /// Joined lines of this run (taken from the new text for common runs).
    pub(crate) value: String,
    /// The run exists only in the new text.
    pub(crate) added: bool,
    /// The run exists only in the old text.
    pub(crate) removed: bool,
}

struct Component {
    count: usize,
    added: bool,
    removed: bool,
    prev: Option<Rc<Self>>,
}

/// Frontier state for one diagonal: furthest old position reached plus the
/// component chain that got there.
struct PathState {
    old_pos: isize,
    last: Option<Rc<Component>>,
}

/// Extend `path` along its diagonal while tokens match, recording the common
/// run. Returns the new-token position (jsdiff `extractCommon`).
fn extract_common(path: &mut PathState, new: &[u32], old: &[u32], diagonal: isize) -> isize {
    let new_len = new.len() as isize;
    let old_len = old.len() as isize;
    let mut old_pos = path.old_pos;
    let mut new_pos = old_pos - diagonal;
    let mut common = 0usize;
    while new_pos + 1 < new_len
        && old_pos + 1 < old_len
        && old[(old_pos + 1) as usize] == new[(new_pos + 1) as usize]
    {
        new_pos += 1;
        old_pos += 1;
        common += 1;
    }
    if common > 0 {
        path.last = Some(Rc::new(Component {
            count: common,
            added: false,
            removed: false,
            prev: path.last.take(),
        }));
    }
    path.old_pos = old_pos;
    new_pos
}

/// Branch from `path` with one added or removed token (jsdiff `addToPath`,
/// which merges into the previous component when the edit kind repeats).
fn add_to_path(path: &PathState, added: bool, removed: bool, old_pos_inc: isize) -> PathState {
    match &path.last {
        Some(last) if last.added == added && last.removed == removed => PathState {
            old_pos: path.old_pos + old_pos_inc,
            last: Some(Rc::new(Component {
                count: last.count + 1,
                added,
                removed,
                prev: last.prev.clone(),
            })),
        },
        Some(_) | None => PathState {
            old_pos: path.old_pos + old_pos_inc,
            last: Some(Rc::new(Component {
                count: 1,
                added,
                removed,
                prev: path.last.clone(),
            })),
        },
    }
}

/// Convert the winning component chain into forward-ordered runs.
fn build_runs(last: Option<&Component>) -> Vec<Run> {
    let mut runs = Vec::new();
    let mut cursor = last;
    while let Some(component) = cursor {
        runs.push(Run {
            count: component.count as u32,
            added: component.added,
            removed: component.removed,
        });
        cursor = component.prev.as_deref();
    }
    runs.reverse();
    runs
}

/// Myers O(ND) diff over interned token ids, replicating jsdiff's default
/// execution path (no `oneChangePerToken`, timeout, or `maxEditLength`) so
/// the run structure is identical.
fn myers_diff(old: &[u32], new: &[u32]) -> Vec<Run> {
    let old_len = old.len() as isize;
    let new_len = new.len() as isize;
    let max_edit = old_len + new_len;
    let offset = max_edit + 1;
    let mut best: Vec<Option<PathState>> = Vec::new();
    best.resize_with((2 * max_edit + 3) as usize, || None);

    // Edit length 0: the content may start with common tokens.
    let mut seed = PathState {
        old_pos: -1,
        last: None,
    };
    let seed_new_pos = extract_common(&mut seed, new, old, 0);
    if seed.old_pos + 1 >= old_len && seed_new_pos + 1 >= new_len {
        return build_runs(seed.last.as_deref());
    }
    best[offset as usize] = Some(seed);

    let mut min_diagonal = isize::MIN;
    let mut max_diagonal = isize::MAX;
    let mut edit_length: isize = 1;
    while edit_length <= max_edit {
        let mut diagonal = min_diagonal.max(-edit_length);
        while diagonal <= max_diagonal.min(edit_length) {
            let idx = (diagonal + offset) as usize;
            let remove_path = best[idx - 1].take();
            let add_path_old_pos = best[idx + 1].as_ref().map(|path| path.old_pos);
            let can_add = add_path_old_pos.is_some_and(|old_pos| {
                let add_new_pos = old_pos - diagonal;
                add_new_pos >= 0 && add_new_pos < new_len
            });
            let can_remove = remove_path
                .as_ref()
                .is_some_and(|path| path.old_pos + 1 < old_len);
            if !can_add && !can_remove {
                best[idx] = None;
                diagonal += 2;
                continue;
            }
            // Branch from the prior path whose old-text position is furthest
            // along, preferring the insertion path on ties (jsdiff order).
            let prefer_add = !can_remove
                || (can_add
                    && remove_path.as_ref().is_some_and(|path| {
                        add_path_old_pos.is_some_and(|add_old| path.old_pos < add_old)
                    }));
            let mut base_path = if prefer_add {
                add_to_path(
                    best[idx + 1]
                        .as_ref()
                        .expect("can_add implies a live add path"),
                    true,
                    false,
                    0,
                )
            } else {
                add_to_path(
                    remove_path
                        .as_ref()
                        .expect("can_remove implies a live remove path"),
                    false,
                    true,
                    1,
                )
            };
            let new_pos = extract_common(&mut base_path, new, old, diagonal);
            if base_path.old_pos + 1 >= old_len && new_pos + 1 >= new_len {
                return build_runs(base_path.last.as_deref());
            }
            if base_path.old_pos + 1 >= old_len {
                max_diagonal = max_diagonal.min(diagonal - 1);
            }
            if new_pos + 1 >= new_len {
                min_diagonal = min_diagonal.max(diagonal + 1);
            }
            best[idx] = Some(base_path);
            diagonal += 2;
        }
        edit_length += 1;
    }
    unreachable!("Myers diff terminates within oldLen + newLen edits")
}

/// jsdiff line tokens: each line keeps its trailing `\n`.
fn line_tokens(text: &str) -> Vec<&str> {
    text.split_inclusive('\n').collect()
}

/// Intern tokens as dense ids under exact equality and diff them.
fn diff_tokens<'a>(old: &[&'a str], new: &[&'a str]) -> Vec<Run> {
    let mut ids: HashMap<&'a str, u32> = HashMap::with_capacity(old.len() + new.len());
    let mut assign = |token: &'a str| -> u32 {
        let next = ids.len() as u32;
        *ids.entry(token).or_insert(next)
    };
    let old_ids: Vec<u32> = old.iter().map(|token| assign(token)).collect();
    let new_ids: Vec<u32> = new.iter().map(|token| assign(token)).collect();
    myers_diff(&old_ids, &new_ids)
}

/// Myers runs over jsdiff line tokens.
pub(crate) fn line_runs(old: &str, new: &str) -> Vec<Run> {
    diff_tokens(&line_tokens(old), &line_tokens(new))
}

/// Line changes with jsdiff `diffLines` semantics.
pub(crate) fn line_changes(old: &str, new: &str) -> Vec<Change> {
    let old_tokens = line_tokens(old);
    let new_tokens = line_tokens(new);
    let runs = diff_tokens(&old_tokens, &new_tokens);
    let mut old_pos = 0usize;
    let mut new_pos = 0usize;
    runs.iter()
        .map(|run| {
            let count = run.count as usize;
            let value = if run.removed {
                let value = old_tokens[old_pos..old_pos + count].concat();
                old_pos += count;
                value
            } else {
                let value = new_tokens[new_pos..new_pos + count].concat();
                new_pos += count;
                if !run.added {
                    old_pos += count;
                }
                value
            };
            Change {
                value,
                added: run.added,
                removed: run.removed,
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lines(old: &str, new: &str) -> Vec<(String, bool, bool)> {
        line_changes(old, new)
            .into_iter()
            .map(|change| (change.value, change.added, change.removed))
            .collect()
    }

    #[test]
    fn line_diff_replaces_middle_line() {
        assert_eq!(
            lines("a\nb\nc\n", "a\nx\nc\n"),
            vec![
                ("a\n".into(), false, false),
                ("b\n".into(), false, true),
                ("x\n".into(), true, false),
                ("c\n".into(), false, false),
            ]
        );
    }

    #[test]
    fn line_diff_treats_missing_trailing_newline_as_distinct() {
        assert_eq!(
            lines("a\nb", "a\nb\n"),
            vec![
                ("a\n".into(), false, false),
                ("b".into(), false, true),
                ("b\n".into(), true, false),
            ]
        );
    }

    #[test]
    fn line_runs_preserve_empty_lines() {
        let shaped: Vec<(u32, bool, bool)> = line_runs("a\n\nb", "a\n\nc")
            .into_iter()
            .map(|run| (run.count, run.added, run.removed))
            .collect();
        assert_eq!(
            shaped,
            vec![(2, false, false), (1, false, true), (1, true, false)]
        );
    }
}
