//! Applying parsed edits to text (omp `modes/hashline/apply.rs`).
//!
//! omp also repairs replacement boundaries and opener landings with a
//! tree-sitter parse probe. Without grammars that probe never parses, which
//! makes those repairs no-ops in omp too; they are not ported (tool-surface
//! design, Phase 5).

use std::{
    collections::{BTreeMap, HashSet},
    sync::LazyLock,
};

use regex::Regex;

use super::{
    clipboard::resolve_clipboard_edits,
    messages::{
        after_insert_landing_shift_warning, ambiguous_boundary_echo_message,
        textual_boundary_echo_warning, BoundarySide, REPLACEMENT_INDENT_AUTO_SHIFT_WARNING,
        UNRESOLVED_BLOCK_INTERNAL, UNRESOLVED_CLIPBOARD_INTERNAL,
    },
    types::{Anchor, ApplyResult, Cursor, Edit},
};
use crate::{error::EditError, store::Clipboard};

/// A line containing only closing delimiters and an optional trailing
/// separator.
pub(crate) static STRUCTURAL_CLOSER_RE: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"^\s*[)\]}]+[;,]?\s*$").expect("valid structural-closer regex"));

fn anchor(edit: &Edit) -> Option<Anchor> {
    match edit {
        Edit::Delete { anchor, .. }
        | Edit::Insert {
            cursor: Cursor::BeforeAnchor(anchor) | Cursor::AfterAnchor(anchor),
            ..
        } => Some(*anchor),
        Edit::Insert {
            cursor: Cursor::Bof | Cursor::Eof,
            ..
        }
        | Edit::Cut { .. }
        | Edit::Paste { .. }
        | Edit::Block { .. } => None,
    }
}

fn with_index(edit: &Edit, index: u32) -> Edit {
    let mut edit = edit.clone();
    match &mut edit {
        Edit::Insert { index: slot, .. } | Edit::Delete { index: slot, .. } => *slot = index,
        Edit::Cut { .. } | Edit::Paste { .. } | Edit::Block { .. } => {}
    }
    edit
}

fn phantom_line(lines: &[String]) -> Option<u32> {
    (lines.len() > 1 && lines.last().is_some_and(String::is_empty)).then_some(lines.len() as u32)
}

fn validate_bounds(edits: &[Edit], lines: &[String]) -> Result<(), EditError> {
    for edit in edits {
        if let Some(anchor) = anchor(edit) {
            if anchor.line < 1 || anchor.line as usize > lines.len() {
                return Err(EditError::apply(format!(
                    "Line {} does not exist (file has {} lines)",
                    anchor.line,
                    lines.len()
                )));
            }
        }
    }
    Ok(())
}

#[derive(Clone)]
struct ReplacementGroup {
    insert_indices: Vec<usize>,
    delete_indices: Vec<usize>,
    payload: Vec<String>,
    start: u32,
    end: u32,
}

fn replacement_group(edits: &[Edit], start: usize) -> Option<ReplacementGroup> {
    let Edit::Insert {
        cursor: Cursor::BeforeAnchor(anchor),
        line_num,
        replacement: true,
        ..
    } = edits.get(start)?
    else {
        return None;
    };
    let anchor_line = anchor.line;
    let op_line = *line_num;
    let mut insert_indices = Vec::new();
    let mut payload = Vec::new();
    let mut i = start;
    while let Some(Edit::Insert {
        cursor: Cursor::BeforeAnchor(anchor),
        text,
        line_num,
        replacement: true,
        ..
    }) = edits.get(i)
    {
        if anchor.line != anchor_line || *line_num != op_line {
            break;
        }
        insert_indices.push(i);
        payload.push(text.clone());
        i += 1;
    }
    let mut delete_indices = Vec::new();
    let mut expected = anchor_line;
    while let Some(Edit::Delete {
        anchor, line_num, ..
    }) = edits.get(i)
    {
        if anchor.line != expected || *line_num != op_line {
            break;
        }
        delete_indices.push(i);
        expected += 1;
        i += 1;
    }
    if delete_indices.is_empty() {
        return None;
    }
    Some(ReplacementGroup {
        insert_indices,
        delete_indices,
        payload,
        start: anchor_line,
        end: expected - 1,
    })
}

fn leading_indent(line: &str) -> &str {
    let end = line
        .bytes()
        .take_while(|byte| matches!(byte, b' ' | b'\t'))
        .count();
    &line[..end]
}
fn indent_deeper(deeper: &str, shallower: &str) -> bool {
    deeper.len() > shallower.len() && deeper.starts_with(shallower)
}
fn has_content(text: &str) -> bool {
    text.bytes().any(|byte| !matches!(byte, 9..=13 | 32))
}

fn repair_indentation(edits: &mut [Edit], lines: &[String]) -> Vec<String> {
    let mut repaired = false;
    let mut start = 0;
    while start < edits.len() {
        let Some(group) = replacement_group(edits, start) else {
            start += 1;
            continue;
        };
        start = group.delete_indices.last().copied().unwrap_or(start) + 1;
        if group.payload.len() != group.delete_indices.len() {
            continue;
        }
        let preceding = lines
            .get(group.start.saturating_sub(2) as usize)
            .map_or("", String::as_str);
        let source_first = lines
            .get((group.start - 1) as usize)
            .map_or("", String::as_str);
        let payload_first = group.payload.first().map_or("", String::as_str);
        if !preceding.trim_end().ends_with('{')
            || !indent_deeper(leading_indent(source_first), leading_indent(preceding))
            || indent_deeper(leading_indent(payload_first), leading_indent(preceding))
        {
            continue;
        }
        let mut shift: Option<&str> = None;
        let mut matches = 0;
        let mut consistent = true;
        for (offset, payload) in group.payload.iter().enumerate() {
            let source = lines
                .get((group.start - 1) as usize + offset)
                .map_or("", String::as_str);
            if source.trim().is_empty() || source.trim_start() != payload.trim_start() {
                continue;
            }
            let source_indent = leading_indent(source);
            let payload_indent = leading_indent(payload);
            if !source_indent.ends_with(payload_indent) {
                consistent = false;
                break;
            }
            let candidate = &source_indent[..source_indent.len() - payload_indent.len()];
            if shift.is_some_and(|old| old != candidate) {
                consistent = false;
                break;
            }
            shift = Some(candidate);
            matches += 1;
        }
        let Some(shift) = shift else { continue };
        if !consistent || shift.is_empty() || matches < 2 || matches * 2 <= group.payload.len() {
            continue;
        }
        for &index in &group.insert_indices {
            if let Edit::Insert { text, .. } = &mut edits[index] {
                if !text.trim().is_empty() {
                    text.insert_str(0, shift);
                }
            }
        }
        repaired = true;
    }
    if repaired {
        vec![REPLACEMENT_INDENT_AUTO_SHIFT_WARNING.to_owned()]
    } else {
        Vec::new()
    }
}

fn duplicate_leading(group: &ReplacementGroup, lines: &[String]) -> usize {
    let max = group
        .payload
        .len()
        .min(group.start.saturating_sub(1) as usize);
    for count in (1..=max).rev() {
        let source_start = group.start as usize - 1 - count;
        let candidate = &group.payload[..count];
        if candidate
            .iter()
            .zip(&lines[source_start..source_start + count])
            .all(|(a, b)| a == b)
            && candidate.iter().any(|line| has_content(line))
        {
            return count;
        }
    }
    0
}
fn duplicate_trailing(group: &ReplacementGroup, lines: &[String]) -> usize {
    let max = group
        .payload
        .len()
        .min(lines.len().saturating_sub(group.end as usize));
    for count in (1..=max).rev() {
        let payload = &group.payload[group.payload.len() - count..];
        let source = &lines[group.end as usize..group.end as usize + count];
        if payload.iter().zip(source).all(|(a, b)| a == b)
            && payload.iter().any(|line| has_content(line))
        {
            return count;
        }
    }
    0
}
#[derive(Clone, Copy)]
struct Ambiguity {
    start: u32,
    end: u32,
    side: BoundarySide,
    count: u32,
}

fn normalize_echoes(edits: &[Edit], lines: &[String]) -> (Vec<Edit>, Vec<String>, Vec<Ambiguity>) {
    let mut out = Vec::new();
    let mut warnings = Vec::new();
    let mut ambiguities = Vec::new();
    let mut i = 0;
    while i < edits.len() {
        let Some(group) = replacement_group(edits, i) else {
            out.push(with_index(&edits[i], i as u32));
            i += 1;
            continue;
        };
        let leading = duplicate_leading(&group, lines);
        let trailing = duplicate_trailing(&group, lines);
        let range_len = group.delete_indices.len();
        let (mut drop_l, mut drop_t) = (0, 0);
        if leading > 0 && trailing > 0 {
            if group.payload.len().saturating_sub(leading + trailing) == range_len {
                drop_l = leading;
                drop_t = trailing;
            }
        } else if leading > 0 && range_len > 1 {
            if group.payload.len().saturating_sub(leading) >= range_len {
                drop_l = leading;
            } else {
                ambiguities.push(Ambiguity {
                    start: group.start,
                    end: group.end,
                    side: BoundarySide::Leading,
                    count: leading as u32,
                });
            }
        } else if trailing > 0 && range_len > 1 {
            if group.payload.len().saturating_sub(trailing) >= range_len {
                drop_t = trailing;
            } else {
                ambiguities.push(Ambiguity {
                    start: group.start,
                    end: group.end,
                    side: BoundarySide::Trailing,
                    count: trailing as u32,
                });
            }
        }
        if drop_l > 0 || drop_t > 0 {
            let kept = &group.insert_indices[drop_l..group.insert_indices.len() - drop_t];
            out.extend(kept.iter().map(|&index| edits[index].clone()));
            out.extend(
                group
                    .delete_indices
                    .iter()
                    .map(|&index| edits[index].clone()),
            );
            warnings.push(textual_boundary_echo_warning(
                group.start,
                drop_l as u32,
                drop_t as u32,
            ));
        } else {
            out.extend(
                group
                    .insert_indices
                    .iter()
                    .chain(&group.delete_indices)
                    .map(|&idx| with_index(&edits[idx], idx as u32)),
            );
        }
        i = group
            .delete_indices
            .last()
            .copied()
            .expect("a replacement group has deletes")
            + 1;
    }
    (out, warnings, ambiguities)
}

#[derive(Clone)]
struct InsertGroup {
    anchor: u32,
    members: Vec<usize>,
}
fn body_indent(rows: &[&str]) -> Option<String> {
    let non_blank: Vec<_> = rows
        .iter()
        .copied()
        .filter(|row| has_content(row))
        .collect();
    if non_blank.is_empty()
        || non_blank
            .iter()
            .all(|row| STRUCTURAL_CLOSER_RE.is_match(row))
    {
        return None;
    }
    let mut target = leading_indent(non_blank[0]).to_owned();
    for row in non_blank {
        let indent = leading_indent(row);
        if indent.starts_with(&target) {
        } else if target.starts_with(indent) {
            indent.clone_into(&mut target);
        } else {
            return None;
        }
    }
    Some(target)
}
/// Slide a `PUT >N:` body indented shallower than its anchor past the
/// closing lines that follow, so it lands at its own depth.
fn repair_landings(edits: &[Edit], lines: &[String]) -> (Vec<Edit>, Vec<String>) {
    let mut groups: Vec<((u32, u32), InsertGroup)> = Vec::new();
    for (index, edit) in edits.iter().enumerate() {
        if let Edit::Insert {
            cursor: Cursor::AfterAnchor(anchor),
            line_num,
            replacement: false,
            ..
        } = edit
        {
            let key = (anchor.line, *line_num);
            if let Some((_, group)) = groups.iter_mut().find(|(candidate, _)| *candidate == key) {
                group.members.push(index);
            } else {
                groups.push((
                    key,
                    InsertGroup {
                        anchor: anchor.line,
                        members: vec![index],
                    },
                ));
            }
        }
    }
    let targeted: HashSet<u32> = edits
        .iter()
        .filter_map(anchor)
        .map(|anchor| anchor.line)
        .collect();
    let mut out = edits.to_vec();
    let mut warnings = Vec::new();
    for (_, group) in &groups {
        let rows: Vec<_> = group
            .members
            .iter()
            .filter_map(|&index| {
                if let Edit::Insert { text, .. } = &edits[index] {
                    Some(text.as_str())
                } else {
                    None
                }
            })
            .collect();
        let Some(target) = body_indent(&rows) else {
            continue;
        };
        let anchor_text = lines
            .get((group.anchor - 1) as usize)
            .map_or("", String::as_str);
        let mut outward = None;
        if has_content(anchor_text) && indent_deeper(leading_indent(anchor_text), &target) {
            let mut landing = group.anchor;
            let mut crossed = 0;
            let mut blocked = false;
            for line in group.anchor + 1..=lines.len() as u32 {
                let text = &lines[(line - 1) as usize];
                if !has_content(text) {
                    continue;
                }
                if !STRUCTURAL_CLOSER_RE.is_match(text)
                    || !leading_indent(text).starts_with(&target)
                {
                    break;
                }
                if targeted.contains(&line) {
                    blocked = true;
                    break;
                }
                landing = line;
                crossed += 1;
                if leading_indent(text).len() == target.len() {
                    break;
                }
            }
            if !blocked && landing != group.anchor {
                outward = Some((landing, crossed));
            }
        }
        if let Some((landing, crossed)) = outward {
            for &index in &group.members {
                if let Edit::Insert { cursor, .. } = &mut out[index] {
                    *cursor = Cursor::AfterAnchor(Anchor { line: landing });
                }
            }
            warnings.push(after_insert_landing_shift_warning(
                group.anchor,
                landing,
                crossed,
            ));
        }
    }
    (out, warnings)
}

fn materialize(original: &[String], edits: &[Edit]) -> (String, Option<u32>) {
    let mut lines = original.to_vec();
    let mut first = None;
    let mut bof = Vec::new();
    let mut eof = Vec::new();
    let mut buckets: BTreeMap<u32, Vec<(usize, Edit)>> = BTreeMap::new();
    for (index, edit) in edits.iter().enumerate() {
        match edit {
            Edit::Insert {
                cursor: Cursor::Bof,
                text,
                ..
            } => bof.push(text.clone()),
            Edit::Insert {
                cursor: Cursor::Eof,
                text,
                ..
            } => eof.push(text.clone()),
            Edit::Insert {
                cursor: Cursor::BeforeAnchor(anchor) | Cursor::AfterAnchor(anchor),
                ..
            }
            | Edit::Delete { anchor, .. } => buckets
                .entry(anchor.line)
                .or_default()
                .push((index, edit.clone())),
            Edit::Cut { .. } | Edit::Paste { .. } | Edit::Block { .. } => {}
        }
    }
    for (line, mut bucket) in buckets.into_iter().rev() {
        bucket.sort_by_key(|(index, _)| *index);
        let index = (line - 1) as usize;
        let current = lines.get(index).cloned().unwrap_or_default();
        let mut before = Vec::new();
        let mut replacements = Vec::new();
        let mut after = Vec::new();
        let mut delete = false;
        for (_, edit) in bucket {
            match edit {
                Edit::Insert {
                    cursor: Cursor::AfterAnchor(_),
                    text,
                    ..
                } => after.push(text),
                Edit::Insert {
                    text,
                    replacement: true,
                    ..
                } => replacements.push(text),
                Edit::Insert { text, .. } => before.push(text),
                Edit::Delete { .. } => delete = true,
                Edit::Cut { .. } | Edit::Paste { .. } | Edit::Block { .. } => {}
            }
        }
        if before.is_empty() && replacements.is_empty() && after.is_empty() && !delete {
            continue;
        }
        let mut replacement = before;
        replacement.extend(replacements);
        if !delete {
            replacement.push(current);
        }
        replacement.extend(after);
        lines.splice(index..=index, replacement);
        first = Some(first.map_or(line, |old: u32| old.min(line)));
    }
    if !bof.is_empty() {
        if lines.len() == 1 && lines[0].is_empty() {
            lines = bof;
        } else {
            lines.splice(0..0, bof);
        }
        first = Some(1);
    }
    if !eof.is_empty() {
        let at = if lines.len() == 1 && lines[0].is_empty() {
            lines = eof;
            1
        } else {
            let index = if lines.last().is_some_and(String::is_empty) {
                lines.len() - 1
            } else {
                lines.len()
            };
            lines.splice(index..index, eof);
            index + 1
        };
        first = Some(first.map_or(at as u32, |old| old.min(at as u32)));
    }
    (lines.join("\n"), first)
}

/// Apply parsed edits to LF-normalized text. Clipboard ops read and write
/// `clipboard`; block ops must already be resolved.
pub(crate) fn apply_edits(
    text: &str,
    edits: &[Edit],
    clipboard: &mut Clipboard,
) -> Result<ApplyResult, EditError> {
    if edits.is_empty() {
        return Ok(ApplyResult {
            text: text.to_owned(),
            ..ApplyResult::default()
        });
    }
    let lines: Vec<String> = text.split('\n').map(str::to_owned).collect();
    let mut warnings = Vec::new();
    let concrete = resolve_clipboard_edits(edits, &lines, clipboard, &mut |warning| {
        warnings.push(warning);
    })?;
    let mut target = Vec::new();
    for edit in concrete {
        match edit {
            Edit::Block { .. } => return Err(EditError::apply(UNRESOLVED_BLOCK_INTERNAL)),
            Edit::Cut { .. } | Edit::Paste { .. } => {
                return Err(EditError::apply(UNRESOLVED_CLIPBOARD_INTERNAL));
            }
            Edit::Insert { .. } | Edit::Delete { .. } => target.push(edit),
        }
    }
    if let Some(phantom) = phantom_line(&lines) {
        target
            .retain(|edit| !matches!(edit, Edit::Delete { anchor, .. } if anchor.line == phantom));
    }
    let mut target: Vec<Edit> = target
        .iter()
        .enumerate()
        .map(|(index, edit)| with_index(edit, index as u32))
        .collect();
    validate_bounds(&target, &lines)?;
    warnings.extend(repair_indentation(&mut target, &lines));
    let (landed, landing_warnings) = repair_landings(&target, &lines);
    warnings.extend(landing_warnings);
    let (normalized, echo_warnings, ambiguities) = normalize_echoes(&landed, &lines);
    warnings.extend(echo_warnings);
    if let Some(ambiguity) = ambiguities.first() {
        return Err(EditError::apply(ambiguous_boundary_echo_message(
            ambiguity.start,
            ambiguity.end,
            ambiguity.side,
            ambiguity.count,
        )));
    }
    let (text, first_changed_line) = materialize(&lines, &normalized);
    Ok(ApplyResult {
        text,
        first_changed_line,
        warnings,
    })
}
