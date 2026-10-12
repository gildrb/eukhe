//! Model-facing numbered diff and its compact preview (port of omp
//! `crates/edit/src/diff_string.rs`).
//!
//! `generate_diff_string` renders `+N|new`, `-N|old`, and ` N|context` rows
//! with two lines of context and the off-window lines of brackets the visible
//! rows open or close. `build_compact_diff_preview` turns those rows into the
//! `N:TEXT` preview of the edited file shown in edit results.

// Line numbers are `u32` like omp's; a text with more than `u32::MAX` lines
// cannot be held in memory.
#![allow(clippy::cast_possible_truncation)]

use std::collections::{BTreeMap, BTreeSet};

const DIFF_GAP_ROW: &str = "";
const DIFF_CONTEXT_LINES: usize = 2;
const ADDED_RUN_CONTEXT_LINES: usize = 2;
const PREVIEW_ELISION_MARKER: &str = "…";
const PREVIEW_GAP_ROW: &str = "";

/// Rendered diff plus the 1-indexed first changed line in the new text.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct DiffOutput {
    /// Numbered diff rows.
    pub(crate) diff: String,
    /// First line affected in the new text.
    pub(crate) first_changed_line: Option<u32>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum DiffPrefix {
    Added,
    Removed,
    Context,
}

#[derive(Debug)]
struct ParsedNumberedDiffRow {
    prefix: DiffPrefix,
    line_number: u32,
}

fn format_numbered_diff_line(prefix: char, line_number: u32, content: &str) -> String {
    format!("{prefix}{line_number}|{content}")
}

fn parse_numbered_diff_row(row: &str) -> Option<ParsedNumberedDiffRow> {
    let (prefix, body) = match row.as_bytes().first().copied()? {
        b'+' => (DiffPrefix::Added, &row[1..]),
        b'-' => (DiffPrefix::Removed, &row[1..]),
        b' ' => (DiffPrefix::Context, &row[1..]),
        _ => return None,
    };
    let separator = body.find('|')?;
    let line_number = body[..separator].parse().ok()?;
    Some(ParsedNumberedDiffRow {
        prefix,
        line_number,
    })
}

fn is_diff_change_row(row: Option<&String>) -> bool {
    row.is_some_and(|value| value.starts_with('+') || value.starts_with('-'))
}

fn parse_source_row_line_number(row: &str) -> Option<u32> {
    let parsed = parse_numbered_diff_row(row)?;
    (parsed.prefix != DiffPrefix::Added).then_some(parsed.line_number)
}

fn normalize_diff_gap_rows(rows: &mut Vec<String>) {
    let mut kept = Vec::with_capacity(rows.len());
    for (index, row) in rows.iter().enumerate() {
        if row != DIFF_GAP_ROW {
            kept.push(row.clone());
            continue;
        }
        if kept.is_empty() || kept.last().is_some_and(String::is_empty) {
            continue;
        }
        let before = kept
            .iter()
            .rev()
            .find_map(|candidate| parse_source_row_line_number(candidate));
        let after = rows[index + 1..]
            .iter()
            .filter(|candidate| !candidate.is_empty())
            .find_map(|candidate| parse_source_row_line_number(candidate));
        if matches!((before, after), (Some(left), Some(right)) if right > left + 1) {
            kept.push(String::new());
        }
    }
    *rows = kept;
}

fn adjusted_context_insert_index(rows: &[String], index: usize) -> usize {
    let mut start = index;
    while start > 0 && is_diff_change_row(rows.get(start - 1)) {
        start -= 1;
    }
    let mut end = index;
    while end < rows.len() && is_diff_change_row(rows.get(end)) {
        end += 1;
    }
    if index > start && index < end {
        end
    } else {
        index
    }
}

fn insert_bracket_context_rows(
    rows: &mut Vec<String>,
    context_lines: Vec<(u32, String)>,
    seen_rows: &mut BTreeSet<String>,
) {
    for (line_number, text) in context_lines {
        let row = format_numbered_diff_line(' ', line_number, &text);
        if seen_rows.contains(&row) {
            continue;
        }

        let mut insert_index = rows.len();
        let mut previous_source_line = None;
        let mut next_source_line = None;
        for (index, candidate) in rows.iter().enumerate() {
            let Some(parsed) = parse_numbered_diff_row(candidate) else {
                continue;
            };
            if parsed.prefix == DiffPrefix::Added {
                continue;
            }
            if parsed.line_number < line_number {
                previous_source_line = Some(parsed.line_number);
                continue;
            }
            next_source_line = Some(parsed.line_number);
            insert_index = index;
            break;
        }

        let mut chunk = Vec::with_capacity(3);
        if previous_source_line.is_some_and(|previous| line_number > previous + 1) {
            chunk.push(String::new());
        }
        chunk.push(row.clone());
        if next_source_line.is_some_and(|next| next > line_number + 1) {
            chunk.push(String::new());
        }

        let insert_index = adjusted_context_insert_index(rows, insert_index);
        rows.splice(insert_index..insert_index, chunk);
        seen_rows.insert(row);
    }
}

fn add_matching_bracket_context_rows(
    rows: &mut Vec<String>,
    old_lines: &[&str],
    new_lines: &[&str],
) {
    let mut old_visible = Vec::new();
    let mut new_visible = Vec::new();
    let mut seen_rows = rows.iter().cloned().collect::<BTreeSet<_>>();
    let mut changes: Vec<(i64, i64)> = Vec::new();
    let mut offset = 0_i64;

    for row in rows.iter() {
        let Some(parsed) = parse_numbered_diff_row(row) else {
            continue;
        };
        match parsed.prefix {
            DiffPrefix::Removed => {
                old_visible.push(parsed.line_number);
                changes.push((i64::from(parsed.line_number) + offset, -1));
                offset -= 1;
            }
            DiffPrefix::Added => {
                new_visible.push(parsed.line_number);
                changes.push((i64::from(parsed.line_number), 1));
                offset += 1;
            }
            DiffPrefix::Context => {
                old_visible.push(parsed.line_number);
                let shifted = i64::from(parsed.line_number) + offset;
                if let Ok(line) = u32::try_from(shifted) {
                    new_visible.push(line);
                }
            }
        }
    }

    let to_old_line_number = |new_line_number: u32| {
        let new_line_number = i64::from(new_line_number);
        let shift: i64 = changes
            .iter()
            .filter(|(new_position, _)| *new_position <= new_line_number)
            .map(|(_, delta)| delta)
            .sum();
        u32::try_from(new_line_number - shift).ok()
    };

    let mut context_rows = find_block_context_lines(old_lines, &old_visible)
        .into_iter()
        .collect::<BTreeMap<_, _>>();
    for (line_number, text) in find_block_context_lines(new_lines, &new_visible) {
        if let Some(old_line_number) = to_old_line_number(line_number) {
            context_rows.entry(old_line_number).or_insert(text);
        }
    }
    insert_bracket_context_rows(rows, context_rows.into_iter().collect(), &mut seen_rows);
    normalize_diff_gap_rows(rows);
}

/// Generate a numbered diff with nearby and enclosing-block context.
pub(crate) fn generate_diff_string(old: &str, new: &str) -> DiffOutput {
    let parts = crate::diff::line_changes(old, new);
    let context_lines = DIFF_CONTEXT_LINES;
    let mut output = Vec::new();
    let mut old_line_number = 1_u32;
    let mut new_line_number = 1_u32;
    let mut last_was_change = false;
    let mut first_changed_line = None;

    for (index, part) in parts.iter().enumerate() {
        let mut raw = part.value.split('\n').collect::<Vec<_>>();
        if raw.last() == Some(&"") {
            raw.pop();
        }

        if part.added || part.removed {
            first_changed_line.get_or_insert(new_line_number);
            for line in raw {
                if part.added {
                    output.push(format_numbered_diff_line('+', new_line_number, line));
                    new_line_number += 1;
                } else {
                    output.push(format_numbered_diff_line('-', old_line_number, line));
                    old_line_number += 1;
                }
            }
            last_was_change = true;
        } else {
            let next_part_is_change = parts
                .get(index + 1)
                .is_some_and(|next| next.added || next.removed);
            if last_was_change || next_part_is_change {
                let mut leading_skip = 0;
                let mut middle_skip = 0;
                let mut trailing_skip = 0;
                let lines_to_show;

                if last_was_change && next_part_is_change {
                    if raw.len() > context_lines * 2 {
                        middle_skip = raw.len() - context_lines * 2;
                        lines_to_show = raw[..context_lines]
                            .iter()
                            .chain(&raw[raw.len() - context_lines..])
                            .copied()
                            .collect::<Vec<_>>();
                    } else {
                        lines_to_show = raw.clone();
                    }
                } else if next_part_is_change {
                    leading_skip = raw.len().saturating_sub(context_lines);
                    lines_to_show = raw[leading_skip..].to_vec();
                } else {
                    trailing_skip = raw.len().saturating_sub(context_lines);
                    lines_to_show = raw[..raw.len().min(context_lines)].to_vec();
                }

                old_line_number += u32::try_from(leading_skip).unwrap_or(u32::MAX);
                new_line_number += u32::try_from(leading_skip).unwrap_or(u32::MAX);
                let first_chunk_length = if middle_skip > 0 {
                    context_lines
                } else {
                    lines_to_show.len()
                };
                for line in &lines_to_show[..first_chunk_length] {
                    output.push(format_numbered_diff_line(' ', old_line_number, line));
                    old_line_number += 1;
                    new_line_number += 1;
                }
                if middle_skip > 0 {
                    old_line_number += u32::try_from(middle_skip).unwrap_or(u32::MAX);
                    new_line_number += u32::try_from(middle_skip).unwrap_or(u32::MAX);
                    for line in &lines_to_show[first_chunk_length..] {
                        output.push(format_numbered_diff_line(' ', old_line_number, line));
                        old_line_number += 1;
                        new_line_number += 1;
                    }
                }
                old_line_number += u32::try_from(trailing_skip).unwrap_or(u32::MAX);
                new_line_number += u32::try_from(trailing_skip).unwrap_or(u32::MAX);
            } else {
                let skipped = u32::try_from(raw.len()).unwrap_or(u32::MAX);
                old_line_number += skipped;
                new_line_number += skipped;
            }
            last_was_change = false;
        }
    }

    let old_lines = old.split('\n').collect::<Vec<_>>();
    let new_lines = new.split('\n').collect::<Vec<_>>();
    add_matching_bracket_context_rows(&mut output, &old_lines, &new_lines);
    DiffOutput {
        diff: output.join("\n"),
        first_changed_line,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ScannerMode {
    Code,
    Single,
    Double,
    Template,
    BlockComment,
}

#[derive(Debug)]
struct StackEntry {
    opener: char,
    line_number: u32,
    text: String,
    visible: bool,
}

fn is_hash_comment_start(line: &str, byte_index: usize) -> bool {
    line.as_bytes().get(byte_index) == Some(&b'#')
        && line.as_bytes()[..byte_index]
            .iter()
            .all(|byte| matches!(byte, b' ' | b'\t'))
}

/// Off-window lines holding the bracket that opens or closes a visible one.
///
/// omp asks tree-sitter first and falls back to this lexical scan for files
/// without a grammar; eukhe has no grammars yet, so the scan is the whole
/// behavior.
#[allow(
    clippy::too_many_lines,
    reason = "one lexical scanner state machine, ported as one function from omp"
)]
fn find_block_context_lines(full_lines: &[&str], visible: &[u32]) -> Vec<(u32, String)> {
    let visible = visible.iter().copied().collect::<BTreeSet<_>>();
    if visible.is_empty() || (!full_lines.is_empty() && visible.len() >= full_lines.len()) {
        return Vec::new();
    }
    let mut context = BTreeMap::new();
    let mut stack: Vec<StackEntry> = Vec::new();
    let mut mode = ScannerMode::Code;
    let mut escaped = false;

    for (line_index, &line) in full_lines.iter().enumerate() {
        let line_number = u32::try_from(line_index + 1).unwrap_or(u32::MAX);
        let line_visible = visible.contains(&line_number);
        let mut chars = line.char_indices().peekable();
        while let Some((byte_index, character)) = chars.next() {
            let next = chars.peek().map(|(_, value)| *value);
            if mode == ScannerMode::BlockComment {
                if character == '*' && next == Some('/') {
                    mode = ScannerMode::Code;
                    chars.next();
                }
                continue;
            }
            if matches!(
                mode,
                ScannerMode::Single | ScannerMode::Double | ScannerMode::Template
            ) {
                if escaped {
                    escaped = false;
                    continue;
                }
                if character == '\\' {
                    escaped = true;
                    continue;
                }
                if (mode == ScannerMode::Single && character == '\'')
                    || (mode == ScannerMode::Double && character == '"')
                    || (mode == ScannerMode::Template && character == '`')
                {
                    mode = ScannerMode::Code;
                }
                continue;
            }
            if character == '/' && next == Some('/') {
                break;
            }
            if character == '/' && next == Some('*') {
                mode = ScannerMode::BlockComment;
                chars.next();
                continue;
            }
            if character == '#' && is_hash_comment_start(line, byte_index) {
                break;
            }
            if character == '\'' {
                mode = ScannerMode::Single;
                escaped = false;
                continue;
            }
            if character == '"' {
                mode = ScannerMode::Double;
                escaped = false;
                continue;
            }
            if character == '`' {
                mode = ScannerMode::Template;
                escaped = false;
                continue;
            }
            if matches!(character, '(' | '[' | '{') {
                stack.push(StackEntry {
                    opener: character,
                    line_number,
                    text: line.to_owned(),
                    visible: line_visible,
                });
                continue;
            }
            let opener = match character {
                ')' => Some('('),
                ']' => Some('['),
                '}' => Some('{'),
                _ => None,
            };
            let matched_index =
                opener.and_then(|opener| stack.iter().rposition(|entry| entry.opener == opener));
            if let Some(match_index) = matched_index {
                let matched = stack.remove(match_index);
                stack.truncate(match_index);
                if line_visible && !matched.visible {
                    context.insert(matched.line_number, matched.text);
                }
                if matched.visible && !line_visible {
                    context.insert(line_number, line.to_owned());
                }
            }
        }
        if matches!(mode, ScannerMode::Single | ScannerMode::Double) {
            mode = ScannerMode::Code;
            escaped = false;
        }
    }
    for line_number in &visible {
        context.remove(line_number);
    }
    context.into_iter().collect()
}

fn is_preview_separator(line: &str) -> bool {
    line == PREVIEW_ELISION_MARKER || line == PREVIEW_GAP_ROW
}

fn append_preview_line(output: &mut Vec<String>, line: &str) {
    let normalized = if matches!(line, "..." | PREVIEW_ELISION_MARKER | "+…") {
        PREVIEW_ELISION_MARKER
    } else {
        line
    };
    if is_preview_separator(normalized)
        && (output.is_empty() || output.last().is_some_and(|last| is_preview_separator(last)))
    {
        return;
    }
    output.push(normalized.to_owned());
}

#[derive(Debug)]
struct ParsedCompactDiffLine<'a> {
    kind: DiffPrefix,
    line_number: i64,
    content: &'a str,
}

fn parse_integer_prefix(value: &str) -> Option<i64> {
    let value = value.trim_start();
    let (negative, digits) = if let Some(rest) = value.strip_prefix('-') {
        (true, rest)
    } else if let Some(rest) = value.strip_prefix('+') {
        (false, rest)
    } else {
        (false, value)
    };
    let digit_count = digits.bytes().take_while(u8::is_ascii_digit).count();
    if digit_count == 0 {
        return None;
    }
    let magnitude = digits[..digit_count].parse::<i64>().ok()?;
    if negative {
        magnitude.checked_neg()
    } else {
        Some(magnitude)
    }
}

fn parse_compact_diff_line(line: &str) -> Option<ParsedCompactDiffLine<'_>> {
    let (kind, body) = match line.as_bytes().first().copied()? {
        b'+' => (DiffPrefix::Added, &line[1..]),
        b'-' => (DiffPrefix::Removed, &line[1..]),
        b' ' => (DiffPrefix::Context, &line[1..]),
        _ => return None,
    };
    let separator = body.find('|')?;
    let line_number = parse_integer_prefix(&body[..separator])?;
    Some(ParsedCompactDiffLine {
        kind,
        line_number,
        content: &body[separator + 1..],
    })
}

fn append_added_run(output: &mut Vec<String>, run: &[String], edge_lines: usize) {
    if run.is_empty() {
        return;
    }
    let collapse_threshold = edge_lines * 2 + 1;
    if run.len() <= collapse_threshold {
        for line in run {
            append_preview_line(output, line);
        }
        return;
    }
    for line in &run[..edge_lines] {
        append_preview_line(output, line);
    }
    append_preview_line(output, PREVIEW_ELISION_MARKER);
    for line in &run[run.len() - edge_lines..] {
        append_preview_line(output, line);
    }
}

/// Build a compact current-file preview from numbered diff rows.
pub(crate) fn build_compact_diff_preview(diff: &str) -> String {
    let lines = if diff.is_empty() {
        Vec::new()
    } else {
        diff.split('\n').collect::<Vec<_>>()
    };
    let added_run_context = ADDED_RUN_CONTEXT_LINES;
    let mut added_lines = 0_usize;
    let mut removed_lines = 0_usize;
    let mut formatted = Vec::new();
    let mut added_run = Vec::new();

    for line in lines {
        let Some(parsed) = parse_compact_diff_line(line) else {
            append_added_run(&mut formatted, &added_run, added_run_context);
            added_run.clear();
            append_preview_line(&mut formatted, line);
            continue;
        };
        match parsed.kind {
            DiffPrefix::Added => {
                added_lines += 1;
                added_run.push(format!("{}:{}", parsed.line_number, parsed.content));
            }
            DiffPrefix::Removed => {
                append_added_run(&mut formatted, &added_run, added_run_context);
                added_run.clear();
                removed_lines += 1;
            }
            DiffPrefix::Context => {
                append_added_run(&mut formatted, &added_run, added_run_context);
                added_run.clear();
                let new_line_number = parsed.line_number
                    + i64::try_from(added_lines).unwrap_or(i64::MAX)
                    - i64::try_from(removed_lines).unwrap_or(i64::MAX);
                append_preview_line(
                    &mut formatted,
                    &format!("{new_line_number}:{}", parsed.content),
                );
            }
        }
    }
    append_added_run(&mut formatted, &added_run, added_run_context);
    while formatted
        .last()
        .is_some_and(|line| is_preview_separator(line))
    {
        formatted.pop();
    }
    formatted.join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rows(old: &[&str], new: &[&str]) -> Vec<String> {
        generate_diff_string(&old.join("\n"), &new.join("\n"))
            .diff
            .split('\n')
            .map(str::to_owned)
            .collect()
    }

    #[test]
    fn collapses_unchanged_lines_between_distant_edits() {
        let old_lines = (1..=20)
            .map(|line| format!("line {line}"))
            .collect::<Vec<_>>();
        let mut new_lines = old_lines.clone();
        new_lines[1] = "line 2 changed".to_owned();
        new_lines[17] = "line 18 changed".to_owned();
        let old: Vec<&str> = old_lines.iter().map(String::as_str).collect();
        let new: Vec<&str> = new_lines.iter().map(String::as_str).collect();
        let result = generate_diff_string(&old.join("\n"), &new.join("\n"));
        assert_eq!(
            result.diff,
            " 1|line 1\n-2|line 2\n+2|line 2 changed\n 3|line 3\n 4|line 4\n 16|line 16\n \
             17|line 17\n-18|line 18\n+18|line 18 changed\n 19|line 19\n 20|line 20"
        );
        assert_eq!(result.first_changed_line, Some(2));
    }

    #[test]
    fn adds_matching_bracket_line_beyond_context() {
        let old = [
            "function outer() {",
            "  const value = 1;",
            "  const two = 2;",
            "  const three = 3;",
            "  const four = 4;",
            "  return value + two + three + four;",
            "}",
        ];
        let mut new = old;
        new[0] = "function renamed() {";
        assert_eq!(
            rows(&old, &new),
            [
                "-1|function outer() {",
                "+1|function renamed() {",
                " 2|  const value = 1;",
                " 3|  const two = 2;",
                "",
                " 7|}",
            ]
        );
    }

    #[test]
    fn translates_new_block_context_to_old_line_numbers() {
        let old = [
            "function outer() {",
            "  const a = 1;",
            "  const keep = 2;",
            "  const b = 3;",
            "  const c = 4;",
            "  const d = 5;",
            "  return a + keep + b;",
            "}",
            "tail();",
        ];
        let mut new = old;
        new[1] = "  const a = 10;";
        let lines = rows(&old, &new);
        assert_eq!(
            lines
                .iter()
                .filter(|line| line.ends_with("|}"))
                .collect::<Vec<_>>(),
            [" 8|}"]
        );
        assert!(lines.contains(&" 1|function outer() {".to_owned()));
    }

    #[test]
    fn compact_preview_matches_omp_diff_preview_cases() {
        let cases = [
            (
                " 1|alpha\n-2|beta\n+2|DELTA\n+3|EPSILON\n 3|gamma",
                "1:alpha\n2:DELTA\n3:EPSILON\n4:gamma",
            ),
            (
                " 1|a1\n 2|a2\n-3|a3\n-4|a4\n+3|X\n+4|Y\n+5|Z\n 5|a5\n 6|a6\n 7|a7",
                "1:a1\n2:a2\n3:X\n4:Y\n5:Z\n6:a5\n7:a6\n8:a7",
            ),
            (
                "+10|line 1\n+11|line 2\n+12|line 3\n+13|line 4\n+14|line 5\n+15|line 6\n+16|line 7",
                "10:line 1\n11:line 2\n…\n15:line 6\n16:line 7",
            ),
            (" 1|alpha\n...\n...\n…\n 20|omega", "1:alpha\n…\n20:omega"),
            (
                "\n 1|alpha\n\n-5|beta\n\n 9|gamma\n\n-12|omitted",
                "1:alpha\n\n8:gamma",
            ),
        ];
        for (diff, preview) in cases {
            assert_eq!(build_compact_diff_preview(diff), preview, "{diff:?}");
        }
    }
}
