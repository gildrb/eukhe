//! Shared diff computation utilities for the edit and similar tools. Port of
//! `tools/edit-diff.ts`.
//!
//! Offsets into text (`index`, `match_index`, `match_length`, line spans) are
//! UTF-16 code units, as in JS.

mod jsdiff;
#[cfg(test)]
mod tests;

use std::borrow::Cow;

use unicode_normalization::UnicodeNormalization;

/// The `contextLines` default of [`generate_unified_patch`] and
/// [`generate_diff_string`].
pub(crate) const DEFAULT_CONTEXT_LINES: usize = 4;

/// A line ending: the TS `"\r\n" | "\n"`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum LineEnding {
    Lf,
    CrLf,
}

impl LineEnding {
    /// The line ending's text.
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Self::Lf => "\n",
            Self::CrLf => "\r\n",
        }
    }
}

/// Why editing failed: the TS `Error` messages, verbatim.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub(crate) enum EditDiffError {
    #[error("Replacement range is outside the base content.")]
    ReplacementOutsideBaseContent,
    #[error(
        "Cannot preserve unchanged lines because the base content has a different line count."
    )]
    LineCountMismatch,
    #[error("{}", empty_old_text_message(path, *edit_index, *total_edits))]
    EmptyOldText {
        path: String,
        edit_index: usize,
        total_edits: usize,
    },
    #[error("{}", not_found_message(path, *edit_index, *total_edits))]
    NotFound {
        path: String,
        edit_index: usize,
        total_edits: usize,
    },
    #[error("{}", duplicate_message(path, *edit_index, *total_edits, *occurrences))]
    Duplicate {
        path: String,
        edit_index: usize,
        total_edits: usize,
        occurrences: usize,
    },
    #[error(
        "edits[{previous_edit_index}] and edits[{current_edit_index}] overlap in {path}. Merge them into one edit or target disjoint regions."
    )]
    Overlap {
        path: String,
        previous_edit_index: usize,
        current_edit_index: usize,
    },
    #[error("{}", no_change_message(path, *total_edits))]
    NoChange { path: String, total_edits: usize },
}

fn not_found_message(path: &str, edit_index: usize, total_edits: usize) -> String {
    if total_edits == 1 {
        return format!(
            "Could not find the exact text in {path}. The old text must match exactly including all whitespace and newlines."
        );
    }
    format!(
        "Could not find edits[{edit_index}] in {path}. The oldText must match exactly including all whitespace and newlines."
    )
}

fn duplicate_message(
    path: &str,
    edit_index: usize,
    total_edits: usize,
    occurrences: usize,
) -> String {
    if total_edits == 1 {
        return format!(
            "Found {occurrences} occurrences of the text in {path}. The text must be unique. Please provide more context to make it unique."
        );
    }
    format!(
        "Found {occurrences} occurrences of edits[{edit_index}] in {path}. Each oldText must be unique. Please provide more context to make it unique."
    )
}

fn empty_old_text_message(path: &str, edit_index: usize, total_edits: usize) -> String {
    if total_edits == 1 {
        return format!("oldText must not be empty in {path}.");
    }
    format!("edits[{edit_index}].oldText must not be empty in {path}.")
}

fn no_change_message(path: &str, total_edits: usize) -> String {
    if total_edits == 1 {
        return format!(
            "No changes made to {path}. The replacement produced identical content. This might indicate an issue with special characters or the text not existing as expected."
        );
    }
    format!("No changes made to {path}. The replacements produced identical content.")
}

pub(crate) fn detect_line_ending(content: &str) -> LineEnding {
    let crlf_index = content.find("\r\n");
    let lf_index = content.find('\n');
    match (crlf_index, lf_index) {
        (Some(crlf_index), Some(lf_index)) if crlf_index < lf_index => LineEnding::CrLf,
        _ => LineEnding::Lf,
    }
}

pub(crate) fn normalize_to_lf(text: &str) -> String {
    text.replace("\r\n", "\n").replace('\r', "\n")
}

pub(crate) fn restore_line_endings(text: &str, ending: LineEnding) -> String {
    match ending {
        LineEnding::CrLf => text.replace('\n', ending.as_str()),
        LineEnding::Lf => text.to_owned(),
    }
}

/// The JS `WhiteSpace` and `LineTerminator` code points `String.prototype.trimEnd`
/// removes (unlike `char::is_whitespace`: U+FEFF yes, U+0085 no).
fn is_js_whitespace(c: char) -> bool {
    matches!(
        c,
        '\u{0009}'
            | '\u{000A}'
            | '\u{000B}'
            | '\u{000C}'
            | '\u{000D}'
            | '\u{0020}'
            | '\u{00A0}'
            | '\u{1680}'
            | '\u{2000}'
            ..='\u{200A}'
                | '\u{2028}'
                | '\u{2029}'
                | '\u{202F}'
                | '\u{205F}'
                | '\u{3000}'
                | '\u{FEFF}'
    )
}

/// Normalize text for fuzzy matching. Applies progressive transformations:
/// NFKC; strip trailing whitespace from each line; smart quotes to ASCII
/// equivalents; Unicode dashes/hyphens to ASCII hyphen; special Unicode spaces
/// to regular space.
pub(crate) fn normalize_for_fuzzy_match(text: &str) -> String {
    let normalized: String = text.nfkc().collect();
    normalized
        .split('\n')
        .map(|line| line.trim_end_matches(is_js_whitespace))
        .collect::<Vec<_>>()
        .join("\n")
        .chars()
        .map(|c| match c {
            // Smart single quotes.
            '\u{2018}' | '\u{2019}' | '\u{201A}' | '\u{201B}' => '\'',
            // Smart double quotes.
            '\u{201C}' | '\u{201D}' | '\u{201E}' | '\u{201F}' => '"',
            // U+2010 hyphen, U+2011 non-breaking hyphen, U+2012 figure dash,
            // U+2013 en-dash, U+2014 em-dash, U+2015 horizontal bar, U+2212 minus.
            '\u{2010}'..='\u{2015}' | '\u{2212}' => '-',
            // U+00A0 NBSP, U+2002-U+200A various spaces, U+202F narrow NBSP,
            // U+205F medium math space, U+3000 ideographic space.
            '\u{00A0}' | '\u{2002}'..='\u{200A}' | '\u{202F}' | '\u{205F}' | '\u{3000}' => ' ',
            other => other,
        })
        .collect()
}

/// `content.match(/[^\n]*\n|[^\n]+/g) ?? []`.
fn split_lines_with_endings(content: &str) -> Vec<&str> {
    content.split_inclusive('\n').collect()
}

fn utf16_len(text: &str) -> usize {
    text.chars().map(char::len_utf16).sum()
}

/// A line of the base content, in UTF-16 code units.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct LineSpan {
    start: usize,
    end: usize,
}

/// A replacement of `match_length` UTF-16 code units at `match_index`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct TextReplacement {
    pub(crate) match_index: usize,
    pub(crate) match_length: usize,
    pub(crate) new_text: String,
}

#[derive(Clone, Debug)]
struct MatchedEdit {
    edit_index: usize,
    replacement: TextReplacement,
}

fn get_line_spans(content: &str) -> Vec<LineSpan> {
    let mut offset = 0;
    split_lines_with_endings(content)
        .into_iter()
        .map(|line| {
            let span = LineSpan {
                start: offset,
                end: offset + utf16_len(line),
            };
            offset = span.end;
            span
        })
        .collect()
}

/// The lines `[start_line, end_line)` a replacement touches.
fn get_replacement_line_range(
    lines: &[LineSpan],
    replacement: &TextReplacement,
) -> Result<(usize, usize), EditDiffError> {
    let replacement_start = replacement.match_index;
    let replacement_end = replacement.match_index + replacement.match_length;

    let start_line = lines
        .iter()
        .position(|line| replacement_start >= line.start && replacement_start < line.end)
        .ok_or(EditDiffError::ReplacementOutsideBaseContent)?;

    let mut end_line = start_line;
    while end_line < lines.len() && lines[end_line].end < replacement_end {
        end_line += 1;
    }
    if end_line >= lines.len() {
        return Err(EditDiffError::ReplacementOutsideBaseContent);
    }

    Ok((start_line, end_line + 1))
}

/// JS `text.substring(start, end)` on UTF-16 code units: both clamped to the
/// text, swapped if reversed.
fn substring(text: &[u16], start: usize, end: usize) -> &[u16] {
    let start = start.min(text.len());
    let end = end.min(text.len());
    &text[start.min(end)..start.max(end)]
}

/// Apply `replacements` (sorted, disjoint) to `content`, whose first code unit
/// is at `offset` of the text the replacements index.
fn apply_replacements<'r>(
    content: &[u16],
    replacements: impl DoubleEndedIterator<Item = &'r TextReplacement>,
    offset: usize,
) -> Vec<u16> {
    let mut result = content.to_vec();
    for replacement in replacements.rev() {
        // A negative JS index clamps to 0, as `saturating_sub` does.
        let match_index = replacement.match_index.saturating_sub(offset);
        let mut next = substring(&result, 0, match_index).to_vec();
        next.extend(replacement.new_text.encode_utf16());
        next.extend_from_slice(substring(
            &result,
            match_index + replacement.match_length,
            usize::MAX,
        ));
        result = next;
    }
    result
}

/// The text of UTF-16 code units. Offsets from [`fuzzy_find_text`] never
/// split a surrogate pair, so this is lossless for every edit; a caller's
/// offset inside a pair leaves lone surrogates in JS, which writing the text
/// as UTF-8 turns into U+FFFD, as here.
fn from_utf16(units: &[u16]) -> String {
    String::from_utf16_lossy(units)
}

/// Apply replacements matched against `base_content` to `original_content`
/// while preserving unchanged line blocks from the original.
///
/// This is useful when `base_content` is a normalized view of the original.
/// Each replacement is widened to the lines it actually touches, those
/// touched lines are rewritten from the normalized base, and all other lines
/// are copied back from `original_content`. The actual replacement ranges
/// drive preservation so duplicate normalized lines cannot be aligned to the
/// wrong occurrence.
pub(crate) fn apply_replacements_preserving_unchanged_lines(
    original_content: &str,
    base_content: &str,
    replacements: &[TextReplacement],
) -> Result<String, EditDiffError> {
    struct Group<'r> {
        start_line: usize,
        end_line: usize,
        replacements: Vec<&'r TextReplacement>,
    }

    let original_lines = split_lines_with_endings(original_content);
    let base_lines = get_line_spans(base_content);
    if original_lines.len() != base_lines.len() {
        return Err(EditDiffError::LineCountMismatch);
    }

    let mut groups: Vec<Group<'_>> = Vec::new();
    let mut sorted_replacements: Vec<&TextReplacement> = replacements.iter().collect();
    sorted_replacements.sort_by_key(|replacement| replacement.match_index);
    for replacement in sorted_replacements {
        let (start_line, end_line) = get_replacement_line_range(&base_lines, replacement)?;
        if let Some(current) = groups.last_mut() {
            if start_line < current.end_line {
                current.end_line = current.end_line.max(end_line);
                current.replacements.push(replacement);
                continue;
            }
        }
        groups.push(Group {
            start_line,
            end_line,
            replacements: vec![replacement],
        });
    }

    let base_units: Vec<u16> = base_content.encode_utf16().collect();
    let mut original_line_index = 0;
    let mut result = String::new();
    for group in groups {
        result.extend(
            original_lines[original_line_index.min(group.start_line)..group.start_line]
                .iter()
                .copied(),
        );

        let group_start_offset = base_lines[group.start_line].start;
        let group_end_offset = base_lines[group.end_line - 1].end;
        result.push_str(&from_utf16(&apply_replacements(
            &base_units[group_start_offset..group_end_offset],
            group.replacements.into_iter(),
            group_start_offset,
        )));
        original_line_index = group.end_line;
    }
    result.extend(original_lines[original_line_index..].iter().copied());

    Ok(result)
}

/// What [`fuzzy_find_text`] found.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct FuzzyMatchResult<'a> {
    /// Whether a match was found.
    pub(crate) found: bool,
    /// Where the match starts in `content_for_replacement`, in UTF-16 code
    /// units; `None` (TS `-1`) when not found.
    pub(crate) index: Option<usize>,
    /// Length of the matched text in UTF-16 code units.
    pub(crate) match_length: usize,
    /// Whether fuzzy matching was used (false = exact match).
    pub(crate) used_fuzzy_match: bool,
    /// The content to use for replacement operations: the original content
    /// on an exact match, the normalized content on a fuzzy match.
    pub(crate) content_for_replacement: Cow<'a, str>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Edit {
    pub(crate) old_text: String,
    pub(crate) new_text: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct AppliedEditsResult {
    pub(crate) base_content: String,
    pub(crate) new_content: String,
}

/// Find `old_text` in `content`, trying exact match first, then fuzzy match.
/// When fuzzy matching is used, the returned `content_for_replacement` is the
/// fuzzy-normalized version of the content (trailing whitespace stripped,
/// Unicode quotes/dashes normalized to ASCII).
pub(crate) fn fuzzy_find_text<'a>(content: &'a str, old_text: &str) -> FuzzyMatchResult<'a> {
    // Try exact match first.
    if let Some(exact_index) = content.find(old_text) {
        return FuzzyMatchResult {
            found: true,
            index: Some(utf16_len(&content[..exact_index])),
            match_length: utf16_len(old_text),
            used_fuzzy_match: false,
            content_for_replacement: Cow::Borrowed(content),
        };
    }

    // Try fuzzy match: work entirely in normalized space.
    let fuzzy_content = normalize_for_fuzzy_match(content);
    let fuzzy_old_text = normalize_for_fuzzy_match(old_text);
    let Some(fuzzy_index) = fuzzy_content.find(&fuzzy_old_text) else {
        return FuzzyMatchResult {
            found: false,
            index: None,
            match_length: 0,
            used_fuzzy_match: false,
            content_for_replacement: Cow::Borrowed(content),
        };
    };

    // When fuzzy matching, return offsets in normalized space. Callers can
    // use the normalized content to compute replacements, then decide how
    // much of that normalized output should be written back.
    FuzzyMatchResult {
        found: true,
        index: Some(utf16_len(&fuzzy_content[..fuzzy_index])),
        match_length: utf16_len(&fuzzy_old_text),
        used_fuzzy_match: true,
        content_for_replacement: Cow::Owned(fuzzy_content),
    }
}

/// A byte-order mark split off a text.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct BomSplit<'a> {
    /// `"\u{FEFF}"` or `""`.
    pub(crate) bom: &'static str,
    pub(crate) text: &'a str,
}

/// Strip a UTF-8 BOM if present; return both the BOM (if any) and the text
/// without it.
pub(crate) fn strip_bom(content: &str) -> BomSplit<'_> {
    match content.strip_prefix('\u{FEFF}') {
        Some(text) => BomSplit {
            bom: "\u{FEFF}",
            text,
        },
        None => BomSplit {
            bom: "",
            text: content,
        },
    }
}

/// `fuzzyContent.split(fuzzyOldText).length - 1`. An empty separator splits
/// into UTF-16 code units; the `-1` it gives for an empty content is 0 here,
/// which callers only compare with `> 1`.
fn count_occurrences(content: &str, old_text: &str) -> usize {
    let fuzzy_content = normalize_for_fuzzy_match(content);
    let fuzzy_old_text = normalize_for_fuzzy_match(old_text);
    if fuzzy_old_text.is_empty() {
        return utf16_len(&fuzzy_content).saturating_sub(1);
    }
    fuzzy_content.matches(fuzzy_old_text.as_str()).count()
}

/// Apply one or more exact-text replacements to LF-normalized content.
///
/// All edits are matched against the same original content. Replacements are
/// then applied in reverse order so offsets remain stable. If any edit needs
/// fuzzy matching, the operation runs in fuzzy-normalized content space and
/// then overlays those line-level changes onto the original content so
/// unchanged line blocks keep their original bytes.
pub(crate) fn apply_edits_to_normalized_content(
    normalized_content: &str,
    edits: &[Edit],
    path: &str,
) -> Result<AppliedEditsResult, EditDiffError> {
    let normalized_edits: Vec<Edit> = edits
        .iter()
        .map(|edit| Edit {
            old_text: normalize_to_lf(&edit.old_text),
            new_text: normalize_to_lf(&edit.new_text),
        })
        .collect();
    let total_edits = normalized_edits.len();

    if let Some(edit_index) = normalized_edits
        .iter()
        .position(|edit| edit.old_text.is_empty())
    {
        return Err(EditDiffError::EmptyOldText {
            path: path.to_owned(),
            edit_index,
            total_edits,
        });
    }

    let used_fuzzy_match = normalized_edits
        .iter()
        .any(|edit| fuzzy_find_text(normalized_content, &edit.old_text).used_fuzzy_match);
    let replacement_base_content = if used_fuzzy_match {
        Cow::Owned(normalize_for_fuzzy_match(normalized_content))
    } else {
        Cow::Borrowed(normalized_content)
    };

    let mut matched_edits: Vec<MatchedEdit> = Vec::with_capacity(total_edits);
    for (edit_index, edit) in normalized_edits.into_iter().enumerate() {
        let match_result = fuzzy_find_text(&replacement_base_content, &edit.old_text);
        let Some(match_index) = match_result.index else {
            return Err(EditDiffError::NotFound {
                path: path.to_owned(),
                edit_index,
                total_edits,
            });
        };

        let occurrences = count_occurrences(&replacement_base_content, &edit.old_text);
        if occurrences > 1 {
            return Err(EditDiffError::Duplicate {
                path: path.to_owned(),
                edit_index,
                total_edits,
                occurrences,
            });
        }

        matched_edits.push(MatchedEdit {
            edit_index,
            replacement: TextReplacement {
                match_index,
                match_length: match_result.match_length,
                new_text: edit.new_text,
            },
        });
    }

    matched_edits.sort_by_key(|edit| edit.replacement.match_index);
    for pair in matched_edits.windows(2) {
        let [previous, current] = pair else { continue };
        if previous.replacement.match_index + previous.replacement.match_length
            > current.replacement.match_index
        {
            return Err(EditDiffError::Overlap {
                path: path.to_owned(),
                previous_edit_index: previous.edit_index,
                current_edit_index: current.edit_index,
            });
        }
    }
    let replacements: Vec<TextReplacement> = matched_edits
        .into_iter()
        .map(|edit| edit.replacement)
        .collect();

    let new_content = if used_fuzzy_match {
        apply_replacements_preserving_unchanged_lines(
            normalized_content,
            &replacement_base_content,
            &replacements,
        )?
    } else {
        let units: Vec<u16> = replacement_base_content.encode_utf16().collect();
        from_utf16(&apply_replacements(&units, replacements.iter(), 0))
    };

    if normalized_content == new_content {
        return Err(EditDiffError::NoChange {
            path: path.to_owned(),
            total_edits,
        });
    }

    Ok(AppliedEditsResult {
        base_content: normalized_content.to_owned(),
        new_content,
    })
}

/// Generate a standard unified patch: jsdiff's `createTwoFilesPatch(path,
/// path, old, new, undefined, undefined, { context: context_lines,
/// headerOptions: FILE_HEADERS_ONLY })`.
pub(crate) fn generate_unified_patch(
    path: &str,
    old_content: &str,
    new_content: &str,
    context_lines: usize,
) -> String {
    jsdiff::create_two_files_patch(path, path, old_content, new_content, context_lines)
}

/// A display-oriented diff and the first changed line (in the new file).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DiffString {
    pub(crate) diff: String,
    pub(crate) first_changed_line: Option<usize>,
}

/// Generate a display-oriented diff string with line numbers and context.
/// Returns both the diff string and the first changed line number (in the new
/// file).
pub(crate) fn generate_diff_string(
    old_content: &str,
    new_content: &str,
    context_lines: usize,
) -> DiffString {
    let parts = jsdiff::diff_lines(old_content, new_content);

    let old_line_count = old_content.split('\n').count();
    let new_line_count = new_content.split('\n').count();
    let max_line_num = old_line_count.max(new_line_count);
    let mut out = NumberedLines {
        output: Vec::new(),
        width: max_line_num.to_string().len(),
        old_line_num: 1,
        new_line_num: 1,
    };
    let mut last_was_change = false;
    let mut first_changed_line: Option<usize> = None;

    for (index, part) in parts.iter().enumerate() {
        let mut raw: Vec<&str> = part.value.split('\n').collect();
        if raw.last() == Some(&"") {
            raw.pop();
        }

        if part.added || part.removed {
            // Capture the first changed line (in the new file).
            first_changed_line.get_or_insert(out.new_line_num);

            // Show the change.
            for line in raw {
                if part.added {
                    out.added(line);
                } else {
                    out.removed(line);
                }
            }
            last_was_change = true;
        } else {
            // Context lines: only show a few before/after changes.
            let next_part_is_change = parts
                .get(index + 1)
                .is_some_and(|next| next.added || next.removed);
            let has_leading_change = last_was_change;
            let has_trailing_change = next_part_is_change;

            if has_leading_change && has_trailing_change {
                if raw.len() <= context_lines * 2 {
                    out.context(&raw);
                } else {
                    let leading_lines = &raw[..context_lines];
                    let trailing_lines = &raw[raw.len() - context_lines..];
                    let skipped_lines = raw.len() - leading_lines.len() - trailing_lines.len();

                    out.context(leading_lines);
                    out.ellipsis(skipped_lines);
                    out.context(trailing_lines);
                }
            } else if has_leading_change {
                let shown_lines = &raw[..raw.len().min(context_lines)];
                let skipped_lines = raw.len() - shown_lines.len();

                out.context(shown_lines);
                if skipped_lines > 0 {
                    out.ellipsis(skipped_lines);
                }
            } else if has_trailing_change {
                let skipped_lines = raw.len().saturating_sub(context_lines);
                if skipped_lines > 0 {
                    out.ellipsis(skipped_lines);
                }
                out.context(&raw[skipped_lines..]);
            } else {
                // Skip these context lines entirely.
                out.old_line_num += raw.len();
                out.new_line_num += raw.len();
            }

            last_was_change = false;
        }
    }

    DiffString {
        diff: out.output.join("\n"),
        first_changed_line,
    }
}

/// The lines of [`generate_diff_string`] and the line numbers it is at.
struct NumberedLines {
    output: Vec<String>,
    /// Digits of the largest line number; numbers are padded to it.
    width: usize,
    old_line_num: usize,
    new_line_num: usize,
}

impl NumberedLines {
    fn push(&mut self, sign: char, line_num: usize, line: &str) {
        let width = self.width;
        self.output.push(format!("{sign}{line_num:>width$} {line}"));
    }

    fn added(&mut self, line: &str) {
        self.push('+', self.new_line_num, line);
        self.new_line_num += 1;
    }

    fn removed(&mut self, line: &str) {
        self.push('-', self.old_line_num, line);
        self.old_line_num += 1;
    }

    fn context(&mut self, lines: &[&str]) {
        for line in lines {
            self.push(' ', self.old_line_num, line);
            self.old_line_num += 1;
            self.new_line_num += 1;
        }
    }

    /// Skip `skipped_lines` unchanged lines, shown as `...`.
    fn ellipsis(&mut self, skipped_lines: usize) {
        self.output.push(format!(" {} ...", " ".repeat(self.width)));
        self.old_line_num += skipped_lines;
        self.new_line_num += skipped_lines;
    }
}
