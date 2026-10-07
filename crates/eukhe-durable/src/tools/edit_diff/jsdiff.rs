//! The parts of jsdiff (`diff` 8.0.4, the version pi-durable 1.0.4 ships
//! with) the edit tool uses: `diffLines` and `createTwoFilesPatch` with
//! `headerOptions: FILE_HEADERS_ONLY`, no file headers, and no callback.
//! Ported line by line so the output, including the tie-breaking of equal-cost
//! edit scripts, is byte-for-byte jsdiff's.
//!
//! Options jsdiff accepts but the edit tool never passes (`ignoreWhitespace`,
//! `newlineIsToken`, `stripTrailingCr`, `ignoreCase`, `comparator`,
//! `oneChangePerToken`, `maxEditLength`, `timeout`, `callback`) are not ported:
//! with them absent, their branches are dead.

use std::ops::Range;

/// One change object of `diffLines`: `count` tokens (lines) of `value`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Change<'a> {
    pub(super) value: &'a str,
    pub(super) count: usize,
    pub(super) added: bool,
    pub(super) removed: bool,
}

/// `Diff.diffLines(old, new)`.
pub(super) fn diff_lines<'a>(old: &'a str, new: &'a str) -> Vec<Change<'a>> {
    let old_tokens = remove_empty(tokenize(old));
    let new_tokens = remove_empty(tokenize(new));
    Myers {
        old,
        new,
        old_tokens: &old_tokens,
        new_tokens: &new_tokens,
        components: Vec::new(),
    }
    .diff()
}

/// `tokenize` of `line.js`: `value.split(/(\n|\r\n)/)`, the final empty part
/// dropped, each separator merged into the line before it. Tokens are byte
/// ranges of `value`; consecutive tokens are adjacent.
fn tokenize(value: &str) -> Vec<Range<usize>> {
    let bytes = value.as_bytes();
    // The parts of the split: lines at even indices, separators at odd ones.
    let mut parts: Vec<Range<usize>> = Vec::new();
    let mut line_start = 0;
    let mut index = 0;
    while index < bytes.len() {
        let separator_length = match bytes[index] {
            b'\n' => 1,
            b'\r' if bytes.get(index + 1) == Some(&b'\n') => 2,
            _ => 0,
        };
        if separator_length == 0 {
            index += 1;
            continue;
        }
        parts.push(line_start..index);
        parts.push(index..index + separator_length);
        index += separator_length;
        line_start = index;
    }
    parts.push(line_start..bytes.len());
    // Ignore the final empty token that occurs if the string ends with a new line.
    if parts.last().is_some_and(Range::is_empty) {
        parts.pop();
    }
    let mut lines: Vec<Range<usize>> = Vec::new();
    for (part_index, part) in parts.into_iter().enumerate() {
        match lines.last_mut() {
            Some(line) if part_index % 2 == 1 => line.end = part.end,
            _ => lines.push(part),
        }
    }
    lines
}

fn remove_empty(tokens: Vec<Range<usize>>) -> Vec<Range<usize>> {
    tokens
        .into_iter()
        .filter(|token| !token.is_empty())
        .collect()
}

/// A node of the linked list of change components jsdiff builds; the list is
/// an arena here, `previous` an index into it.
#[derive(Clone, Copy, Debug)]
struct Component {
    count: usize,
    added: bool,
    removed: bool,
    previous: Option<usize>,
}

/// A furthest-reaching path on one diagonal.
#[derive(Clone, Copy, Debug)]
struct Path {
    /// Position in the old tokens; -1 before the first.
    old_pos: isize,
    last_component: Option<usize>,
}

struct Myers<'a, 't> {
    old: &'a str,
    new: &'a str,
    old_tokens: &'t [Range<usize>],
    new_tokens: &'t [Range<usize>],
    components: Vec<Component>,
}

impl<'a> Myers<'a, '_> {
    /// `Diff.diffWithOptionsObj` without a callback or limits.
    #[expect(
        clippy::cast_possible_wrap,
        reason = "token counts are lengths of in-memory vectors, far below isize::MAX"
    )]
    fn diff(mut self) -> Vec<Change<'a>> {
        let new_len = self.new_tokens.len() as isize;
        let old_len = self.old_tokens.len() as isize;
        let max_edit_length = new_len + old_len;
        // `bestPath` is a sparse JS array indexed by diagonal in
        // `-(max_edit_length + 1)..=max_edit_length + 1`.
        let offset = max_edit_length + 1;
        let mut best_path: Vec<Option<Path>> =
            vec![None; usize::try_from(2 * offset + 1).unwrap_or(0)];
        let slot = |diagonal: isize| usize::try_from(diagonal + offset).unwrap_or(0);

        let mut seed = Path {
            old_pos: -1,
            last_component: None,
        };
        // Seed edit length 0, i.e. the content starts with the same values.
        let new_pos = self.extract_common(&mut seed, 0);
        if seed.old_pos + 1 >= old_len && new_pos + 1 >= new_len {
            // Identity per the equality and tokenizer.
            return self.build_values(seed.last_component);
        }
        best_path[slot(0)] = Some(seed);

        // Once a path hits the right edge of the edit graph on some diagonal,
        // no diagonal above it can do better, and once one hits the bottom,
        // no diagonal below it can; jsdiff records this in these bounds.
        let mut min_diagonal_to_consider = isize::MIN;
        let mut max_diagonal_to_consider = isize::MAX;
        // Myers's algorithm reaches the end within `old_len + new_len`
        // edits, jsdiff's default `maxEditLength`, so this loop returns.
        let mut edit_length: isize = 1;
        loop {
            let mut diagonal = min_diagonal_to_consider.max(-edit_length);
            while diagonal <= max_diagonal_to_consider.min(edit_length) {
                let remove_path = best_path[slot(diagonal - 1)];
                let add_path = best_path[slot(diagonal + 1)];
                if remove_path.is_some() {
                    // No one else is going to attempt to use this value.
                    best_path[slot(diagonal - 1)] = None;
                }
                // What newPos will be after an insertion.
                let addable = add_path.filter(|path| {
                    let add_path_new_pos = path.old_pos - diagonal;
                    0 <= add_path_new_pos && add_path_new_pos < new_len
                });
                let removable = remove_path.filter(|path| path.old_pos + 1 < old_len);
                // Branch from the prior path whose position in the old
                // tokens is the farthest from the origin and does not pass
                // the bounds of the edit graph.
                let mut base_path = match (addable, removable) {
                    (None, None) => {
                        // A terminal path: prune it.
                        best_path[slot(diagonal)] = None;
                        diagonal += 2;
                        continue;
                    }
                    (Some(add), None) => self.add_to_path(add, Edit::Add),
                    (Some(add), Some(remove)) if remove.old_pos < add.old_pos => {
                        self.add_to_path(add, Edit::Add)
                    }
                    (_, Some(remove)) => self.add_to_path(remove, Edit::Remove),
                };
                let new_pos = self.extract_common(&mut base_path, diagonal);
                if base_path.old_pos + 1 >= old_len && new_pos + 1 >= new_len {
                    // The end of both token lists: done.
                    return self.build_values(base_path.last_component);
                }
                best_path[slot(diagonal)] = Some(base_path);
                if base_path.old_pos + 1 >= old_len {
                    max_diagonal_to_consider = max_diagonal_to_consider.min(diagonal - 1);
                }
                if new_pos + 1 >= new_len {
                    min_diagonal_to_consider = min_diagonal_to_consider.max(diagonal + 1);
                }
                diagonal += 2;
            }
            edit_length += 1;
        }
    }

    fn add_to_path(&mut self, path: Path, edit: Edit) -> Path {
        let (added, removed, old_pos_inc) = match edit {
            Edit::Add => (true, false, 0),
            Edit::Remove => (false, true, 1),
        };
        let last = path.last_component.map(|index| self.components[index]);
        let component = match last {
            Some(last) if last.added == added && last.removed == removed => Component {
                count: last.count + 1,
                added,
                removed,
                previous: last.previous,
            },
            _ => Component {
                count: 1,
                added,
                removed,
                previous: path.last_component,
            },
        };
        self.components.push(component);
        Path {
            old_pos: path.old_pos + old_pos_inc,
            last_component: Some(self.components.len() - 1),
        }
    }

    /// Follow the diagonal while tokens are equal; returns the new position.
    fn extract_common(&mut self, base_path: &mut Path, diagonal: isize) -> isize {
        let mut old_pos = base_path.old_pos;
        let mut new_pos = old_pos - diagonal;
        let mut common_count = 0;
        while let (Some(old_token), Some(new_token)) = (
            token_at(self.old_tokens, old_pos + 1),
            token_at(self.new_tokens, new_pos + 1),
        ) {
            if self.old[old_token] != self.new[new_token] {
                break;
            }
            new_pos += 1;
            old_pos += 1;
            common_count += 1;
        }
        if common_count > 0 {
            self.components.push(Component {
                count: common_count,
                added: false,
                removed: false,
                previous: base_path.last_component,
            });
            base_path.last_component = Some(self.components.len() - 1);
        }
        base_path.old_pos = old_pos;
        new_pos
    }

    fn build_values(&self, last_component: Option<usize>) -> Vec<Change<'a>> {
        let mut components: Vec<Component> = Vec::new();
        let mut next = last_component;
        while let Some(index) = next {
            let component = self.components[index];
            components.push(component);
            next = component.previous;
        }
        components.reverse();

        let mut new_pos = 0;
        let mut old_pos = 0;
        components
            .into_iter()
            .map(|component| {
                let value = if component.removed {
                    let value = join(
                        self.old,
                        &self.old_tokens[old_pos..old_pos + component.count],
                    );
                    old_pos += component.count;
                    value
                } else {
                    let value = join(
                        self.new,
                        &self.new_tokens[new_pos..new_pos + component.count],
                    );
                    new_pos += component.count;
                    // Common case.
                    if !component.added {
                        old_pos += component.count;
                    }
                    value
                };
                Change {
                    value,
                    count: component.count,
                    added: component.added,
                    removed: component.removed,
                }
            })
            .collect()
    }
}

#[derive(Clone, Copy)]
enum Edit {
    Add,
    Remove,
}

/// The token at a JS index: none below 0 or past the end.
fn token_at(tokens: &[Range<usize>], index: isize) -> Option<Range<usize>> {
    usize::try_from(index)
        .ok()
        .and_then(|index| tokens.get(index))
        .cloned()
}

/// The adjacent tokens joined: the text they span.
fn join<'a>(text: &'a str, tokens: &[Range<usize>]) -> &'a str {
    match (tokens.first(), tokens.last()) {
        (Some(first), Some(last)) => &text[first.start..last.end],
        _ => "",
    }
}

/// One hunk of `structuredPatch`.
struct Hunk {
    old_start: usize,
    old_lines: usize,
    new_start: usize,
    new_lines: usize,
    lines: Vec<String>,
}

/// `Diff.createTwoFilesPatch(oldFileName, newFileName, oldStr, newStr,
/// undefined, undefined, { context, headerOptions: FILE_HEADERS_ONLY })`.
pub(super) fn create_two_files_patch(
    old_file_name: &str,
    new_file_name: &str,
    old: &str,
    new: &str,
    context: usize,
) -> String {
    format_patch(
        old_file_name,
        new_file_name,
        structured_patch(old, new, context),
    )
}

/// The hunks of `structuredPatch`.
fn structured_patch(old: &str, new: &str, context: usize) -> Vec<Hunk> {
    // STEP 1: build up the patch with no "\ No newline at end of file" lines
    // and with the lines keeping their trailing newline characters.
    let mut diff: Vec<(bool, bool, Vec<&str>)> = diff_lines(old, new)
        .into_iter()
        .map(|change| (change.added, change.removed, split_lines(change.value)))
        .collect();
    // An empty value appended to make cleanup easier.
    diff.push((false, false, Vec::new()));

    let context_lines =
        |lines: &[&str]| -> Vec<String> { lines.iter().map(|entry| format!(" {entry}")).collect() };

    let mut hunks: Vec<Hunk> = Vec::new();
    // 0: no range open.
    let mut old_range_start = 0;
    let mut new_range_start = 0;
    let mut cur_range: Vec<String> = Vec::new();
    let mut old_line = 1;
    let mut new_line = 1;
    for (index, (added, removed, lines)) in diff.iter().enumerate() {
        if *added || *removed {
            // If there is previous context, start with that.
            if old_range_start == 0 {
                old_range_start = old_line;
                new_range_start = new_line;
                if let Some((_, _, previous)) = index.checked_sub(1).map(|previous| &diff[previous])
                {
                    cur_range = if context > 0 {
                        context_lines(&previous[previous.len().saturating_sub(context)..])
                    } else {
                        Vec::new()
                    };
                    old_range_start -= cur_range.len();
                    new_range_start -= cur_range.len();
                }
            }
            // Output the changes.
            let sign = if *added { '+' } else { '-' };
            cur_range.extend(lines.iter().map(|line| format!("{sign}{line}")));
            // Track the updated file position.
            if *added {
                new_line += lines.len();
            } else {
                old_line += lines.len();
            }
        } else {
            // Identical context lines: track line changes.
            if old_range_start != 0 {
                // Close out any changes that have been output (or join overlapping).
                if lines.len() <= context * 2 && index + 2 < diff.len() {
                    // Overlapping.
                    cur_range.extend(context_lines(lines));
                } else {
                    // End the range and output.
                    let context_size = lines.len().min(context);
                    cur_range.extend(context_lines(&lines[..context_size]));
                    hunks.push(Hunk {
                        old_start: old_range_start,
                        old_lines: old_line - old_range_start + context_size,
                        new_start: new_range_start,
                        new_lines: new_line - new_range_start + context_size,
                        lines: std::mem::take(&mut cur_range),
                    });
                    old_range_start = 0;
                    new_range_start = 0;
                }
            }
            old_line += lines.len();
            new_line += lines.len();
        }
    }

    // Step 2: eliminate the trailing `\n` from each line of each hunk and,
    // where needed, add "\ No newline at end of file".
    for hunk in &mut hunks {
        let mut lines = Vec::with_capacity(hunk.lines.len() + 2);
        for mut line in std::mem::take(&mut hunk.lines) {
            if line.ends_with('\n') {
                line.pop();
                lines.push(line);
            } else {
                lines.push(line);
                lines.push("\\ No newline at end of file".to_owned());
            }
        }
        hunk.lines = lines;
    }
    hunks
}

/// `formatPatch` with `FILE_HEADERS_ONLY` and no headers.
fn format_patch(old_file_name: &str, new_file_name: &str, hunks: Vec<Hunk>) -> String {
    let mut ret: Vec<String> = vec![
        format!("--- {old_file_name}"),
        format!("+++ {new_file_name}"),
    ];
    for mut hunk in hunks {
        // Unified diff format quirk: if the chunk size is 0, the first number
        // is one lower than one would expect.
        if hunk.old_lines == 0 {
            hunk.old_start -= 1;
        }
        if hunk.new_lines == 0 {
            hunk.new_start -= 1;
        }
        ret.push(format!(
            "@@ -{},{} +{},{} @@",
            hunk.old_start, hunk.old_lines, hunk.new_start, hunk.new_lines
        ));
        ret.extend(hunk.lines);
    }
    ret.join("\n") + "\n"
}

/// Split `text` into lines, keeping the trailing newline character where
/// present (`splitLines` of `create.js`).
fn split_lines(text: &str) -> Vec<&str> {
    if text.is_empty() {
        // `"".split("\n")` is `[""]`.
        return vec![""];
    }
    text.split_inclusive('\n').collect()
}
