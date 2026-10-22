//! Agent Markdown to Signal text: the markers become `signal-cli` text styles
//! (`start:length:STYLE`, UTF-16 code units), and long replies split into
//! chunks Signal accepts.

use eukhe_tui::width::str_width;

#[cfg(test)]
mod tests;

/// The UTF-16 length limit of one chunk.
const CHUNK_UNITS: usize = 2000;

/// One Signal message: plain text and its `signal-cli` text styles.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct StyledText {
    pub(crate) text: String,
    /// `start:length:STYLE`, in UTF-16 code units of `text`.
    pub(crate) styles: Vec<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Style {
    Bold,
    Italic,
    Strikethrough,
    Monospace,
}

impl Style {
    fn name(self) -> &'static str {
        match self {
            Style::Bold => "BOLD",
            Style::Italic => "ITALIC",
            Style::Strikethrough => "STRIKETHROUGH",
            Style::Monospace => "MONOSPACE",
        }
    }
}

/// A styled range, in UTF-16 code units: `start..end`.
#[derive(Debug, Clone, Copy)]
struct Span {
    start: usize,
    end: usize,
    style: Style,
}

/// Rendered text with its length in UTF-16 code units and its styled ranges.
#[derive(Debug, Default)]
struct Rendered {
    text: String,
    units: usize,
    spans: Vec<Span>,
}

impl Rendered {
    fn push(&mut self, text: &str) {
        self.text.push_str(text);
        self.units += text.encode_utf16().count();
    }

    /// Starts an output line: a line break unless nothing is out yet, so
    /// leading blank lines disappear.
    fn begin_line(&mut self) {
        if !self.text.is_empty() {
            self.text.push('\n');
            self.units += 1;
        }
    }

    /// Styles everything pushed since `start` (a former `units`).
    fn style_from(&mut self, start: usize, style: Style) {
        if self.units > start {
            self.spans.push(Span {
                start,
                end: self.units,
                style,
            });
        }
    }

    fn append(&mut self, other: &Rendered) {
        let offset = self.units;
        self.text.push_str(&other.text);
        self.units += other.units;
        self.spans.extend(other.spans.iter().map(|span| Span {
            start: span.start + offset,
            end: span.end + offset,
            style: span.style,
        }));
    }
}

/// Renders agent Markdown as Signal messages of at most 2000 UTF-16 code
/// units each. Splits prefer blank lines, then line breaks, then spaces.
/// Unclosed markers stay literal text. Never returns an empty chunk; blank
/// input gives no chunks.
pub(crate) fn render(markdown: &str) -> Vec<StyledText> {
    let lines: Vec<&str> = markdown.lines().collect();
    let mut out = Rendered::default();
    let mut index = 0;
    while index < lines.len() {
        let line = lines[index];
        let fenced = fence_open(line).and_then(|(fence, length)| {
            (index + 1..lines.len())
                .find(|&candidate| fence_closes(lines[candidate], fence, length))
        });
        if let Some(close) = fenced {
            let mut start = None;
            for body in &lines[index + 1..close] {
                out.begin_line();
                start.get_or_insert(out.units);
                out.push(body);
            }
            if let Some(start) = start {
                out.style_from(start, Style::Monospace);
            }
            index = close + 1;
            continue;
        }
        if line.contains('|')
            && lines
                .get(index + 1)
                .is_some_and(|next| is_delimiter_row(next))
        {
            let end = (index + 2..lines.len())
                .find(|&row| !lines[row].contains('|') || lines[row].trim().is_empty())
                .unwrap_or(lines.len());
            out.push_table(&lines[index..end]);
            index = end;
            continue;
        }
        out.begin_line();
        if let Some(heading) = heading(line) {
            let start = out.units;
            inline(heading, &mut out);
            out.style_from(start, Style::Bold);
        } else {
            let content = line.trim_start();
            let indent = &line[..line.len() - content.len()];
            match content
                .strip_prefix("* ")
                .or_else(|| content.strip_prefix("+ "))
            {
                Some(item) => {
                    out.push(indent);
                    out.push("- ");
                    inline(item, &mut out);
                }
                None => inline(line, &mut out),
            }
        }
        index += 1;
    }
    out.into_chunks()
}

/// Where a table's cells go: the width of every column (the rule row) and,
/// per row, the spaces after each cell but the last column's
/// (`layout` in `bend/gateway_width.bend`, `LAWS.bend` section `gateway_width`).
#[derive(Debug, Clone, PartialEq, Eq)]
struct Layout {
    widths: Vec<usize>,
    pads: Vec<Vec<usize>>,
}

/// The layout of a table whose cells have these display widths, row by
/// row: a column is as wide as its widest cell (a missing cell is 0
/// wide), and a cell's pad is its column's width less its own.
fn layout(rows: &[Vec<usize>]) -> Layout {
    let columns = rows.iter().map(Vec::len).max().unwrap_or(0);
    let widths: Vec<usize> = (0..columns)
        .map(|column| {
            rows.iter()
                .filter_map(|row| row.get(column).copied())
                .max()
                .unwrap_or(0)
        })
        .collect();
    let pads = rows
        .iter()
        .map(|row| {
            widths
                .iter()
                .take(columns.saturating_sub(1))
                .enumerate()
                .map(|(column, width)| width - row.get(column).copied().unwrap_or(0))
                .collect()
        })
        .collect();
    Layout { widths, pads }
}

impl Rendered {
    /// Pushes a table (header, delimiter row, body rows) as a monospace
    /// block with aligned columns.
    fn push_table(&mut self, lines: &[&str]) {
        let rows: Vec<Vec<Rendered>> = lines
            .iter()
            .enumerate()
            .filter(|&(row, _)| row != 1)
            .map(|(_, row)| {
                table_cells(row)
                    .into_iter()
                    .map(|cell| {
                        let mut rendered = Rendered::default();
                        inline(cell, &mut rendered);
                        rendered
                    })
                    .collect()
            })
            .collect();
        let measured: Vec<Vec<usize>> = rows
            .iter()
            .map(|row| row.iter().map(|cell| str_width(&cell.text)).collect())
            .collect();
        let Layout { widths, pads } = layout(&measured);
        self.begin_line();
        let start = self.units;
        for (row_index, (row, pads)) in rows.iter().zip(&pads).enumerate() {
            if row_index > 0 {
                self.begin_line();
            }
            for column in 0..widths.len() {
                if column > 0 {
                    self.push(" | ");
                }
                if let Some(cell) = row.get(column) {
                    self.append(cell);
                }
                if let Some(pad) = pads.get(column) {
                    self.push(&" ".repeat(*pad));
                }
            }
            if row_index == 0 {
                self.begin_line();
                let rule: Vec<String> = widths.iter().map(|width| "-".repeat(*width)).collect();
                self.push(&rule.join("-|-"));
            }
        }
        self.style_from(start, Style::Monospace);
    }

    /// Splits the text into chunks of at most [`CHUNK_UNITS`], with the
    /// styles clipped to each chunk and re-based on its start.
    fn into_chunks(self) -> Vec<StyledText> {
        let text = self.text.as_str();
        let end = text.trim_end().len();
        let mut chunks = Vec::new();
        let mut position = 0;
        let mut position_units = 0;
        while position < end {
            let skipped =
                text[position..end].len() - text[position..end].trim_start_matches('\n').len();
            position += skipped;
            position_units += skipped;
            let rest = &text[position..end];
            if rest.is_empty() {
                break;
            }
            let mut limit = rest.len();
            let mut units = 0;
            for (offset, character) in rest.char_indices() {
                if units + character.len_utf16() > CHUNK_UNITS {
                    limit = offset;
                    break;
                }
                units += character.len_utf16();
            }
            let (chunk_end, next) = if limit == rest.len() {
                (limit, limit)
            } else {
                // A boundary in the first half makes a needlessly short chunk.
                let window = &rest[..limit];
                let floor = limit / 2;
                let late = |at: &usize| *at >= floor;
                if let Some(blank) = window.rfind("\n\n").filter(late) {
                    let after =
                        blank + rest[blank..].len() - rest[blank..].trim_start_matches('\n').len();
                    (window[..blank].trim_end_matches('\n').len(), after)
                } else if let Some(at) = window
                    .rfind('\n')
                    .filter(late)
                    .or_else(|| window.rfind(' ').filter(late))
                {
                    (at, at + 1)
                } else {
                    (limit, limit)
                }
            };
            let chunk = rest[..chunk_end].trim_end();
            if !chunk.trim_start().is_empty() {
                let window_end = position_units + chunk.encode_utf16().count();
                let styles = self
                    .spans
                    .iter()
                    .filter_map(|span| {
                        let start = span.start.max(position_units);
                        let stop = span.end.min(window_end);
                        (start < stop).then(|| {
                            format!(
                                "{}:{}:{}",
                                start - position_units,
                                stop - start,
                                span.style.name()
                            )
                        })
                    })
                    .collect();
                chunks.push(StyledText {
                    text: chunk.to_owned(),
                    styles,
                });
            }
            position_units += rest[..next].encode_utf16().count();
            position += next;
        }
        chunks
    }
}

/// An opening code fence: its character and run length.
fn fence_open(line: &str) -> Option<(u8, usize)> {
    let content = line.trim_start_matches(' ');
    if line.len() - content.len() > 3 {
        return None;
    }
    let fence = *content.as_bytes().first()?;
    if fence != b'`' && fence != b'~' {
        return None;
    }
    let length = run_length(content.as_bytes(), 0, fence);
    let info = &content[length..];
    (length >= 3 && !(fence == b'`' && info.contains('`'))).then_some((fence, length))
}

fn fence_closes(line: &str, fence: u8, length: usize) -> bool {
    let content = line.trim_start_matches(' ');
    let run = run_length(content.as_bytes(), 0, fence);
    line.len() - content.len() <= 3 && run >= length && content[run..].trim().is_empty()
}

/// The content of an ATX heading line (`# x`), without the closing hashes.
fn heading(line: &str) -> Option<&str> {
    let content = line.trim_start_matches(' ');
    if line.len() - content.len() > 3 {
        return None;
    }
    let level = run_length(content.as_bytes(), 0, b'#');
    if !(1..=6).contains(&level) {
        return None;
    }
    let rest = &content[level..];
    if !rest.is_empty() && !rest.starts_with([' ', '\t']) {
        return None;
    }
    let rest = rest.trim();
    let without_closing = rest.trim_end_matches('#');
    if without_closing.is_empty() {
        return Some(without_closing);
    }
    if without_closing.ends_with([' ', '\t']) {
        return Some(without_closing.trim_end());
    }
    Some(rest)
}

fn table_cells(line: &str) -> Vec<&str> {
    let row = line.trim();
    let row = row.strip_prefix('|').unwrap_or(row);
    let row = row.strip_suffix('|').unwrap_or(row);
    row.split('|').map(str::trim).collect()
}

/// A table delimiter row (`|---|:--:|`).
fn is_delimiter_row(line: &str) -> bool {
    line.contains('|')
        && table_cells(line).iter().all(|cell| {
            let dashes = cell.trim_start_matches(':').trim_end_matches(':');
            !dashes.is_empty() && dashes.bytes().all(|byte| byte == b'-')
        })
}

fn run_length(bytes: &[u8], from: usize, byte: u8) -> usize {
    bytes[from..]
        .iter()
        .take_while(|&&candidate| candidate == byte)
        .count()
}

/// The start of the backtick run of exactly `length` that closes a code span.
fn code_close(bytes: &[u8], from: usize, length: usize) -> Option<usize> {
    let mut index = from;
    while index < bytes.len() {
        if bytes[index] == b'`' {
            let run = run_length(bytes, index, b'`');
            if run == length {
                return Some(index);
            }
            index += run;
        } else {
            index += 1;
        }
    }
    None
}

/// The index of the bracket that closes the one before `from`, skipping
/// nested pairs, escapes and code spans.
fn bracket_close(bytes: &[u8], from: usize, open: u8, close: u8) -> Option<usize> {
    let mut depth = 0_usize;
    let mut index = from;
    while index < bytes.len() {
        let byte = bytes[index];
        if byte == b'\\' {
            index += 2;
        } else if byte == b'`' {
            let run = run_length(bytes, index, b'`');
            index = code_close(bytes, index + run, run).map_or(index + run, |end| end + run);
        } else if byte == close {
            if depth == 0 {
                return Some(index);
            }
            depth -= 1;
            index += 1;
        } else {
            if byte == open {
                depth += 1;
            }
            index += 1;
        }
    }
    None
}

/// The start of the delimiter (`length` times `marker`) that closes an
/// emphasis opened before `from`.
fn emphasis_close(text: &str, from: usize, marker: u8, length: usize) -> Option<usize> {
    let bytes = text.as_bytes();
    let mut index = from;
    while index < bytes.len() {
        let byte = bytes[index];
        if byte == b'\\' {
            index += 2;
        } else if byte == b'`' {
            let run = run_length(bytes, index, b'`');
            index = code_close(bytes, index + run, run).map_or(index + run, |end| end + run);
        } else if byte == marker {
            let run = run_length(bytes, index, marker);
            // `***` closes both a strong and an emphasis: take its tail.
            let candidate = if run == length {
                Some(index)
            } else if run == 3 {
                Some(index + 3 - length)
            } else {
                None
            };
            let closes = candidate.filter(|&at| {
                at > from
                    && text[..at]
                        .chars()
                        .next_back()
                        .is_some_and(|before| !before.is_whitespace())
                    && (marker != b'_'
                        || !text[at + length..]
                            .chars()
                            .next()
                            .is_some_and(char::is_alphanumeric))
            });
            if closes.is_some() {
                return closes;
            }
            index += run;
        } else {
            index += 1;
        }
    }
    None
}

/// Renders the inline Markdown of one line.
fn inline(text: &str, out: &mut Rendered) {
    let bytes = text.as_bytes();
    let mut plain = 0;
    let mut index = 0;
    while index < bytes.len() {
        match bytes[index] {
            b'\\' if bytes.get(index + 1).is_some_and(u8::is_ascii_punctuation) => {
                out.push(&text[plain..index]);
                out.push(&text[index + 1..index + 2]);
                index += 2;
                plain = index;
            }
            b'`' => {
                let run = run_length(bytes, index, b'`');
                match code_close(bytes, index + run, run) {
                    Some(close) => {
                        out.push(&text[plain..index]);
                        let code = &text[index + run..close];
                        let code = match code
                            .strip_prefix(' ')
                            .and_then(|inner| inner.strip_suffix(' '))
                        {
                            Some(inner) if !code.trim().is_empty() => inner,
                            Some(_) | None => code,
                        };
                        let start = out.units;
                        out.push(code);
                        out.style_from(start, Style::Monospace);
                        index = close + run;
                        plain = index;
                    }
                    None => index += run,
                }
            }
            marker @ (b'*' | b'_' | b'~') => {
                let run = run_length(bytes, index, marker);
                let emphasis = match (marker, run) {
                    (b'~', 2) => Some((2, Style::Strikethrough)),
                    (b'*' | b'_', 1) => Some((1, Style::Italic)),
                    (b'*' | b'_', 2 | 3) => Some((2, Style::Bold)),
                    _ => None,
                };
                let opens = |length: usize| {
                    text[index + length..]
                        .chars()
                        .next()
                        .is_some_and(|after| !after.is_whitespace())
                        && (marker != b'_'
                            || !text[..index]
                                .chars()
                                .next_back()
                                .is_some_and(char::is_alphanumeric))
                };
                match emphasis
                    .filter(|&(length, _)| opens(length))
                    .and_then(|(length, style)| {
                        emphasis_close(text, index + length, marker, length)
                            .map(|close| (length, style, close))
                    }) {
                    Some((length, style, close)) => {
                        out.push(&text[plain..index]);
                        let start = out.units;
                        inline(&text[index + length..close], out);
                        out.style_from(start, style);
                        index = close + length;
                        plain = index;
                    }
                    None => index += run,
                }
            }
            b'[' | b'!' | b'<' => match link_at(text, index) {
                Some(link) => {
                    out.push(&text[plain..index]);
                    if link.label == link.target || link.label.is_empty() {
                        out.push(link.target);
                    } else {
                        inline(link.label, out);
                        out.push(" (");
                        out.push(link.target);
                        out.push(")");
                    }
                    index = link.end;
                    plain = index;
                }
                None => index += 1,
            },
            _ => index += 1,
        }
    }
    out.push(&text[plain..]);
}

/// A link: `[label](target)`, `![label](target)` or `<target>`.
struct Link<'a> {
    /// Empty for an autolink.
    label: &'a str,
    target: &'a str,
    /// The byte after the link.
    end: usize,
}

/// The link that starts at `index`, if one does.
fn link_at(text: &str, index: usize) -> Option<Link<'_>> {
    let bytes = text.as_bytes();
    if bytes[index] == b'<' {
        let length = text[index + 1..].find('>')?;
        let target = &text[index + 1..index + 1 + length];
        let autolink = !target.contains(char::is_whitespace)
            && (target.contains("://") || target.starts_with("mailto:"));
        return autolink.then_some(Link {
            label: "",
            target,
            end: index + length + 2,
        });
    }
    let open = if bytes[index] == b'!' {
        index + 1
    } else {
        index
    };
    if bytes.get(open) != Some(&b'[') {
        return None;
    }
    let close = bracket_close(bytes, open + 1, b'[', b']')?;
    if bytes.get(close + 1) != Some(&b'(') {
        return None;
    }
    let end = bracket_close(bytes, close + 2, b'(', b')')?;
    let target = text[close + 2..end].trim();
    // Drop a link title: `url "title"`.
    let target = target.split_whitespace().next().unwrap_or(target);
    let target = target
        .strip_prefix('<')
        .and_then(|inner| inner.strip_suffix('>'))
        .unwrap_or(target);
    Some(Link {
        label: &text[open + 1..close],
        target,
        end: end + 1,
    })
}
