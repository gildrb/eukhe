//! Line classification for hashline payloads (omp
//! `modes/hashline/tokenizer.rs`).

use super::{
    messages::{ABORT_MARKER, BEGIN_PATCH_MARKER, END_PATCH_MARKER, HL_FILE_HASH_LENGTH},
    types::{Anchor, ParsedRange},
};

/// Locator and optional register parsed from one operation header.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum BlockTarget {
    Replace {
        range: ParsedRange,
        register: Option<String>,
    },
    Block {
        anchor: Anchor,
        register: Option<String>,
    },
    InsertBefore {
        anchor: Anchor,
        register: Option<String>,
    },
    InsertAfter {
        anchor: Anchor,
        register: Option<String>,
    },
    InsertAfterBlock {
        anchor: Anchor,
        register: Option<String>,
    },
    Cut {
        range: ParsedRange,
        register: Option<String>,
    },
    CutBlock {
        anchor: Anchor,
        register: Option<String>,
    },
    Bof {
        register: Option<String>,
    },
    Eof {
        register: Option<String>,
    },
    Rem,
    Move {
        dest: String,
    },
}

impl BlockTarget {
    /// The optional clipboard register.
    pub(crate) fn register(&self) -> Option<&str> {
        match self {
            Self::Replace { register, .. }
            | Self::Block { register, .. }
            | Self::InsertBefore { register, .. }
            | Self::InsertAfter { register, .. }
            | Self::InsertAfterBlock { register, .. }
            | Self::Cut { register, .. }
            | Self::CutBlock { register, .. }
            | Self::Bof { register }
            | Self::Eof { register } => register.as_deref(),
            Self::Rem | Self::Move { .. } => None,
        }
    }
}

/// One classified payload row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Token {
    Blank {
        line_num: u32,
    },
    EnvelopeBegin {
        line_num: u32,
    },
    EnvelopeEnd {
        line_num: u32,
    },
    Abort {
        line_num: u32,
    },
    Header {
        line_num: u32,
        path: String,
        file_hash: Option<String>,
    },
    OpBlock {
        line_num: u32,
        target: BlockTarget,
        had_colon: bool,
    },
    PayloadLiteral {
        line_num: u32,
        text: String,
    },
    Raw {
        line_num: u32,
        text: String,
    },
}

/// Classify every row of `text` (LF or CRLF), numbering rows from 1. A
/// trailing newline does not produce an extra row.
pub(crate) fn tokenize(text: &str) -> Vec<Token> {
    let mut rows: Vec<&str> = text.split('\n').collect();
    if rows.last() == Some(&"") {
        rows.pop();
    }
    rows.into_iter()
        .zip(1_u32..)
        .map(|(row, line_num)| classify_line(row.strip_suffix('\r').unwrap_or(row), line_num))
        .collect()
}

/// Whether text is a complete operation header.
pub(crate) fn is_hunk_header_text(text: &str) -> bool {
    let lead = text.trim_start();
    ["PUT", "CUT", "REM", "MV"]
        .iter()
        .any(|keyword| lead.starts_with(keyword))
        && parse_hunk_header(text).is_some()
}

fn marker_line_equals(line: &str, marker: &str) -> bool {
    line.trim_end() == marker
}
fn parse_number_prefix(raw: &str) -> Option<(u32, usize)> {
    let bytes = raw.as_bytes();
    if bytes
        .first()
        .is_none_or(|byte| !matches!(byte, b'1'..=b'9'))
    {
        return None;
    }
    let mut end = 1;
    while end < bytes.len() && bytes[end].is_ascii_digit() {
        end += 1;
    }
    Some((raw[..end].parse().ok()?, end))
}

fn parse_range(raw: &str, allow_single: bool) -> Option<(ParsedRange, usize, bool)> {
    let leading = raw.len() - raw.trim_start().len();
    let (start, used) = parse_number_prefix(&raw[leading..])?;
    let mut cursor = leading + used;
    let mut saw_non_ws = false;
    while cursor < raw.len() {
        let ch = raw[cursor..].chars().next()?;
        if ch.is_whitespace() || matches!(ch, '-' | '.' | '=' | '…') {
            saw_non_ws |= !ch.is_whitespace();
            cursor += ch.len_utf8();
        } else {
            break;
        }
    }
    if let Some((end, count)) = parse_number_prefix(&raw[cursor..]) {
        cursor += count;
        while cursor < raw.len() && raw.as_bytes()[cursor].is_ascii_whitespace() {
            cursor += 1;
        }
        return Some((
            ParsedRange {
                start: Anchor { line: start },
                end: Anchor { line: end },
            },
            cursor,
            true,
        ));
    }
    if !allow_single {
        return None;
    }
    if saw_non_ws
        && (cursor == raw.len() || matches!(raw.as_bytes().get(cursor), Some(b':' | b'@')))
    {
        return Some((
            ParsedRange {
                start: Anchor { line: start },
                end: Anchor { line: start },
            },
            cursor,
            true,
        ));
    }
    Some((
        ParsedRange {
            start: Anchor { line: start },
            end: Anchor { line: start },
        },
        cursor,
        false,
    ))
}

fn parse_register_and_colon(raw: &str, mut target: BlockTarget) -> Option<(BlockTarget, bool)> {
    let mut rest = raw.trim_start();
    if let Some(register_raw) = rest.strip_prefix('@') {
        let name_len = register_raw
            .bytes()
            .take_while(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'-'))
            .count();
        if name_len == 0 || name_len > 64 {
            return None;
        }
        let name = register_raw[..name_len].to_string();
        target = with_register(target, Some(name));
        rest = register_raw[name_len..].trim_start();
    }
    let had_colon = rest.starts_with(':');
    if had_colon {
        rest = rest[1..].trim_start();
    }
    if rest.is_empty() {
        Some((target, had_colon))
    } else {
        None
    }
}

fn with_register(target: BlockTarget, register: Option<String>) -> BlockTarget {
    match target {
        BlockTarget::Replace { range, .. } => BlockTarget::Replace { range, register },
        BlockTarget::Block { anchor, .. } => BlockTarget::Block { anchor, register },
        BlockTarget::InsertBefore { anchor, .. } => BlockTarget::InsertBefore { anchor, register },
        BlockTarget::InsertAfter { anchor, .. } => BlockTarget::InsertAfter { anchor, register },
        BlockTarget::InsertAfterBlock { anchor, .. } => {
            BlockTarget::InsertAfterBlock { anchor, register }
        }
        BlockTarget::Cut { range, .. } => BlockTarget::Cut { range, register },
        BlockTarget::CutBlock { anchor, .. } => BlockTarget::CutBlock { anchor, register },
        BlockTarget::Bof { .. } => BlockTarget::Bof { register },
        BlockTarget::Eof { .. } => BlockTarget::Eof { register },
        target @ (BlockTarget::Rem | BlockTarget::Move { .. }) => target,
    }
}

fn parse_put_target(raw: &str) -> Option<(BlockTarget, bool)> {
    let rest = raw.trim_start();
    if let Some(after) = rest.strip_prefix('>') {
        let after = after.trim_start();
        if let Some(tail) = after.strip_prefix('$') {
            return parse_register_and_colon(tail, BlockTarget::Eof { register: None });
        }
        let (line, used) = parse_number_prefix(after)?;
        let mut tail = &after[used..];
        let block = tail.starts_with('*');
        if block {
            tail = &tail[1..];
        }
        let target = if block {
            BlockTarget::InsertAfterBlock {
                anchor: Anchor { line },
                register: None,
            }
        } else {
            BlockTarget::InsertAfter {
                anchor: Anchor { line },
                register: None,
            }
        };
        return parse_register_and_colon(tail, target);
    }
    if let Some(after) = rest.strip_prefix('<') {
        let after = after.trim_start();
        let (line, used) = parse_number_prefix(after)?;
        let mut tail = &after[used..];
        if tail.starts_with('*') {
            tail = &tail[1..];
        }
        let target = if line == 1 {
            BlockTarget::Bof { register: None }
        } else {
            BlockTarget::InsertBefore {
                anchor: Anchor { line },
                register: None,
            }
        };
        return parse_register_and_colon(tail, target);
    }
    let (range, used, had_separator) = parse_range(rest, true)?;
    let mut tail = &rest[used..];
    if tail.starts_with('*') {
        if had_separator {
            return None;
        }
        tail = &tail[1..];
        return parse_register_and_colon(
            tail,
            BlockTarget::Block {
                anchor: range.start,
                register: None,
            },
        );
    }
    parse_register_and_colon(
        tail,
        BlockTarget::Replace {
            range,
            register: None,
        },
    )
}

fn parse_cut_target(raw: &str) -> Option<(BlockTarget, bool)> {
    let rest = raw.trim_start();
    let (range, used, had_separator) = parse_range(rest, true)?;
    let mut tail = &rest[used..];
    if tail.starts_with('*') {
        if had_separator {
            return None;
        }
        tail = &tail[1..];
        return parse_register_and_colon(
            tail,
            BlockTarget::CutBlock {
                anchor: range.start,
                register: None,
            },
        );
    }
    parse_register_and_colon(
        tail,
        BlockTarget::Cut {
            range,
            register: None,
        },
    )
}

fn keyword_tail<'a>(line: &'a str, keyword: &str) -> Option<&'a str> {
    let rest = line.strip_prefix(keyword)?;
    if rest.is_empty()
        || rest.starts_with(':')
        || rest.chars().next().is_some_and(char::is_whitespace)
    {
        Some(rest)
    } else {
        None
    }
}

fn parse_hunk_header(line: &str) -> Option<(BlockTarget, bool)> {
    let line = line.trim();
    if let Some(rest) = keyword_tail(line, "REM") {
        return rest.trim().is_empty().then_some((BlockTarget::Rem, false));
    }
    if let Some(rest) = keyword_tail(line, "MV") {
        let dest = unquote_path(rest.trim())?;
        return (!dest.is_empty()).then_some((BlockTarget::Move { dest }, false));
    }
    if let Some(rest) = keyword_tail(line, "PUT") {
        return parse_put_target(rest);
    }
    if let Some(rest) = keyword_tail(line, "CUT") {
        return parse_cut_target(rest);
    }
    None
}

fn unquote_path(raw: &str) -> Option<String> {
    if raw.len() >= 2
        && ((raw.starts_with('"') && raw.ends_with('"'))
            || (raw.starts_with('\'') && raw.ends_with('\'')))
    {
        return Some(raw[1..raw.len() - 1].to_string());
    }
    if raw.starts_with('"') || raw.starts_with('\'') {
        None
    } else {
        Some(raw.to_string())
    }
}

/// Whether a header path closes a bracket it never opened (`Foo] [bar.ts`).
///
/// The path runs from the row's opening `[` to its final `]`, so a path may
/// legitimately contain brackets (`app/[slug]/page.tsx`). An unmatched `]`
/// cannot come from one authored header — it means the row holds two bracket
/// groups, as in `[*** Begin Patch] [migrations.ts#5275]`, and reading it as a
/// path would aim the edit at a file named after the surrounding noise.
pub(crate) fn header_path_has_orphan_bracket(path: &str) -> bool {
    let mut depth = 0u32;
    for byte in path.bytes() {
        match byte {
            b'[' => depth += 1,
            b']' if depth == 0 => return true,
            b']' => depth -= 1,
            _ => {}
        }
    }
    false
}

fn parse_header(line: &str) -> Option<(String, Option<String>)> {
    let line = line.trim_end();
    let body = line.strip_prefix("[")?.strip_suffix("]")?;
    if body.is_empty() {
        return None;
    }
    if let Some((path, hash)) = body.rsplit_once('#') {
        if path.is_empty()
            || path.contains('#')
            || header_path_has_orphan_bracket(path)
            || hash.len() != HL_FILE_HASH_LENGTH
            || !hash.bytes().all(|byte| byte.is_ascii_hexdigit())
        {
            return None;
        }
        return Some((path.to_string(), Some(hash.to_ascii_uppercase())));
    }
    if body.contains('#') || header_path_has_orphan_bracket(body) {
        None
    } else {
        Some((body.to_string(), None))
    }
}

pub(crate) fn classify_line(line: &str, line_num: u32) -> Token {
    if line.is_empty() {
        return Token::Blank { line_num };
    }
    if marker_line_equals(line, BEGIN_PATCH_MARKER) {
        return Token::EnvelopeBegin { line_num };
    }
    if marker_line_equals(line, END_PATCH_MARKER) {
        return Token::EnvelopeEnd { line_num };
    }
    if marker_line_equals(line, ABORT_MARKER) {
        return Token::Abort { line_num };
    }
    if let Some((path, file_hash)) = parse_header(line) {
        return Token::Header {
            line_num,
            path,
            file_hash,
        };
    }
    if let Some((target, had_colon)) = parse_hunk_header(line) {
        return Token::OpBlock {
            line_num,
            target,
            had_colon,
        };
    }
    if let Some(text) = line.strip_prefix('+') {
        return Token::PayloadLiteral {
            line_num,
            text: text.to_string(),
        };
    }
    Token::Raw {
        line_num,
        text: line.to_string(),
    }
}
