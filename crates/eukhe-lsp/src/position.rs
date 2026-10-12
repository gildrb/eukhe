//! Positions: the model's 1-based line + symbol spec, the LSP wire
//! position in the negotiated encoding, and the 1-based Unicode-scalar
//! columns that come back.

use std::path::Path;

use eukhe_types::lsp::{LspError, LspPoint, LspSpan};

use crate::protocol::{Position, Range};

/// The negotiated LSP position encoding (`general.positionEncodings`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PositionEncoding {
    Utf8,
    Utf16,
    Utf32,
}

impl PositionEncoding {
    /// The server's `positionEncoding`; absent means UTF-16 (LSP default).
    pub(crate) fn from_server(value: Option<&str>) -> Self {
        match value {
            Some("utf-8") => Self::Utf8,
            Some("utf-32") => Self::Utf32,
            Some(_) | None => Self::Utf16,
        }
    }

    fn units(self, character: char) -> usize {
        match self {
            Self::Utf8 => character.len_utf8(),
            Self::Utf16 => character.len_utf16(),
            Self::Utf32 => 1,
        }
    }
}

/// The lines of `text` without their terminators (`\n`, `\r\n`).
pub(crate) fn lines(text: &str) -> Vec<&str> {
    text.split('\n')
        .map(|line| line.strip_suffix('\r').unwrap_or(line))
        .collect()
}

/// The LSP position of 0-based `column` (in scalars) on 0-based `line`.
pub(crate) fn to_lsp(
    line_text: &str,
    line: u32,
    column: usize,
    encoding: PositionEncoding,
) -> Position {
    let units: usize = line_text
        .chars()
        .take(column)
        .map(|character| encoding.units(character))
        .sum();
    Position {
        line,
        character: u32::try_from(units).unwrap_or(u32::MAX),
    }
}

/// The 1-based point of an LSP position; a column past the line's end
/// clamps to the end (servers address line ends loosely).
pub(crate) fn from_lsp(
    text_lines: &[&str],
    position: Position,
    encoding: PositionEncoding,
) -> LspPoint {
    let line_text = text_lines
        .get(position.line as usize)
        .copied()
        .unwrap_or_default();
    let target = position.character as usize;
    let mut units = 0;
    let mut column = 0u32;
    for character in line_text.chars() {
        if units >= target {
            break;
        }
        units += encoding.units(character);
        column += 1;
    }
    LspPoint {
        line: position.line + 1,
        column: column + 1,
    }
}

pub(crate) fn span_from_lsp(
    text_lines: &[&str],
    range: Range,
    encoding: PositionEncoding,
) -> LspSpan {
    LspSpan {
        start: from_lsp(text_lines, range.start, encoding),
        end: from_lsp(text_lines, range.end, encoding),
    }
}

/// The 0-based scalar column of `symbol` (`name` or `name#N`) on 1-based
/// `line` (omp `resolveSymbolColumn`): exact matches first, then
/// case-insensitive ones; a bare identifier must sit on word boundaries.
pub(crate) fn symbol_column(
    path: &Path,
    text_lines: &[&str],
    line: u32,
    symbol: &str,
) -> Result<(usize, usize), LspError> {
    let line_text = line
        .checked_sub(1)
        .and_then(|index| text_lines.get(index as usize))
        .ok_or_else(|| LspError::LineOutOfRange {
            path: path.to_owned(),
            line,
            lines: text_lines.len(),
        })?;
    let (name, occurrence) = parse_symbol_spec(symbol);
    let mut matches = match_indexes(line_text, name, Case::Exact);
    if matches.is_empty() {
        matches = match_indexes(line_text, name, Case::Insensitive);
    }
    if matches.is_empty() {
        return Err(LspError::SymbolNotFound {
            symbol: name.to_owned(),
            line,
        });
    }
    let found = matches.len();
    matches
        .get(occurrence - 1)
        .map(|column| (*column, name.chars().count()))
        .ok_or(LspError::OccurrenceOutOfRange {
            symbol: name.to_owned(),
            line,
            occurrence,
            found,
        })
}

/// `name#N` (N >= 1) or a literal name; greedy, so `#name#2` is `#name`
/// occurrence 2.
fn parse_symbol_spec(spec: &str) -> (&str, usize) {
    if let Some((name, number)) = spec.rsplit_once('#') {
        if !name.is_empty()
            && !number.is_empty()
            && number.bytes().all(|byte| byte.is_ascii_digit())
        {
            return (name, number.parse::<usize>().unwrap_or(usize::MAX).max(1));
        }
    }
    (spec, 1)
}

#[derive(Clone, Copy)]
enum Case {
    Exact,
    Insensitive,
}

fn is_identifier_char(character: char) -> bool {
    character.is_ascii_alphanumeric() || character == '_' || character == '$'
}

/// Scalar indexes of non-overlapping matches of `needle` in `haystack`.
fn match_indexes(haystack: &str, needle: &str, case: Case) -> Vec<usize> {
    let fold = |text: &str| -> Vec<char> {
        match case {
            Case::Exact => text.chars().collect(),
            Case::Insensitive => text.chars().flat_map(char::to_lowercase).collect(),
        }
    };
    let hay = fold(haystack);
    let pin = fold(needle);
    if pin.is_empty() || pin.len() > hay.len() {
        return Vec::new();
    }
    let word = pin
        .first()
        .is_some_and(|first| first.is_ascii_alphabetic() || *first == '_' || *first == '$')
        && pin.iter().all(|character| is_identifier_char(*character));
    let mut indexes = Vec::new();
    let mut from = 0;
    while from + pin.len() <= hay.len() {
        if hay[from..from + pin.len()] != pin[..] {
            from += 1;
            continue;
        }
        let before = from.checked_sub(1).map(|index| hay[index]);
        let after = hay.get(from + pin.len()).copied();
        if word && (before.is_some_and(is_identifier_char) || after.is_some_and(is_identifier_char))
        {
            from += 1;
            continue;
        }
        indexes.push(from);
        from += pin.len();
    }
    indexes
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn symbol_specs_pick_word_bounded_occurrences() {
        let text = lines("let foo = foobar(foo);\n");
        let path = Path::new("/a.rs");
        assert_eq!(symbol_column(path, &text, 1, "foo"), Ok((4, 3)));
        assert_eq!(symbol_column(path, &text, 1, "foo#2"), Ok((17, 3)));
        assert_eq!(symbol_column(path, &text, 1, "FOOBAR"), Ok((10, 6)));
        assert_eq!(
            symbol_column(path, &text, 1, "foo#3"),
            Err(LspError::OccurrenceOutOfRange {
                symbol: "foo".to_owned(),
                line: 1,
                occurrence: 3,
                found: 2,
            })
        );
        assert_eq!(
            symbol_column(path, &text, 3, "foo"),
            Err(LspError::LineOutOfRange {
                path: path.to_owned(),
                line: 3,
                lines: 2,
            })
        );
        assert_eq!(
            symbol_column(path, &lines("#name#2 #name"), 1, "#name#2"),
            Ok((8, 5))
        );
    }

    #[test]
    fn encodings_round_trip_columns_past_wide_characters() {
        let line = "é😀x";
        for encoding in [
            PositionEncoding::Utf8,
            PositionEncoding::Utf16,
            PositionEncoding::Utf32,
        ] {
            let position = to_lsp(line, 0, 2, encoding);
            assert_eq!(
                from_lsp(&[line], position, encoding),
                LspPoint { line: 1, column: 3 }
            );
        }
        assert_eq!(to_lsp(line, 0, 2, PositionEncoding::Utf16).character, 3);
        assert_eq!(to_lsp(line, 0, 2, PositionEncoding::Utf8).character, 6);
    }
}
