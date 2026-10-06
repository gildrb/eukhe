//! Soft-wrapped blocks: one logical line laid out over several rows that
//! the inline terminal writes back to back with autowrap on, so the
//! terminal records the wrap itself. Selecting, copying, and URL
//! detection then see one unbroken line (a sign-in link stays whole).
//!
//! A block's rows carry a zero-width marker span at their head; the
//! inline writer reads it and strips it before output, and the plain-text
//! dumps strip it too.

use unicode_segmentation::UnicodeSegmentation;

use crate::style::Style;
use crate::{Line, Span};

/// Marks the first row of a block. A private OSC string: zero-width for
/// every width measurement, and never written to the terminal.
const HEAD: &str = "\x1b]eukhe;wrap-head\x07";
/// Marks every later row of a block.
const CONTINUATION: &str = "\x1b]eukhe;wrap-next\x07";

/// How a row sits in a soft-wrapped block.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RowWrap {
    /// A row of its own.
    Single,
    /// The first row of a block.
    Head,
    /// A row that continues the row above it.
    Continuation,
}

/// Whether a block's text is an OSC 8 hyperlink to the whole text.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Link {
    Plain,
    Hyperlink,
}

/// Lay `text` (plain, control-free) out as a block at `width`: `indent`
/// unstyled, then the text in `style`. Each row is filled the way the
/// terminal's autowrap fills it -- to the last column, or one short when
/// a wide grapheme would straddle the edge -- so the rows the terminal
/// shows are exactly the rows returned. Text that fits one row is a
/// plain single row. A hyperlinked block links every row's piece to the
/// whole text.
pub(crate) fn rows(indent: &str, text: &str, style: Style, width: usize, link: Link) -> Vec<Line> {
    let width = width.max(1);
    let mut pieces: Vec<String> = Vec::new();
    let mut piece = String::new();
    let mut used = crate::width::str_width(indent).min(width);
    for grapheme in text.graphemes(true) {
        let cells = crate::width::grapheme_width(grapheme);
        if used + cells > width && used > 0 {
            pieces.push(std::mem::take(&mut piece));
            used = 0;
        }
        piece.push_str(grapheme);
        used += cells;
    }
    pieces.push(piece);
    let styled = |piece: String| match link {
        Link::Plain => Span::styled(piece, style),
        Link::Hyperlink => Span::styled(
            format!(
                "{}{piece}{}",
                crate::hyperlinks::osc8_open(text),
                crate::hyperlinks::OSC8_CLOSE
            ),
            style,
        ),
    };
    let single = pieces.len() == 1;
    pieces
        .into_iter()
        .enumerate()
        .map(|(index, piece)| match (index, single) {
            (0, true) => vec![Span::raw(indent), styled(piece)],
            (0, false) => vec![Span::raw(HEAD), Span::raw(indent), styled(piece)],
            (_, _) => vec![Span::raw(CONTINUATION), styled(piece)],
        })
        .collect()
}

/// Where `row` sits in a block, read from its head marker.
pub(crate) fn row_wrap(row: &[Span]) -> RowWrap {
    match row.first().map(|span| span.content.as_str()) {
        Some(HEAD) => RowWrap::Head,
        Some(CONTINUATION) => RowWrap::Continuation,
        Some(_) | None => RowWrap::Single,
    }
}

/// The row without its marker span.
pub(crate) fn content(row: &[Span]) -> &[Span] {
    match row_wrap(row) {
        RowWrap::Single => row,
        RowWrap::Head | RowWrap::Continuation => &row[1..],
    }
}

/// Plain rows joined into the logical lines they show: every
/// continuation row appended to the row above it.
#[cfg(test)]
pub(crate) fn logical_lines(rows: &[Line]) -> Vec<String> {
    let mut lines: Vec<String> = Vec::new();
    for row in rows {
        let text = crate::app::plain_row(row);
        match (row_wrap(row), lines.last_mut()) {
            (RowWrap::Continuation, Some(last)) => last.push_str(&text),
            (RowWrap::Continuation | RowWrap::Single | RowWrap::Head, _) => lines.push(text),
        }
    }
    lines
}

#[cfg(test)]
mod tests {
    use super::*;

    fn plain(rows: &[Line]) -> Vec<String> {
        rows.iter().map(crate::app::plain_row).collect()
    }

    #[test]
    fn a_long_text_fills_every_row_but_the_last() {
        let rows = rows(" ", "abcdefghij", Style::default(), 4, Link::Plain);
        assert_eq!(plain(&rows), [" abc", "defg", "hij"]);
        assert_eq!(
            rows.iter().map(|row| row_wrap(row)).collect::<Vec<_>>(),
            [RowWrap::Head, RowWrap::Continuation, RowWrap::Continuation]
        );
        assert_eq!(logical_lines(&rows), [" abcdefghij"]);
    }

    #[test]
    fn a_text_that_fits_is_one_plain_row() {
        let rows = rows(" ", "abc", Style::default(), 4, Link::Plain);
        assert_eq!(plain(&rows), [" abc"]);
        assert_eq!(row_wrap(&rows[0]), RowWrap::Single);
    }

    /// A wide grapheme that would straddle the edge starts the next row,
    /// where the terminal's autowrap puts it.
    #[test]
    fn a_wide_grapheme_never_straddles_the_edge() {
        let rows = rows("", "ab\u{4e16}c", Style::default(), 3, Link::Plain);
        assert_eq!(plain(&rows), ["ab", "\u{4e16}c"]);
    }

    #[test]
    fn every_hyperlinked_piece_links_the_whole_text() {
        let rows = rows("", "abcdef", Style::default(), 3, Link::Hyperlink);
        let open = crate::hyperlinks::osc8_open("abcdef");
        assert_eq!(
            content(&rows[0])[1].content,
            format!("{open}abc\x1b]8;;\x1b\\")
        );
        assert_eq!(
            content(&rows[1])[0].content,
            format!("{open}def\x1b]8;;\x1b\\")
        );
    }
}
