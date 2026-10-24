//! The fullscreen chat's text selection, Rust side. In fullscreen the
//! terminal reports every press, drag and release to eukhe
//! (`screen_mode.rs` turns on `?1002h`), so its own selection cannot work
//! and eukhe selects instead. What a selection is -- where it starts and
//! ends, a double or triple click, when to scroll, which text a release
//! copies, what clears it -- is the Bend model `bend/selection.bend`,
//! reached through the stepper `bend/ffi_selection.bend`. This module
//! only carries bytes: it writes the model's events, reads its replies,
//! turns a transcript row into the glyph widths the model reads, paints
//! the range the model shows, and joins the copied pieces into text.

use eukhe_bend::wire::{Reader, WireError, Writer, NAT_MAX};
use eukhe_bend::{expect_core, Entry, Stepper};

use crate::soft_wrap::RowWrap;
use crate::style::{Modifier, Style};
use crate::{Line, Span};

/// A cell: a transcript row id (rows numbered top to bottom from the
/// transcript's first row) and a screen column.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Cell {
    pub row: usize,
    pub col: usize,
}

/// One transcript row as the model reads it: its glyphs (the text of
/// each, for the copy) and how it sits in a soft-wrapped block.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Row {
    wrap: RowWrap,
    /// Each glyph's text and its width on the wire: 0 for a one-cell
    /// blank, else the cells it takes.
    glyphs: Vec<(String, usize)>,
}

impl Row {
    /// The row a rendered transcript line shows.
    pub(crate) fn of(line: &Line) -> Row {
        use unicode_segmentation::UnicodeSegmentation;
        let text = crate::app::plain_row(line);
        let mut glyphs: Vec<(String, usize)> = Vec::new();
        let mut rest = text.as_str();
        while !rest.is_empty() {
            if let Some(len) = crate::width::escape_len(rest) {
                rest = &rest[len..];
                continue;
            }
            let g = rest.graphemes(true).next().unwrap_or(rest);
            rest = &rest[g.len()..];
            match crate::width::grapheme_width(g) {
                // A zero-width cluster rides with the glyph before it.
                0 => {
                    if let Some((last, _)) = glyphs.last_mut() {
                        last.push_str(g);
                    }
                }
                1 if g == " " => glyphs.push((g.to_string(), 0)),
                w => glyphs.push((g.to_string(), w)),
            }
        }
        Row {
            wrap: crate::soft_wrap::row_wrap(line),
            glyphs,
        }
    }

    fn write(&self, w: &mut Writer) {
        w.tag(match self.wrap {
            RowWrap::Single => 0,
            RowWrap::Head => 1,
            RowWrap::Continuation => 2,
        });
        write_glyphs(w, &self.glyphs);
    }
}

fn write_glyphs(w: &mut Writer, glyphs: &[(String, usize)]) {
    w.count(glyphs.len());
    for (_, width) in glyphs {
        w.nat(nat(*width));
    }
}

fn nat(n: usize) -> u64 {
    u64::try_from(n).unwrap_or(NAT_MAX).min(NAT_MAX)
}

fn write_cell(w: &mut Writer, at: Cell) {
    w.nat(nat(at.row)).nat(nat(at.col));
}

/// One input of the selection.
#[derive(Debug)]
pub(crate) enum Event<'a> {
    /// The left button went down on `at` (`time` in ms, `row` the row
    /// under it).
    Press {
        at: Cell,
        time: u64,
        row: &'a Row,
    },
    /// The button moved to `at` while held; `lo..=hi` the transcript rows
    /// on screen.
    Drag {
        at: Cell,
        lo: usize,
        hi: usize,
    },
    /// The button went up; `rows` the rows of the shown range, from its
    /// first row on.
    Release {
        rows: &'a [Row],
    },
    Key,
    Esc,
    Wheel,
    /// The rows under the shown range changed.
    Changed,
}

impl Event<'_> {
    fn write(&self, w: &mut Writer) {
        match self {
            Event::Press { at, time, row } => {
                w.tag(0);
                write_cell(w, *at);
                w.nat((*time).min(NAT_MAX));
                write_glyphs(w, &row.glyphs);
            }
            Event::Drag { at, lo, hi } => {
                w.tag(1);
                write_cell(w, *at);
                w.nat(nat(*lo)).nat(nat(*hi));
            }
            Event::Release { rows } => {
                w.tag(2).count(rows.len());
                for row in *rows {
                    row.write(w);
                }
            }
            Event::Key => {
                w.tag(3);
            }
            Event::Esc => {
                w.tag(4);
            }
            Event::Wheel => {
                w.tag(5);
            }
            Event::Changed => {
                w.tag(6);
            }
        }
    }
}

/// The scroll step a drag asks for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Pan {
    None,
    Up,
    Down,
}

/// Glyphs `from..to` of release row `row`, after a newline when `nl`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Piece {
    pub row: usize,
    pub from: usize,
    pub to: usize,
    pub nl: bool,
}

/// The model's answer to one input.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Reply {
    /// The range to show, start and end cells both in.
    pub sel: Option<(Cell, Cell)>,
    /// The pieces to copy.
    pub copy: Option<Vec<Piece>>,
    pub pan: Pan,
    /// The input is spent (the app does not see it).
    pub eat: bool,
}

fn read_cell(r: &mut Reader<'_>) -> Result<Cell, WireError> {
    Ok(Cell {
        row: r.count()?,
        col: r.count()?,
    })
}

fn read_reply(reply: &str) -> Result<Reply, WireError> {
    let mut r = Reader::reply(reply)?;
    let sel = if r.maybe()? {
        Some((read_cell(&mut r)?, read_cell(&mut r)?))
    } else {
        None
    };
    let copy = if r.maybe()? {
        let n = r.count()?;
        let mut pieces = Vec::with_capacity(n.min(4096));
        for _ in 0..n {
            pieces.push(Piece {
                row: r.count()?,
                from: r.count()?,
                to: r.count()?,
                nl: r.bool()?,
            });
        }
        Some(pieces)
    } else {
        None
    };
    let pan = match r.tag_of(3, "a Pan tag")? {
        0 => Pan::None,
        1 => Pan::Up,
        _ => Pan::Down,
    };
    let eat = r.bool()?;
    r.end()?;
    Ok(Reply {
        sel,
        copy,
        pan,
        eat,
    })
}

/// The selection's state, kept in the Bend heap.
#[derive(Debug)]
pub(crate) struct Selection {
    stepper: Stepper,
}

impl Selection {
    /// Nothing selected.
    pub(crate) fn open() -> Selection {
        let (stepper, reply) = expect_core(Entry::Selection, Stepper::open(Entry::Selection, ""));
        expect_core(Entry::Selection, read_reply(&reply));
        Selection { stepper }
    }

    /// Feed one input; the model's answer.
    pub(crate) fn step(&mut self, event: &Event<'_>) -> Reply {
        let mut w = Writer::new();
        event.write(&mut w);
        let input = expect_core(Entry::Selection, w.finish());
        let reply = expect_core(Entry::Selection, self.stepper.step(&input));
        expect_core(Entry::Selection, read_reply(&reply))
    }
}

/// The text of `pieces` over the release rows `rows`.
pub(crate) fn copy_text(pieces: &[Piece], rows: &[Row]) -> String {
    let mut text = String::new();
    for piece in pieces {
        if piece.nl {
            text.push('\n');
        }
        if let Some(row) = rows.get(piece.row) {
            let to = piece.to.min(row.glyphs.len());
            for (glyph, _) in row.glyphs.get(piece.from.min(to)..to).unwrap_or_default() {
                text.push_str(glyph);
            }
        }
    }
    text
}

/// `line` with the cells `from..=to` (`to` `None`: to the row's end)
/// shown reversed; zero-width escapes stay where they are.
pub(crate) fn highlight(line: &Line, from: usize, to: Option<usize>) -> Line {
    use unicode_segmentation::UnicodeSegmentation;
    let mark = Style::new().add_modifier(Modifier::REVERSED);
    let mut out: Line = Vec::with_capacity(line.len() + 2);
    let push = |out: &mut Line, style: Style, text: &str| match out.last_mut() {
        Some(last) if last.style == style && crate::width::escape_len(&last.content).is_none() => {
            last.content.push_str(text);
        }
        _ => out.push(Span::styled(text, style)),
    };
    let mut col = 0usize;
    for span in line {
        let mut rest = span.content.as_str();
        while !rest.is_empty() {
            if let Some(len) = crate::width::escape_len(rest) {
                out.push(Span::styled(&rest[..len], span.style));
                rest = &rest[len..];
                continue;
            }
            let g = rest.graphemes(true).next().unwrap_or(rest);
            let w = crate::width::grapheme_width(g);
            let last = col + w.max(1) - 1;
            let inside = last >= from && to.is_none_or(|to| col <= to);
            let style = if inside {
                span.style.patch(mark)
            } else {
                span.style
            };
            push(&mut out, style, g);
            col += w;
            rest = &rest[g.len()..];
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::{copy_text, highlight, Cell, Event, Pan, Row, Selection};
    use crate::style::Modifier;
    use crate::Span;

    fn row(text: &str) -> Row {
        Row::of(&vec![Span::raw(text)])
    }

    /// The compiled core is reached: a drag from the second cell of one
    /// row to the third of the next copies exactly those cells, and Esc
    /// clears the shown range (and is spent).
    #[test]
    fn a_drag_reaches_the_compiled_model() {
        let rows = [row("hello world"), row("second row")];
        let mut s = Selection::open();
        let at = |row, col| Cell { row, col };
        let press = s.step(&Event::Press {
            at: at(10, 1),
            time: 0,
            row: &rows[0],
        });
        assert_eq!(press.sel, None);
        let drag = s.step(&Event::Drag {
            at: at(11, 2),
            lo: 10,
            hi: 20,
        });
        assert_eq!(drag.sel, Some((at(10, 1), at(11, 2))));
        assert_eq!(drag.pan, Pan::None);
        let release = s.step(&Event::Release { rows: &rows });
        let pieces = release.copy.expect("a release copies");
        assert_eq!(copy_text(&pieces, &rows), "ello world\nsec");
        let esc = s.step(&Event::Esc);
        assert_eq!((esc.sel, esc.eat), (None, true));
        assert!(!s.step(&Event::Esc).eat);
    }

    #[test]
    fn wide_glyphs_and_blanks_cross_as_widths() {
        let r = row("a 你");
        assert_eq!(
            r.glyphs.iter().map(|(_, w)| *w).collect::<Vec<_>>(),
            [1, 0, 2]
        );
        let lit = highlight(&vec![Span::raw("ab你c")], 1, Some(2));
        let reversed: String = lit
            .iter()
            .filter(|s| s.style.add_modifier.contains(Modifier::REVERSED))
            .map(|s| s.content.as_str())
            .collect();
        assert_eq!(reversed, "b你");
    }
}
