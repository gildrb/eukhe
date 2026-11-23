//! The fullscreen transcript's text selection, view side: a mouse cell
//! becomes a transcript row, the rows go to the model
//! (`crate::selection`) as glyph widths, and the frame paints the range
//! the model shows. The model decides everything else.
//!
//! The selection holds on to the text it covers, not to screen rows or
//! row ids. The model's rows are the transcript's row ids plus an offset
//! (`Select::off`), and every frame finds the covered rows again in the
//! entry they came from: rows that arrive, leave or change above or below
//! them (streamed output, a thinking row, a tool card's result) move the
//! offset, so the selection moves with its text. Only a change of the
//! covered text itself, or of the width, is the model's `Changed`, which
//! clears it.

use std::time::Instant;

use crossterm::event::{
    KeyCode, KeyEvent, KeyEventKind, KeyModifiers, MouseButton, MouseEventKind,
};

use super::{AgentView, Blocks, Position, RowAt, ScrollAmount, ScrollRequest};
use crate::selection::{copy_text, highlight, Cell, Event, Pan, Reply, Row, Selection};
use crate::Line;

/// The model's row of transcript row 0 when the model opens: rows above
/// the selection can grow by this much before the model's rows would go
/// below 0 (far under the wire's largest Nat).
const ORIGIN: usize = 1 << 32;

/// Where the last frame put the transcript: its first row, how many
/// transcript rows it shows from screen row 0 on, and its width.
#[derive(Debug, Clone, Copy)]
pub(super) struct Shown {
    pub(super) top: RowAt,
    pub(super) rows: usize,
    pub(super) width: usize,
}

/// What a key does to the transcript selection.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SelectionKey {
    /// The app handles the key.
    Pass,
    /// Esc cleared a shown selection: the app must not see it.
    Spent,
    /// The copy key over a shown selection: copy this text, again. The
    /// selection stays.
    Copy(String),
}

/// Where the rows the model's state covers are, and the text they show.
#[derive(Debug)]
struct Anchor {
    /// The first covered row.
    at: RowAt,
    /// The covered rows' text, the last row's only through the last
    /// covered cell (what follows it on that row may still change).
    text: Vec<String>,
    /// The last covered cell's column.
    to: usize,
    /// The width the rows were laid out at.
    width: usize,
}

impl Anchor {
    /// The covered text of `rows` (the covered rows, first to last).
    fn covered(rows: &[Line], to: usize) -> Vec<String> {
        let last = rows.len().saturating_sub(1);
        rows.iter()
            .enumerate()
            .map(|(index, row)| {
                let text = crate::app::plain_row(row);
                if index == last {
                    through(&text, to)
                } else {
                    text
                }
            })
            .collect()
    }

    /// The covered text starts at `at`.
    fn starts_at(&self, blocks: &mut Blocks<'_>, at: RowAt) -> bool {
        let rows = blocks.collect(at, self.text.len());
        rows.len() == self.text.len() && Self::covered(&rows, self.to) == self.text
    }

    /// Where the covered text starts now: where it was, else the nearest
    /// row of the same entry it starts at. `None`: it is gone.
    fn find(&self, blocks: &mut Blocks<'_>) -> Option<RowAt> {
        if self.at.block >= blocks.count() {
            return None;
        }
        if self.starts_at(blocks, self.at) {
            return Some(self.at);
        }
        let mut rows: Vec<usize> = (0..blocks.len(self.at.block)).collect();
        rows.sort_by_key(|row| row.abs_diff(self.at.row));
        rows.into_iter()
            .map(|row| RowAt {
                block: self.at.block,
                row,
            })
            .find(|at| self.starts_at(blocks, *at))
    }
}

/// `text` through cell `to`: the glyphs that start at or before it.
fn through(text: &str, to: usize) -> String {
    use unicode_segmentation::UnicodeSegmentation;
    let mut out = String::new();
    let mut col = 0usize;
    let mut rest = text;
    while !rest.is_empty() && col <= to {
        if let Some(len) = crate::width::escape_len(rest) {
            rest = &rest[len..];
            continue;
        }
        let g = rest.graphemes(true).next().unwrap_or(rest);
        out.push_str(g);
        col += crate::width::grapheme_width(g);
        rest = &rest[g.len()..];
    }
    out
}

#[derive(Debug, Default)]
pub(super) struct Select {
    /// The model, opened at the first press.
    core: Option<Selection>,
    /// Press times count from here.
    epoch: Option<Instant>,
    /// The model's rows are transcript row ids plus this.
    off: usize,
    /// The range the model shows (the model's rows).
    range: Option<(Cell, Cell)>,
    /// The pressed cell while the button is held (the model's rows).
    press: Option<Cell>,
    /// The covered rows of the model's state: its range, else its press.
    anchor: Option<Anchor>,
    /// The window's first row while a press holds a following window
    /// still: new output does not move the rows under the pointer.
    hold: Option<RowAt>,
    /// The text the shown range's release copied.
    copied: Option<String>,
}

impl Select {
    fn step(&mut self, event: &Event<'_>) -> Option<Reply> {
        let reply = self.core.as_mut()?.step(event);
        if let Event::Key | Event::Esc | Event::Wheel | Event::Changed = event {
            self.press = None;
            self.hold = None;
        }
        if reply.sel != self.range {
            self.range = reply.sel;
            self.copied = None;
        }
        if self.span().is_none() {
            self.anchor = None;
        }
        Some(reply)
    }

    /// The model's cells its state covers: its range, else its press.
    fn span(&self) -> Option<(Cell, Cell)> {
        self.range.or(self.press.map(|at| (at, at)))
    }

    /// The transcript row id of the model's row `row`.
    fn id(&self, row: usize) -> Option<usize> {
        row.checked_sub(self.off)
    }

    /// The model's row of transcript row id `id`.
    fn row(&self, id: usize) -> usize {
        id + self.off
    }

    /// Note which rows the model's state covers now, and their text.
    fn anchor(&mut self, blocks: &mut Blocks<'_>, width: usize) {
        self.anchor = self.span().and_then(|(start, end)| {
            let first = self.id(start.row)?;
            let last = self.id(end.row)?;
            let at = blocks.down(RowAt { block: 0, row: 0 }, first);
            let rows = blocks.collect(at, last.saturating_sub(first) + 1);
            Some(Anchor {
                at,
                text: Anchor::covered(&rows, end.col),
                to: end.col,
                width,
            })
        });
    }

    /// Find the covered text in this frame's rows and move the model's
    /// rows onto it; text that is gone (or a new width) is `Changed`.
    fn follow(&mut self, blocks: &mut Blocks<'_>, width: usize) {
        let Some(anchor) = &self.anchor else {
            return;
        };
        let found = if anchor.width == width {
            anchor.find(blocks)
        } else {
            None
        };
        let off = found.zip(self.span()).and_then(|(at, (start, _))| {
            let off = start.row.checked_sub(blocks.id(at))?;
            Some((at, off))
        });
        match (off, self.anchor.as_mut()) {
            (Some((at, off)), Some(anchor)) => {
                anchor.at = at;
                self.off = off;
            }
            _ => {
                self.step(&Event::Changed);
            }
        }
    }

    /// The rows with ids `first..=last`.
    fn rows(blocks: &mut Blocks<'_>, first: usize, last: usize) -> Vec<Line> {
        blocks.rows_by_id(first, last.saturating_sub(first) + 1)
    }

    /// The window's first row while a press holds a following window.
    pub(super) fn hold(&self) -> Option<RowAt> {
        self.hold
    }

    /// Paint the shown range over `rows` (the frame's transcript rows,
    /// `shown.top` first), after following its text to where it is now.
    pub(super) fn paint(&mut self, blocks: &mut Blocks<'_>, shown: Shown, rows: &mut [Line]) {
        self.follow(blocks, shown.width);
        let Some((start, end)) = self.range else {
            return;
        };
        let (Some(first), Some(last)) = (self.id(start.row), self.id(end.row)) else {
            return;
        };
        let top = blocks.id(shown.top);
        for (offset, row) in rows.iter_mut().enumerate() {
            let id = top + offset;
            if (first..=last).contains(&id) {
                let from = if id == first { start.col } else { 0 };
                let to = (id == last).then_some(end.col);
                *row = highlight(row, from, to);
            }
        }
    }

    /// One left-button report at screen cell (`col`, `y`) over a window
    /// that follows the bottom when `follow`: the model's reply and the
    /// text it copies.
    fn mouse(
        &mut self,
        blocks: &mut Blocks<'_>,
        shown: Shown,
        follow: bool,
        kind: MouseEventKind,
        col: usize,
        y: usize,
    ) -> Option<(Reply, Option<String>)> {
        let top = blocks.id(shown.top);
        let out = match kind {
            MouseEventKind::Down(MouseButton::Left) => {
                // A press off the transcript (the dock, the toasts) is not
                // the selection's.
                if y >= shown.rows {
                    return None;
                }
                let line = Self::rows(blocks, top + y, top + y).pop()?;
                let epoch = *self.epoch.get_or_insert_with(Instant::now);
                let time = u64::try_from(epoch.elapsed().as_millis()).unwrap_or(u64::MAX);
                if self.core.is_none() {
                    self.core = Some(Selection::open());
                    self.off = ORIGIN;
                }
                let at = Cell {
                    row: self.row(top + y),
                    col,
                };
                let reply = self.step(&Event::Press {
                    at,
                    time,
                    row: &Row::of(&line),
                })?;
                self.press = Some(at);
                self.hold = follow.then_some(shown.top);
                (reply, None)
            }
            MouseEventKind::Drag(MouseButton::Left) => {
                let hi = top + shown.rows.checked_sub(1)?;
                let reply = self.step(&Event::Drag {
                    at: Cell {
                        row: self.row(top + y),
                        col,
                    },
                    lo: self.row(top),
                    hi: self.row(hi),
                })?;
                (reply, None)
            }
            MouseEventKind::Up(MouseButton::Left) => {
                let rows: Vec<Row> = match self
                    .range
                    .and_then(|(start, end)| Some((self.id(start.row)?, self.id(end.row)?)))
                {
                    Some((first, last)) => Self::rows(blocks, first, last)
                        .iter()
                        .map(Row::of)
                        .collect(),
                    None => Vec::new(),
                };
                self.press = None;
                self.hold = None;
                let reply = self.step(&Event::Release { rows: &rows })?;
                let copied = reply.copy.as_ref().map(|pieces| copy_text(pieces, &rows));
                if copied.is_some() {
                    self.copied.clone_from(&copied);
                }
                (reply, copied)
            }
            _ => return None,
        };
        self.anchor(blocks, shown.width);
        Some(out)
    }

    /// Move a held window one row toward `pan` (a drag past its edge).
    fn pan_hold(&mut self, blocks: &mut Blocks<'_>, pan: Pan) {
        if let Some(at) = self.hold {
            self.hold = Some(match pan {
                Pan::None => at,
                Pan::Up => blocks.up(at, 1),
                Pan::Down => blocks.down(at, 1),
            });
        }
    }
}

impl AgentView {
    /// One left-button report over the fullscreen chat (column and row
    /// on screen): the selection's model takes it; answers the text to
    /// copy when the model copies. A press holds a following window still
    /// until its release; a drag past the window's edge scrolls it one
    /// row (the held window now, else with the next frame).
    pub fn selection_mouse(
        &mut self,
        kind: MouseEventKind,
        column: u16,
        row: u16,
    ) -> Option<String> {
        if self.screen_mode != crate::screen_mode::ScreenMode::Fullscreen {
            return None;
        }
        let shown = self.viewport.shown?;
        let follow = self.viewport.position == Position::Follow;
        let mut select = std::mem::take(&mut self.viewport.select);
        let out = self.with_blocks(shown.width, |blocks| {
            let out = select.mouse(
                blocks,
                shown,
                follow,
                kind,
                usize::from(column),
                usize::from(row),
            );
            if let Some((reply, _)) = &out {
                select.pan_hold(blocks, reply.pan);
            }
            out
        });
        let held = select.hold.is_some();
        self.viewport.select = select;
        let (reply, copied) = out?;
        match reply.pan {
            Pan::None => {}
            _ if held => {}
            Pan::Up => self.scroll_viewport(ScrollRequest::Up(ScrollAmount::Rows(1))),
            Pan::Down => self.scroll_viewport(ScrollRequest::Down(ScrollAmount::Rows(1))),
        }
        copied
    }

    /// A key press reaches the selection first (once it is open): the
    /// copy key (`tui.editor.copySelection`) over a shown selection
    /// copies its text again and keeps it; every other key goes to the
    /// model, which clears the selection (Esc that cleared a shown one is
    /// spent there).
    pub fn selection_key(&mut self, key: &KeyEvent) -> SelectionKey {
        if key.kind == KeyEventKind::Release {
            return SelectionKey::Pass;
        }
        if let Some(text) = &self.viewport.select.copied {
            let copy = crate::keys::key_event_to_id(key).is_some_and(|id| {
                self.editor
                    .keybindings()
                    .matches(&id, "tui.editor.copySelection")
            });
            if copy {
                return SelectionKey::Copy(text.clone());
            }
        }
        let event = if key.code == KeyCode::Esc && key.modifiers == KeyModifiers::NONE {
            Event::Esc
        } else {
            Event::Key
        };
        match self.viewport.select.step(&event) {
            Some(reply) if reply.eat => SelectionKey::Spent,
            _ => SelectionKey::Pass,
        }
    }

    /// A wheel notch reaches the selection's model before it scrolls.
    pub fn selection_wheel(&mut self) {
        let _ = self.viewport.select.step(&Event::Wheel);
    }
}
