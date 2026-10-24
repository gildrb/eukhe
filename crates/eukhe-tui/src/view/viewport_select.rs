//! The fullscreen transcript's text selection, view side: a mouse cell
//! becomes a transcript row id (rows counted from the transcript's first
//! row, so a scroll keeps them), the rows go to the model
//! (`crate::selection`) as glyph widths, and the frame paints the range
//! the model shows. The model decides everything else.

use std::time::Instant;

use crossterm::event::{
    KeyCode, KeyEvent, KeyEventKind, KeyModifiers, MouseButton, MouseEventKind,
};

use super::{AgentView, Blocks, RowAt, ScrollAmount, ScrollRequest};
use crate::selection::{copy_text, highlight, Cell, Event, Pan, Reply, Row, Selection};
use crate::Line;

/// Where the last frame put the transcript: its first row, how many
/// transcript rows it shows from screen row 0 on, and its width.
#[derive(Debug, Clone, Copy)]
pub(super) struct Shown {
    pub(super) top: RowAt,
    pub(super) rows: usize,
    pub(super) width: usize,
}

#[derive(Debug, Default)]
pub(super) struct Select {
    /// The model, opened at the first press.
    core: Option<Selection>,
    /// Press times count from here.
    epoch: Option<Instant>,
    /// The range the model shows.
    range: Option<(Cell, Cell)>,
    /// The text of the range's rows and the width when it was first
    /// painted: a change is the model's `Changed` input.
    seen: Option<(Vec<String>, usize)>,
}

impl Select {
    fn take(&mut self, reply: &Reply) {
        if reply.sel != self.range {
            self.range = reply.sel;
            self.seen = None;
        }
    }

    fn step(&mut self, event: &Event<'_>) -> Option<Reply> {
        let reply = self.core.as_mut()?.step(event);
        self.take(&reply);
        Some(reply)
    }

    /// The rows with ids `first..=last`.
    fn rows(blocks: &mut Blocks<'_>, first: usize, last: usize) -> Vec<Line> {
        blocks.rows_by_id(first, last.saturating_sub(first) + 1)
    }

    /// Paint the shown range over `rows` (the frame's transcript rows,
    /// `shown.top` first); a change of the text under it goes to the
    /// model first.
    pub(super) fn paint(&mut self, blocks: &mut Blocks<'_>, shown: Shown, rows: &mut [Line]) {
        let Some((start, end)) = self.range else {
            return;
        };
        let text: Vec<String> = Self::rows(blocks, start.row, end.row)
            .iter()
            .map(crate::app::plain_row)
            .collect();
        let changed = match &self.seen {
            None => false,
            Some((seen, width)) => *seen != text || *width != shown.width,
        };
        if self.seen.is_none() {
            self.seen = Some((text, shown.width));
        } else if changed {
            self.step(&Event::Changed);
        }
        let Some((start, end)) = self.range else {
            return;
        };
        let top = blocks.id(shown.top);
        for (offset, row) in rows.iter_mut().enumerate() {
            let id = top + offset;
            if (start.row..=end.row).contains(&id) {
                let from = if id == start.row { start.col } else { 0 };
                let to = (id == end.row).then_some(end.col);
                *row = highlight(row, from, to);
            }
        }
    }

    /// One left-button report at screen cell (`col`, `y`): the model's
    /// reply and the text it copies.
    fn mouse(
        &mut self,
        blocks: &mut Blocks<'_>,
        shown: Shown,
        kind: MouseEventKind,
        col: usize,
        y: usize,
    ) -> Option<(Reply, Option<String>)> {
        let top = blocks.id(shown.top);
        match kind {
            MouseEventKind::Down(MouseButton::Left) => {
                // A press off the transcript (the dock, the toasts) is not
                // the selection's.
                if y >= shown.rows {
                    return None;
                }
                let line = Self::rows(blocks, top + y, top + y).pop()?;
                let epoch = *self.epoch.get_or_insert_with(Instant::now);
                let time = u64::try_from(epoch.elapsed().as_millis()).unwrap_or(u64::MAX);
                self.core.get_or_insert_with(Selection::open);
                let reply = self.step(&Event::Press {
                    at: Cell { row: top + y, col },
                    time,
                    row: &Row::of(&line),
                })?;
                Some((reply, None))
            }
            MouseEventKind::Drag(MouseButton::Left) => {
                let hi = top + shown.rows.checked_sub(1)?;
                let reply = self.step(&Event::Drag {
                    at: Cell { row: top + y, col },
                    lo: top,
                    hi,
                })?;
                Some((reply, None))
            }
            MouseEventKind::Up(MouseButton::Left) => {
                let rows: Vec<Row> = match self.range {
                    Some((start, end)) => Self::rows(blocks, start.row, end.row)
                        .iter()
                        .map(Row::of)
                        .collect(),
                    None => Vec::new(),
                };
                let reply = self.step(&Event::Release { rows: &rows })?;
                let copied = reply.copy.as_ref().map(|pieces| copy_text(pieces, &rows));
                Some((reply, copied))
            }
            _ => None,
        }
    }
}

impl AgentView {
    /// One left-button report over the fullscreen chat (column and row
    /// on screen): the selection's model takes it; answers the text to
    /// copy when the model copies. Its scroll step is queued for the next
    /// frame.
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
        let mut select = std::mem::take(&mut self.viewport.select);
        let out = self.with_blocks(shown.width, |blocks| {
            select.mouse(blocks, shown, kind, usize::from(column), usize::from(row))
        });
        self.viewport.select = select;
        let (reply, copied) = out?;
        match reply.pan {
            Pan::None => {}
            Pan::Up => self.scroll_viewport(ScrollRequest::Up(ScrollAmount::Rows(1))),
            Pan::Down => self.scroll_viewport(ScrollRequest::Down(ScrollAmount::Rows(1))),
        }
        copied
    }

    /// A key press reaches the selection's model first (once it is
    /// open): true when the model spends it (Esc that cleared a shown
    /// selection), so the app must not see it.
    pub fn selection_key(&mut self, key: &KeyEvent) -> bool {
        if key.kind == KeyEventKind::Release {
            return false;
        }
        let event = if key.code == KeyCode::Esc && key.modifiers == KeyModifiers::NONE {
            Event::Esc
        } else {
            Event::Key
        };
        self.viewport
            .select
            .step(&event)
            .is_some_and(|reply| reply.eat)
    }

    /// A wheel notch reaches the selection's model before it scrolls.
    pub fn selection_wheel(&mut self) {
        let _ = self.viewport.select.step(&Event::Wheel);
    }
}
