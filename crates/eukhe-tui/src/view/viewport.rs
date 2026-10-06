//! The fullscreen chat frame: exactly `height` rows, a transcript window
//! on top and the dock below it. The window shows the whole transcript
//! (splash, every entry, the tail) through a scroll position that
//! follows the bottom until the user scrolls up.
//!
//! The transcript is a list of blocks: block 0 is the splash, block
//! `i + 1` is chat entry `i`, and the last block is the tail (pending
//! bash cards, loaders). Settled blocks render once, when the window
//! first reaches them, and their rows are kept; unsettled entries and
//! the tail render every frame, as inline mode does. A frame walks only
//! the blocks the window and its "more below" count need.

use super::frame::{ChatFrame, FrameStart};
use super::AgentView;
use crate::inline_term::LiveCursor;
use crate::screen_mode::WheelDirection;
use crate::theme::ThemeColor;
use crate::Line;

/// How far one scroll request moves the window.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScrollAmount {
    Rows(usize),
    /// The transcript rows a scrolled window shows (the indicator row
    /// takes one) minus one, so one row stays in view across a page.
    Page,
}

/// One scroll request against the fullscreen transcript window.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScrollRequest {
    Up(ScrollAmount),
    Down(ScrollAmount),
    /// The first transcript row.
    Top,
    /// The bottom, following new output.
    Bottom,
}

impl ScrollRequest {
    /// One wheel notch.
    #[must_use]
    pub fn wheel(direction: WheelDirection) -> Self {
        let rows = ScrollAmount::Rows(crate::screen_mode::WHEEL_ROWS);
        match direction {
            WheelDirection::Up => ScrollRequest::Up(rows),
            WheelDirection::Down => ScrollRequest::Down(rows),
        }
    }
}

/// A transcript row: a block and a row within it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct RowAt {
    block: usize,
    row: usize,
}

/// Where the window is.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
enum Position {
    /// The window shows the last rows and moves with new output.
    #[default]
    Follow,
    /// The window's first row; new output below does not move it.
    Anchored(RowAt),
}

/// The fullscreen window state an [`AgentView`] keeps between frames.
#[derive(Debug, Default)]
pub(crate) struct Viewport {
    position: Position,
    /// Requests since the last frame; the frame applies them against
    /// its own geometry.
    pending: Vec<ScrollRequest>,
    /// Rows of the settled blocks `0..=committed`, filled on first use.
    settled: Vec<Option<Vec<Line>>>,
}

/// The blocks of one frame.
struct Blocks<'a> {
    view: &'a AgentView,
    width: usize,
    settled: &'a mut Vec<Option<Vec<Line>>>,
    /// The unsettled entries, then the tail.
    live: Vec<Vec<Line>>,
}

impl Blocks<'_> {
    fn count(&self) -> usize {
        self.settled.len() + self.live.len()
    }

    fn rows(&mut self, block: usize) -> &[Line] {
        let settled = self.settled.len();
        if block >= settled {
            return &self.live[block - settled];
        }
        let (view, width) = (self.view, self.width);
        self.settled[block].get_or_insert_with(|| match block.checked_sub(1) {
            Some(index) => view.render_entry_at(index, width),
            None => view.splash_rows(width),
        })
    }

    fn len(&mut self, block: usize) -> usize {
        self.rows(block).len()
    }

    /// One past the last row.
    fn end(&self) -> RowAt {
        RowAt {
            block: self.count(),
            row: 0,
        }
    }

    /// Rows from `at` to the end.
    fn rows_from(&mut self, at: RowAt) -> usize {
        let mut total = 0;
        for block in at.block..self.count() {
            total += self.len(block);
        }
        total.saturating_sub(at.row)
    }

    /// The row `n` rows above `at`, clamped at the first row.
    fn up(&mut self, mut at: RowAt, mut n: usize) -> RowAt {
        loop {
            if n <= at.row {
                at.row -= n;
                return at;
            }
            n -= at.row;
            loop {
                if at.block == 0 {
                    return RowAt { block: 0, row: 0 };
                }
                at.block -= 1;
                let len = self.len(at.block);
                if len > 0 {
                    at.row = len - 1;
                    break;
                }
            }
            n -= 1;
        }
    }

    /// The row `n` rows below `at`, clamped at the end.
    fn down(&mut self, mut at: RowAt, mut n: usize) -> RowAt {
        while at.block < self.count() {
            let remaining = self.len(at.block).saturating_sub(at.row);
            if n < remaining {
                at.row += n;
                return at;
            }
            n -= remaining;
            at.block += 1;
            at.row = 0;
        }
        self.end()
    }

    /// Up to `count` rows from `at` on.
    fn collect(&mut self, mut at: RowAt, count: usize) -> Vec<Line> {
        let mut out = Vec::with_capacity(count);
        while out.len() < count && at.block < self.count() {
            let rows = self.rows(at.block);
            let from = at.row.min(rows.len());
            let take = (count - out.len()).min(rows.len() - from);
            out.extend_from_slice(&rows[from..from + take]);
            at.block += 1;
            at.row = 0;
        }
        out
    }

    /// Apply one request to `position` for a window of `window` rows.
    fn scroll(&mut self, position: Position, request: ScrollRequest, window: usize) -> Position {
        let page = window.saturating_sub(2).max(1);
        let rows = |amount: ScrollAmount| match amount {
            ScrollAmount::Rows(rows) => rows,
            ScrollAmount::Page => page,
        };
        match (request, position) {
            (ScrollRequest::Up(amount), Position::Follow) => {
                let top = self.up(self.end(), window);
                Position::Anchored(self.up(top, rows(amount)))
            }
            (ScrollRequest::Up(amount), Position::Anchored(at)) => {
                Position::Anchored(self.up(at, rows(amount)))
            }
            (ScrollRequest::Down(_), Position::Follow) | (ScrollRequest::Bottom, _) => {
                Position::Follow
            }
            (ScrollRequest::Down(amount), Position::Anchored(at)) => {
                Position::Anchored(self.down(at, rows(amount)))
            }
            (ScrollRequest::Top, _) => Position::Anchored(RowAt { block: 0, row: 0 }),
        }
    }
}

impl AgentView {
    /// Queue a scroll of the fullscreen transcript window; the next
    /// fullscreen frame applies it. Inline, nothing scrolls.
    pub fn scroll_viewport(&mut self, request: ScrollRequest) {
        if self.screen_mode == crate::screen_mode::ScreenMode::Fullscreen {
            self.viewport.pending.push(request);
        }
    }

    /// Compose the fullscreen frame for a `width` x `height` terminal:
    /// exactly `height` live rows and no history. The dock is laid out
    /// first; the toasts sit above it; the transcript window takes the
    /// rest. A replay frame asks the terminal for a full repaint.
    pub fn compose_fullscreen(&mut self, width: usize, height: usize) -> ChatFrame {
        let start = self.begin_frame(width);
        if start != FrameStart::Continue {
            self.viewport.settled.clear();
        }
        while self.committed < self.chat.len() && self.entry_settled(self.committed) {
            self.committed += 1;
        }
        self.viewport
            .settled
            .resize_with(self.committed + 1, || None);
        let replay = start == FrameStart::Replay;
        if let Some(screen) = self.onboarding.as_mut() {
            let kb = self.editor.keybindings();
            let mut live = screen.render(&self.theme, width, height, kb);
            crate::screen_mode::fill_height(&mut live, height);
            return ChatFrame {
                replay,
                history: Vec::new(),
                live,
                cursor: None,
            };
        }
        let (mut dock, editor_focused) = self.compose_dock(width);
        let clipped = dock.len().saturating_sub(height);
        dock.drain(..clipped);
        let mut toasts = self.toast_rows(width);
        toasts.truncate(height - dock.len());
        let window = height - dock.len() - toasts.len();
        let mut live = self.transcript_window(width, window);
        let cursor = self
            .dock_cursor
            .filter(|_| editor_focused)
            .and_then(|(row, col)| row.checked_sub(clipped).map(|row| (row, col)))
            .map(|(row, col)| LiveCursor {
                row: window + toasts.len() + row,
                col,
            });
        live.extend(toasts);
        live.extend(dock);
        ChatFrame {
            replay,
            history: Vec::new(),
            live,
            cursor,
        }
    }

    /// The transcript window: exactly `window` rows.
    fn transcript_window(&mut self, width: usize, window: usize) -> Vec<Line> {
        let mut live: Vec<Vec<Line>> = (self.committed..self.chat.len())
            .map(|index| self.render_entry_at(index, width))
            .collect();
        live.push(self.render_transcript_tail(width));
        let mut settled = std::mem::take(&mut self.viewport.settled);
        let pending = std::mem::take(&mut self.viewport.pending);
        let mut position = self.viewport.position;
        let mut blocks = Blocks {
            view: self,
            width,
            settled: &mut settled,
            live,
        };
        for request in pending {
            position = blocks.scroll(position, request, window);
        }
        if let Position::Anchored(at) = position {
            if blocks.rows_from(at) <= window {
                position = Position::Follow;
            }
        }
        let mut rows = match position {
            Position::Anchored(_) | Position::Follow if window == 0 => Vec::new(),
            Position::Follow => {
                let top = blocks.up(blocks.end(), window);
                blocks.collect(top, window)
            }
            Position::Anchored(at) => {
                let content = window - 1;
                let mut rows = blocks.collect(at, content);
                let below = blocks.rows_from(at) - content;
                rows.push(self.more_below_row(below, width));
                rows
            }
        };
        crate::screen_mode::fill_height(&mut rows, window);
        self.viewport.settled = settled;
        self.viewport.position = position;
        rows
    }

    /// The dim `v N more below` row under a scrolled-up window.
    fn more_below_row(&self, below: usize, width: usize) -> Line {
        use std::fmt::Write as _;
        let mut text = format!("v {below} more below");
        if let Some(key) = self.editor.keybindings().first_key("tui.viewport.bottom") {
            let _ = write!(
                text,
                " - {} to follow",
                crate::keybindings::format_key_text(&key)
            );
        }
        vec![self.theme.fg(
            ThemeColor::Dim,
            crate::width::truncate_to_width(&text, width, ""),
        )]
    }
}

#[cfg(test)]
#[path = "viewport_tests.rs"]
mod tests;
