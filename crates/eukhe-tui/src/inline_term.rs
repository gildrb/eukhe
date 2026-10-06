//! The inline terminal: the one writer that paints the CLI into the
//! normal screen. No alternate screen, no mouse capture.
//!
//! The screen has two parts:
//!
//! - history: rows written once into native scrollback, never touched
//!   again;
//! - the live area: the rows at the bottom of the output (streaming
//!   reply, loaders, pickers, editor, footer), redrawn in place each
//!   frame.
//!
//! The writer moves the cursor only relative to the live area (cursor
//! up/down, carriage return), so it never needs the absolute cursor
//! position. Every frame goes out as one write inside a synchronized
//! update with autowrap off: a row wider than the screen clips instead
//! of wrapping, so the row count on screen always equals the row count
//! the writer tracks.

use std::io::{self, Write};
use std::sync::atomic::{AtomicUsize, Ordering};

use crate::Line;

/// Rows between the cursor and the last live row of the live area on
/// screen, or [`NO_LIVE_AREA`]. Process-global so the crash restore
/// ([`park_below_live`]) can put the shell prompt below the live area
/// without the writer that drew it.
static LIVE_ROWS_BELOW_CURSOR: AtomicUsize = AtomicUsize::new(NO_LIVE_AREA);
const NO_LIVE_AREA: usize = usize::MAX;

/// Move the cursor to the line below the live area last painted, if one
/// is still on screen. The best-effort exit restore runs this when the
/// owning [`InlineTerminal`] is gone (panic, force quit, fatal error).
pub(crate) fn park_below_live(out: &mut impl Write) {
    let below = LIVE_ROWS_BELOW_CURSOR.swap(NO_LIVE_AREA, Ordering::SeqCst);
    if below == NO_LIVE_AREA {
        return;
    }
    let move_down = if below > 0 {
        format!("\x1b[{below}B\r\n")
    } else {
        "\r\n".to_string()
    };
    let _ = out.write_all(move_down.as_bytes());
}

/// Drop the live-area position [`park_below_live`] would move below:
/// the screen it was painted on is gone (an alternate-screen switch).
pub(crate) fn forget_live_area() {
    LIVE_ROWS_BELOW_CURSOR.store(NO_LIVE_AREA, Ordering::SeqCst);
}

/// Begin a frame: hide the cursor, start a synchronized update, turn
/// autowrap off.
const PAINT_BEGIN: &str = "\x1b[?25l\x1b[?2026h\x1b[?7l";
/// Erase the whole row before writing it. Erasing after the text would
/// delete the last cell of a row that fills the width (autowrap is off,
/// so the cursor stays on that cell).
const ERASE_LINE: &str = "\x1b[2K";
/// End a frame: autowrap back on, end the synchronized update.
const PAINT_END: &str = "\x1b[?7h\x1b[?2026l";
/// Close any OSC 8 hyperlink left open by a row.
const OSC8_CLOSE: &str = "\x1b]8;;\x1b\\";
const OSC8_OPEN_PREFIX: &str = "\x1b]8;;";

/// Where the hardware cursor goes after a frame: a row of the live area
/// and a display column.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LiveCursor {
    pub row: usize,
    pub col: usize,
}

/// One frame for [`InlineTerminal::paint`].
#[derive(Debug, Clone, Copy)]
pub struct InlineFrame<'a> {
    /// Rows that move into scrollback for good, above the live area.
    pub history: &'a [Line],
    /// The live area, top to bottom.
    pub live: &'a [Line],
    /// The visible cursor; `None` keeps the cursor hidden.
    pub cursor: Option<LiveCursor>,
}

/// The live-area state of the inline terminal.
#[derive(Debug)]
pub struct InlineTerminal {
    /// Encoded rows now on screen in the live area.
    live: Vec<String>,
    /// The live-area row the terminal cursor is on. `live.len()` means
    /// the line below the live area (the state after
    /// [`InlineTerminal::release`]).
    cursor_row: usize,
    height: usize,
    /// Whether a frame's cursor is shown. When off, the cursor still
    /// moves to the caret (IME candidate windows anchor there) but stays
    /// hidden.
    cursor_visible: bool,
    /// The caret of the frame on screen (after clipping). An unchanged
    /// frame with the same caret writes nothing.
    shown_cursor: Option<LiveCursor>,
}

impl InlineTerminal {
    /// A writer whose live area starts at the current cursor line, which
    /// must be at column 0.
    #[must_use]
    pub fn new(height: u16) -> Self {
        InlineTerminal {
            live: Vec::new(),
            cursor_row: 0,
            height: usize::from(height.max(1)),
            cursor_visible: true,
            shown_cursor: None,
        }
    }

    /// Show or hide the cursor at a frame's caret. Hidden, the cursor
    /// still moves to the caret.
    pub fn set_cursor_visible(&mut self, visible: bool) {
        self.cursor_visible = visible;
    }

    /// The terminal height changed. The width is not tracked: rows come
    /// fitted to the width from the composer.
    pub fn set_height(&mut self, height: u16) {
        self.height = usize::from(height.max(1));
    }

    /// Paint one frame: history rows go above the live area into
    /// scrollback, then the live area is redrawn. Unchanged live rows are
    /// not rewritten.
    ///
    /// A live area taller than the screen keeps its bottom rows; the
    /// clipped top rows are not shown and do not enter scrollback.
    ///
    /// # Errors
    ///
    /// Propagates the write error of `out`.
    pub fn paint(&mut self, out: &mut impl Write, frame: InlineFrame<'_>) -> io::Result<()> {
        let skip = frame.live.len().saturating_sub(self.height);
        let live = &frame.live[skip..];
        let cursor = frame.cursor.and_then(|c| {
            c.row
                .checked_sub(skip)
                .map(|row| LiveCursor { row, col: c.col })
        });
        let encoded: Vec<String> = live.iter().map(encode_row).collect();
        if frame.history.is_empty() && encoded == self.live && cursor == self.shown_cursor {
            return Ok(());
        }
        self.shown_cursor = cursor;
        let mut buf = String::from(PAINT_BEGIN);
        if frame.history.is_empty() {
            self.diff_live(&mut buf, encoded);
        } else {
            self.move_to(&mut buf, 0);
            buf.push_str("\x1b[J");
            for row in frame.history {
                buf.push_str(&encode_row(row));
                buf.push_str("\r\n");
            }
            self.write_rows_from_here(&mut buf, encoded);
        }
        self.place_cursor(&mut buf, cursor);
        buf.push_str(PAINT_END);
        self.publish_rows_below_cursor();
        out.write_all(buf.as_bytes())?;
        out.flush()
    }

    /// Record where the live area ends relative to the cursor for
    /// [`park_below_live`].
    fn publish_rows_below_cursor(&self) {
        let below = if self.live.is_empty() {
            NO_LIVE_AREA
        } else {
            self.live
                .len()
                .saturating_sub(1)
                .saturating_sub(self.cursor_row)
        };
        LIVE_ROWS_BELOW_CURSOR.store(below, Ordering::SeqCst);
    }

    /// Erase the live area and leave the cursor at its first row. The
    /// next frame paints from there.
    ///
    /// # Errors
    ///
    /// Propagates the write error of `out`.
    pub fn clear_live(&mut self, out: &mut impl Write) -> io::Result<()> {
        let mut buf = String::new();
        self.move_to(&mut buf, 0);
        buf.push_str("\x1b[J");
        self.live.clear();
        self.shown_cursor = None;
        self.cursor_row = 0;
        self.publish_rows_below_cursor();
        out.write_all(buf.as_bytes())?;
        out.flush()
    }

    /// Clear the screen and the scrollback, for a full replay at a new
    /// width or for a new session. The next frame should carry the whole
    /// transcript as history.
    ///
    /// # Errors
    ///
    /// Propagates the write error of `out`.
    pub fn reset(&mut self, out: &mut impl Write) -> io::Result<()> {
        // Screen before scrollback: tmux needs this order.
        out.write_all(b"\x1b[H\x1b[2J\x1b[3J")?;
        self.live.clear();
        self.shown_cursor = None;
        self.cursor_row = 0;
        self.publish_rows_below_cursor();
        out.flush()
    }

    /// Leave the live area on screen as final output, put the cursor on
    /// the line below it, and show the cursor. Use at exit, suspend, and
    /// before a child process takes the terminal. The next frame starts a
    /// new live area at that line.
    ///
    /// # Errors
    ///
    /// Propagates the write error of `out`.
    pub fn release(&mut self, out: &mut impl Write) -> io::Result<()> {
        let mut buf = String::new();
        if !self.live.is_empty() {
            let last = self.live.len() - 1;
            self.move_to(&mut buf, last);
            buf.push_str("\r\n");
        }
        buf.push_str("\x1b[?25h");
        self.live.clear();
        self.shown_cursor = None;
        self.cursor_row = 0;
        self.publish_rows_below_cursor();
        out.write_all(buf.as_bytes())?;
        out.flush()
    }

    /// Rewrite only the rows that changed. Rows past the old live area
    /// are appended with CRLF, which scrolls the screen when needed.
    fn diff_live(&mut self, buf: &mut String, encoded: Vec<String>) {
        let shared = self.live.len().min(encoded.len());
        for (i, row) in encoded.iter().enumerate().take(shared) {
            if self.live[i] != *row {
                self.move_to(buf, i);
                buf.push_str(ERASE_LINE);
                buf.push_str(row);
            }
        }
        if encoded.len() > self.live.len() {
            if self.live.is_empty() {
                self.move_to(buf, 0);
                buf.push('\r');
            } else {
                let last = self.live.len() - 1;
                self.move_to(buf, last);
                buf.push_str("\r\n");
                self.cursor_row = self.live.len();
            }
            for (i, row) in encoded.iter().enumerate().skip(self.live.len()) {
                if i > self.live.len() {
                    buf.push_str("\r\n");
                }
                buf.push_str(ERASE_LINE);
                buf.push_str(row);
                self.cursor_row = i;
            }
        } else if encoded.len() < self.live.len() {
            if encoded.is_empty() {
                self.move_to(buf, 0);
                buf.push_str("\x1b[J");
            } else {
                let last = encoded.len() - 1;
                self.move_to(buf, last);
                // Erase the rows below the last kept row. They exist on
                // screen, so the cursor-down never scrolls.
                buf.push_str("\x1b[1B\r\x1b[J\x1b[1A");
            }
        }
        self.live = encoded;
    }

    /// Write `encoded` as the live area starting at the cursor line, then
    /// erase below. The cursor is at column 0 of a fresh line.
    fn write_rows_from_here(&mut self, buf: &mut String, encoded: Vec<String>) {
        for (i, row) in encoded.iter().enumerate() {
            if i > 0 {
                buf.push_str("\r\n");
            }
            buf.push_str(ERASE_LINE);
            buf.push_str(row);
        }
        buf.push_str("\x1b[J");
        self.cursor_row = encoded.len().saturating_sub(1);
        self.live = encoded;
    }

    /// Move the cursor to column 0 of live row `row`.
    fn move_to(&mut self, buf: &mut String, row: usize) {
        use std::fmt::Write as _;
        if row < self.cursor_row {
            let _ = write!(buf, "\x1b[{}A", self.cursor_row - row);
        } else if row > self.cursor_row {
            let _ = write!(buf, "\x1b[{}B", row - self.cursor_row);
        }
        buf.push('\r');
        self.cursor_row = row;
    }

    fn place_cursor(&mut self, buf: &mut String, cursor: Option<LiveCursor>) {
        use std::fmt::Write as _;
        match cursor {
            Some(c) if c.row < self.live.len() => {
                self.move_to(buf, c.row);
                if c.col > 0 {
                    let _ = write!(buf, "\x1b[{}C", c.col);
                }
                if self.cursor_visible {
                    buf.push_str("\x1b[?25h");
                }
            }
            Some(_) | None => {}
        }
    }
}

/// Encode one row: SGR styling, image rows raw, and every hyperlink or
/// style closed at the row end so nothing leaks into the next row or
/// into scrollback. A hyperlink still open at the row end is closed and
/// reopened on the next row by the composer's rows themselves. Text goes
/// through TS `applyLineResets` (tabs to three spaces, Thai/Lao AM
/// decomposed) so the terminal's cells match the measured widths.
fn encode_row(row: &Line) -> String {
    let raw: String = row.iter().map(|span| span.content.as_str()).collect();
    if crate::terminal_image::is_image_line(&raw) {
        return raw;
    }
    let mut out = match crate::width::normalize_terminal_output(&raw) {
        std::borrow::Cow::Borrowed(_) => crate::ansi::line_to_ansi(row),
        std::borrow::Cow::Owned(_) => crate::ansi::line_to_ansi(
            &row.iter()
                .map(|span| {
                    crate::Span::styled(
                        crate::width::normalize_terminal_output(&span.content),
                        span.style,
                    )
                })
                .collect(),
        ),
    };
    if link_left_open(&raw) {
        out.push_str(OSC8_CLOSE);
    }
    out
}

/// Whether the last OSC 8 sequence in `text` opens a link (a non-empty
/// URL) rather than closing one.
fn link_left_open(text: &str) -> bool {
    text.rfind(OSC8_OPEN_PREFIX).is_some_and(|at| {
        let rest = &text[at + OSC8_OPEN_PREFIX.len()..];
        !(rest.starts_with('\x1b') || rest.starts_with('\x07'))
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Span;

    /// The crash park reads a process-global; tests that paint hold
    /// this so a parallel test never moves it under the park test.
    fn live_area_lock() -> std::sync::MutexGuard<'static, ()> {
        static LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());
        LOCK.lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    }

    fn rows(texts: &[&str]) -> Vec<Line> {
        texts
            .iter()
            .map(|t| vec![Span::raw((*t).to_string())])
            .collect()
    }

    /// A tab would jump the terminal's cursor to its next tab stop and
    /// desync the measured row: the writer expands it to three spaces.
    #[test]
    fn rows_expand_tabs_at_paint() {
        let row = vec![
            Span::raw("a\tb"),
            Span::styled(
                "\tc",
                crate::style::Style::new().add_modifier(crate::style::Modifier::BOLD),
            ),
        ];
        assert_eq!(encode_row(&row), "a   b\x1b[1m   c\x1b[0m");
    }

    /// A minimal terminal: applies the escape subset the writer emits to
    /// a grid that scrolls into a scrollback list. Returns scrollback +
    /// screen as plain rows.
    struct Screen {
        height: usize,
        scrollback: Vec<String>,
        grid: Vec<String>,
        row: usize,
        col: usize,
    }

    impl Screen {
        fn new(height: usize) -> Self {
            Screen {
                height,
                scrollback: Vec::new(),
                grid: vec![String::new(); height],
                row: 0,
                col: 0,
            }
        }

        fn line_feed(&mut self) {
            if self.row + 1 == self.height {
                let top = self.grid.remove(0);
                self.scrollback.push(top);
                self.grid.push(String::new());
            } else {
                self.row += 1;
            }
        }

        fn put(&mut self, ch: char) {
            let line = &mut self.grid[self.row];
            let mut chars: Vec<char> = line.chars().collect();
            while chars.len() < self.col {
                chars.push(' ');
            }
            if self.col < chars.len() {
                chars[self.col] = ch;
            } else {
                chars.push(ch);
            }
            *line = chars.into_iter().collect();
            self.col += 1;
        }

        fn feed(&mut self, bytes: &str) {
            let chars: Vec<char> = bytes.chars().collect();
            let mut i = 0;
            while i < chars.len() {
                match chars[i] {
                    '\r' => self.col = 0,
                    '\n' => self.line_feed(),
                    '\x1b' => {
                        i += 1;
                        match chars[i] {
                            '[' => {
                                let start = i + 1;
                                let mut end = start;
                                while !chars[end].is_ascii_alphabetic() {
                                    end += 1;
                                }
                                let params: String = chars[start..end].iter().collect();
                                let n: usize = params.trim_start_matches('?').parse().unwrap_or(1);
                                match chars[end] {
                                    'A' => self.row -= n,
                                    'B' => self.row += n,
                                    'C' => self.col += n,
                                    'K' if params == "2" => self.grid[self.row].clear(),
                                    'K' => {
                                        let line = &mut self.grid[self.row];
                                        let keep: String = line.chars().take(self.col).collect();
                                        *line = keep;
                                    }
                                    'J' if params == "2" => {
                                        self.grid = vec![String::new(); self.height];
                                    }
                                    'J' if params == "3" => self.scrollback.clear(),
                                    'J' => {
                                        let line = &mut self.grid[self.row];
                                        let keep: String = line.chars().take(self.col).collect();
                                        *line = keep;
                                        for line in &mut self.grid[self.row + 1..] {
                                            line.clear();
                                        }
                                    }
                                    'H' => {
                                        self.row = 0;
                                        self.col = 0;
                                    }
                                    _ => {}
                                }
                                i = end;
                            }
                            ']' => {
                                while !(chars[i] == '\x1b' && chars[i + 1] == '\\') {
                                    i += 1;
                                }
                                i += 1;
                            }
                            _ => {}
                        }
                    }
                    ch => self.put(ch),
                }
                i += 1;
            }
        }

        fn all(&self) -> Vec<String> {
            let mut out = self.scrollback.clone();
            out.extend(self.grid.iter().cloned());
            while out.last().is_some_and(String::is_empty) {
                out.pop();
            }
            out
        }
    }

    fn paint(term: &mut InlineTerminal, screen: &mut Screen, history: &[&str], live: &[&str]) {
        let history = rows(history);
        let live = rows(live);
        let mut out = Vec::new();
        term.paint(
            &mut out,
            InlineFrame {
                history: &history,
                live: &live,
                cursor: None,
            },
        )
        .unwrap();
        screen.feed(&String::from_utf8(out).unwrap());
    }

    #[test]
    fn history_lands_above_the_redrawn_live_area() {
        let _global = live_area_lock();
        let mut term = InlineTerminal::new(6);
        let mut screen = Screen::new(6);
        paint(&mut term, &mut screen, &[], &["thinking", "> |"]);
        paint(&mut term, &mut screen, &[], &["thinking.", "reply", "> |"]);
        paint(&mut term, &mut screen, &["you: hi", "reply"], &["> |"]);
        assert_eq!(screen.all(), ["you: hi", "reply", "> |"]);
    }

    #[test]
    fn a_shrinking_live_area_erases_the_rows_below_it() {
        let _global = live_area_lock();
        let mut term = InlineTerminal::new(6);
        let mut screen = Screen::new(6);
        paint(&mut term, &mut screen, &[], &["a", "b", "c", "d"]);
        paint(&mut term, &mut screen, &[], &["a", "x"]);
        assert_eq!(screen.all(), ["a", "x"]);
    }

    #[test]
    fn history_past_the_screen_height_scrolls_into_scrollback() {
        let _global = live_area_lock();
        let mut term = InlineTerminal::new(3);
        let mut screen = Screen::new(3);
        paint(&mut term, &mut screen, &[], &["live"]);
        paint(
            &mut term,
            &mut screen,
            &["1", "2", "3", "4"],
            &["live", "edit"],
        );
        paint(&mut term, &mut screen, &[], &["live!", "edit"]);
        assert_eq!(screen.all(), ["1", "2", "3", "4", "live!", "edit"]);
    }

    #[test]
    fn a_live_area_taller_than_the_screen_keeps_its_bottom_rows() {
        let _global = live_area_lock();
        let mut term = InlineTerminal::new(2);
        let mut screen = Screen::new(2);
        paint(&mut term, &mut screen, &[], &["a", "b", "c"]);
        paint(&mut term, &mut screen, &[], &["a", "b", "z"]);
        assert_eq!(screen.all(), ["b", "z"]);
    }

    #[test]
    fn release_leaves_the_live_area_as_output_and_starts_below_it() {
        let _global = live_area_lock();
        let mut term = InlineTerminal::new(6);
        let mut screen = Screen::new(6);
        paint(&mut term, &mut screen, &[], &["last frame", "> |"]);
        let mut out = Vec::new();
        term.release(&mut out).unwrap();
        screen.feed(&String::from_utf8(out).unwrap());
        paint(&mut term, &mut screen, &[], &["next"]);
        assert_eq!(screen.all(), ["last frame", "> |", "next"]);
    }

    #[test]
    fn reset_wipes_screen_and_scrollback_before_a_replay() {
        let _global = live_area_lock();
        let mut term = InlineTerminal::new(3);
        let mut screen = Screen::new(3);
        paint(
            &mut term,
            &mut screen,
            &["old 1", "old 2", "old 3"],
            &["live"],
        );
        let mut out = Vec::new();
        term.reset(&mut out).unwrap();
        screen.feed(&String::from_utf8(out).unwrap());
        paint(&mut term, &mut screen, &["new"], &["live"]);
        assert_eq!(screen.all(), ["new", "live"]);
    }

    #[test]
    fn an_open_hyperlink_is_closed_at_the_row_end() {
        let row = vec![Span::raw(format!("{OSC8_OPEN_PREFIX}https://x\x1b\\link"))];
        assert!(encode_row(&row).ends_with(OSC8_CLOSE));
        let closed = vec![Span::raw(format!(
            "{OSC8_OPEN_PREFIX}https://x\x1b\\link{OSC8_CLOSE}"
        ))];
        assert_eq!(encode_row(&closed).matches(OSC8_CLOSE).count(), 1);
    }

    #[test]
    fn a_hidden_cursor_still_moves_to_the_caret() {
        let _global = live_area_lock();
        let mut term = InlineTerminal::new(6);
        term.set_cursor_visible(false);
        let live = rows(&["> hi", "footer"]);
        let mut out = Vec::new();
        term.paint(
            &mut out,
            InlineFrame {
                history: &[],
                live: &live,
                cursor: Some(LiveCursor { row: 0, col: 4 }),
            },
        )
        .unwrap();
        let bytes = String::from_utf8(out).unwrap();
        assert!(
            bytes.ends_with("\x1b[1A\r\x1b[4C\x1b[?7h\x1b[?2026l"),
            "{bytes:?}"
        );
        assert!(!bytes.contains("\x1b[?25h"));
    }

    #[test]
    fn the_crash_park_lands_below_the_last_painted_live_area() {
        let _global = live_area_lock();
        let mut term = InlineTerminal::new(6);
        let mut screen = Screen::new(6);
        let live = rows(&["> hi", "tray", "footer"]);
        let mut out = Vec::new();
        term.paint(
            &mut out,
            InlineFrame {
                history: &[],
                live: &live,
                cursor: Some(LiveCursor { row: 0, col: 4 }),
            },
        )
        .unwrap();
        park_below_live(&mut out);
        screen.feed(&String::from_utf8(out).unwrap());
        screen.feed("$ ");
        assert_eq!(screen.all(), ["> hi", "tray", "footer", "$ "]);
        let mut again = Vec::new();
        park_below_live(&mut again);
        assert!(again.is_empty(), "a second park writes nothing");
    }
}
