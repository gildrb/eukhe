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
//!
//! The one exception is a soft-wrapped block ([`crate::soft_wrap`]): its
//! rows are filled to the edge by the composer and written back to back
//! with autowrap on, so the terminal joins them into one logical line
//! (selection and URL detection see it whole) and still shows exactly
//! the rows tracked. A block is rewritten whole when any row of it
//! changes.
//!
//! Every frame is checked off screen before it is written (the model's
//! `present`, bend/screen.bend): its bytes run on a copy of a shadow
//! screen ([`crate::vt::Vt`]) and must leave the history rows right above
//! the live area, every live row as it reads written fresh, and the
//! cursor where the writer tracks it. A frame that fails is drawn again
//! whole and checked again; a frame that fails both is not written and
//! is reported ([`take_rejection`]).
//!
//! A resize keeps scrollback as the terminal reflowed it: the writer
//! never clears scrollback or writes a history row again. It estimates
//! where the reflow put the live area and redraws only that.

use std::borrow::Cow;
use std::io::{self, Write};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Mutex, PoisonError};

use crate::vt::{Pos, Vt, VtRow};
use crate::Line;

/// Rows between the cursor and the last live row of the live area on
/// screen, or [`NO_LIVE_AREA`]. Process-global so the crash restore
/// ([`park_below_live`]) can put the shell prompt below the live area
/// without the writer that drew it.
static LIVE_ROWS_BELOW_CURSOR: AtomicUsize = AtomicUsize::new(NO_LIVE_AREA);
const NO_LIVE_AREA: usize = usize::MAX;

/// The last frame no check let through, until [`take_rejection`] reads
/// it.
static REJECTION: Mutex<Option<Rejection>> = Mutex::new(None);

/// Where a rejected frame is logged (the agent log, through the client
/// settings seam); `None` logs nowhere (a surface without the seam).
type RejectionLog = Box<dyn Fn(&str) + Send>;
static REJECTION_LOG: Mutex<Option<RejectionLog>> = Mutex::new(None);

/// The frames in a row the checks may reject before the writer gives
/// up: the next paint fails with [`ScreenCheckFailed`] and the surface
/// ends (its exit restores the terminal) instead of freezing.
pub(crate) const REJECTED_FRAMES_LIMIT: usize = 3;

/// Log every rejected frame (and history a release leaves unwritten)
/// with `log` from now on.
pub(crate) fn log_rejections_with(log: RejectionLog) {
    *REJECTION_LOG.lock().unwrap_or_else(PoisonError::into_inner) = Some(log);
}

/// Record a rejection: log it and keep it for [`take_rejection`].
fn report(rejection: &Rejection) {
    if let Some(log) = REJECTION_LOG
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .as_ref()
    {
        log(&rejection.message);
    }
    *REJECTION.lock().unwrap_or_else(PoisonError::into_inner) = Some(rejection.clone());
}

/// The checks rejected [`REJECTED_FRAMES_LIMIT`] frames in a row: the
/// writer stopped. The error a paint fails with then.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScreenCheckFailed {
    /// The frames rejected in a row.
    pub frames: usize,
    /// The last rejection.
    pub last: Rejection,
}

impl std::fmt::Display for ScreenCheckFailed {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "the screen stopped: the off-screen check rejected {} frames in a row (last: {})",
            self.frames, self.last.message
        )?;
        match eukhe_types::platform::agent_dir() {
            Some(dir) => write!(
                f,
                "; each rejection is in the agent log, {}",
                dir.join("logs").join("agent.jsonl").display()
            ),
            None => write!(f, "; each rejection is in the agent log"),
        }
    }
}

impl std::error::Error for ScreenCheckFailed {}

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

/// The last frame rejected by any writer since the last call, if any.
pub(crate) fn take_rejection() -> Option<Rejection> {
    REJECTION
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .take()
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
/// Autowrap on and off around a soft-wrapped block's pieces.
const AUTOWRAP_ON: &str = "\x1b[?7h";
const AUTOWRAP_OFF: &str = "\x1b[?7l";
/// The longest row excerpt a rejection message quotes.
const EXCERPT_CHARS: usize = 40;

/// One encoded row as the terminal holds it.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Row {
    text: String,
    /// Written right after the row above under autowrap: the terminal
    /// holds it as that row's soft-wrap continuation.
    joins_above: bool,
}

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

/// What [`InlineTerminal::paint`] did with a frame.
#[must_use]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Painted {
    /// The frame is already on screen: nothing was written.
    Unchanged,
    /// The frame's own update passed its check and was written.
    Drawn,
    /// The frame's own update failed its check (or the width changed):
    /// a full redraw of the live area passed its check and was written.
    Redrawn,
    /// Both checks failed: nothing was written. The frame's history rows
    /// go out with the next frame.
    Rejected(Rejection),
}

/// Why a frame was not shown.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rejection {
    /// Which checks failed, and the first row that differed.
    pub message: String,
}

impl std::fmt::Display for Rejection {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message)
    }
}

/// The result of a frame's off-screen check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Check {
    Pass,
    Fail,
}

/// How a shown frame was drawn.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Redraw {
    /// Only what changed.
    Diff,
    /// The whole live area.
    Full,
}

/// What reached the terminal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Shown<F> {
    /// The terminal got `frame`.
    Drawn { frame: F, redraw: Redraw },
    /// Both checks failed: nothing was drawn. `frame` is the first one.
    Error { frame: F },
}

/// Pick what reaches the terminal (the model's `present`): `frame` when
/// its check passed; else the full redraw `full` builds, when its check
/// passed; else nothing. `full` runs only when the first check failed.
pub(crate) fn present<F>(frame: F, first: Check, full: impl FnOnce() -> (F, Check)) -> Shown<F> {
    match first {
        Check::Pass => Shown::Drawn {
            frame,
            redraw: Redraw::Diff,
        },
        Check::Fail => {
            let (redrawn, second) = full();
            match second {
                Check::Pass => Shown::Drawn {
                    frame: redrawn,
                    redraw: Redraw::Full,
                },
                Check::Fail => Shown::Error { frame },
            }
        }
    }
}

/// Whether the live rows tracked are the rows on screen.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Layout {
    /// The rows tracked are on screen as written.
    Written,
    /// The width changed and the terminal reflowed the live area: the
    /// next frame redraws it whole.
    Reflowed,
}

/// A frame's bytes, run off screen.
struct Candidate {
    bytes: String,
    /// The shadow screen after the bytes.
    screen: Vt,
    /// What the check found wrong, if anything.
    failure: Option<String>,
}

impl Candidate {
    fn check(&self) -> Check {
        match self.failure {
            None => Check::Pass,
            Some(_) => Check::Fail,
        }
    }
}

/// The live-area state of the inline terminal.
#[derive(Debug)]
#[cfg_attr(test, derive(Clone))]
pub struct InlineTerminal {
    /// Encoded rows now on screen in the live area.
    live: Vec<Row>,
    /// The live-area row the terminal cursor is on. `live.len()` means
    /// the line below the live area (the state after
    /// [`InlineTerminal::release`]).
    cursor_row: usize,
    width: usize,
    height: usize,
    /// Whether a frame's cursor is shown. When off, the cursor still
    /// moves to the caret (IME candidate windows anchor there) but stays
    /// hidden.
    cursor_visible: bool,
    /// The caret of the frame on screen (after clipping). An unchanged
    /// frame with the same caret writes nothing.
    shown_cursor: Option<LiveCursor>,
    /// The screen as this writer left it, scrollback dropped after each
    /// frame. Every frame is checked on a copy first.
    shadow: Vt,
    /// The shadow's grid row of the live area's first row.
    top: usize,
    layout: Layout,
    /// History rows of rejected frames, written before the next frame's
    /// history.
    pending_history: Vec<Line>,
    /// The frames rejected since the last frame shown.
    rejected_in_a_row: usize,
}

impl InlineTerminal {
    /// A writer for a `width` x `height` terminal whose live area starts
    /// at the current cursor line, which must be at column 0.
    #[must_use]
    pub fn new(width: u16, height: u16) -> Self {
        let width = usize::from(width.max(1));
        let height = usize::from(height.max(1));
        InlineTerminal {
            live: Vec::new(),
            cursor_row: 0,
            width,
            height,
            cursor_visible: true,
            shown_cursor: None,
            shadow: Vt::new(width, height),
            top: 0,
            layout: Layout::Written,
            pending_history: Vec::new(),
            rejected_in_a_row: 0,
        }
    }

    /// Show or hide the cursor at a frame's caret. Hidden, the cursor
    /// still moves to the caret.
    pub fn set_cursor_visible(&mut self, visible: bool) {
        self.cursor_visible = visible;
    }

    /// The terminal width changed (no-op when it did not). Scrollback
    /// stays as the terminal reflowed it; the next frame redraws only
    /// the live area, at the new width, from where the reflow put its
    /// top. Rows come fitted to the width from the composer.
    pub fn set_width(&mut self, width: u16) {
        let width = usize::from(width.max(1));
        if width != self.width {
            self.resize(width, self.height);
        }
    }

    /// The terminal height changed (no-op when it did not).
    pub fn set_height(&mut self, height: u16) {
        let height = usize::from(height.max(1));
        if height != self.height {
            self.resize(self.width, height);
        }
    }

    /// Resize the shadow screen the way the terminal does and find the
    /// live area in it again: its first row and the last cell of its
    /// last row move with their cells.
    fn resize(&mut self, width: usize, height: usize) {
        let last = self.top + self.live.len().saturating_sub(1);
        let last_col = self
            .shadow
            .row_at(last)
            .map_or(0, |row| row.cell_count().saturating_sub(1));
        let mut marks = [
            Pos {
                row: self.top,
                col: 0,
            },
            Pos {
                row: last,
                col: last_col,
            },
        ];
        self.shadow.resize_marked(width, height, &mut marks);
        let dropped = self.shadow.scrollback_len();
        self.shadow.forget_scrollback();
        let [top, bottom] = marks.map(|mark| mark.row.saturating_sub(dropped));
        if width != self.width || marks[0].row < dropped {
            // The rows on screen are no longer the rows tracked: track
            // how many rows the area takes now and redraw it whole.
            let rows = if self.live.is_empty() {
                0
            } else {
                bottom.saturating_sub(top) + 1
            };
            self.live = vec![
                Row {
                    text: String::new(),
                    joins_above: false,
                };
                rows
            ];
            self.layout = Layout::Reflowed;
        }
        self.top = top;
        self.cursor_row = self.shadow.cursor().row.saturating_sub(top);
        self.width = width;
        self.height = height;
    }

    /// Paint one frame: history rows go above the live area into
    /// scrollback, then the live area is redrawn. Unchanged live rows are
    /// not rewritten.
    ///
    /// The frame is checked off screen first. When the check fails, the
    /// whole live area is drawn again and checked again; when that fails
    /// too, nothing is written, the frame comes back as
    /// [`Painted::Rejected`] (logged, and kept for [`take_rejection`]),
    /// and its history rows go out with the next frame.
    ///
    /// A live area taller than the screen keeps its bottom rows; the
    /// clipped top rows are not shown and do not enter scrollback.
    ///
    /// # Errors
    ///
    /// Propagates the write error of `out`. Fails with
    /// [`ScreenCheckFailed`] when this is the
    /// [`REJECTED_FRAMES_LIMIT`]th frame in a row the checks reject: the
    /// surface ends instead of freezing on a screen it cannot update.
    pub fn paint(&mut self, out: &mut impl Write, frame: InlineFrame<'_>) -> io::Result<Painted> {
        let skip = frame.live.len().saturating_sub(self.height);
        let live = &frame.live[skip..];
        let cursor = frame.cursor.and_then(|c| {
            c.row
                .checked_sub(skip)
                .map(|row| LiveCursor { row, col: c.col })
        });
        let encoded = encode_rows(live);
        if frame.history.is_empty()
            && self.pending_history.is_empty()
            && self.layout == Layout::Written
            && encoded == self.live
            && cursor == self.shown_cursor
        {
            return Ok(Painted::Unchanged);
        }
        let history_lines: Cow<'_, [Line]> = if self.pending_history.is_empty() {
            Cow::Borrowed(frame.history)
        } else {
            let mut lines = std::mem::take(&mut self.pending_history);
            lines.extend_from_slice(frame.history);
            Cow::Owned(lines)
        };
        let history = encode_rows(&history_lines);
        let old_live = std::mem::take(&mut self.live);
        let old_cursor_row = self.cursor_row;
        let first = match self.layout {
            Layout::Written => {
                let bytes = self.frame_bytes(Redraw::Diff, &old_live, &history, encoded, cursor);
                self.check(bytes, &old_live, &history, cursor)
            }
            Layout::Reflowed => {
                self.live = encoded;
                Candidate {
                    bytes: String::new(),
                    screen: Vt::new(1, 1),
                    failure: Some("the width changed".to_string()),
                }
            }
        };
        let first_check = first.check();
        let mut full_failure = String::new();
        let shown = present(first, first_check, || {
            let encoded = std::mem::take(&mut self.live);
            // Start from the cursor row the shadow screen has, not the
            // one tracked: the redraw must not depend on what failed.
            self.cursor_row = self.shadow.cursor().row.saturating_sub(self.top);
            let bytes = self.frame_bytes(Redraw::Full, &[], &history, encoded, cursor);
            let full = self.check(bytes, &[], &history, cursor);
            if let Some(failure) = &full.failure {
                full_failure.clone_from(failure);
            }
            let check = full.check();
            (full, check)
        });
        match shown {
            Shown::Drawn { frame, redraw } => {
                self.shadow = frame.screen;
                let dropped = self.shadow.scrollback_len();
                self.shadow.forget_scrollback();
                self.top = (self.top + history.len()).saturating_sub(dropped);
                self.shown_cursor = cursor;
                self.rejected_in_a_row = 0;
                self.layout = Layout::Written;
                self.publish_rows_below_cursor();
                out.write_all(frame.bytes.as_bytes())?;
                out.flush()?;
                Ok(match redraw {
                    Redraw::Diff => Painted::Drawn,
                    Redraw::Full => Painted::Redrawn,
                })
            }
            Shown::Error { frame } => {
                self.live = old_live;
                self.cursor_row = old_cursor_row;
                self.pending_history = history_lines.into_owned();
                let rejection = Rejection {
                    message: format!(
                        "frame not shown: {}; full redraw: {full_failure}",
                        frame.failure.unwrap_or_default()
                    ),
                };
                report(&rejection);
                self.rejected_in_a_row += 1;
                if self.rejected_in_a_row >= REJECTED_FRAMES_LIMIT {
                    return Err(io::Error::other(ScreenCheckFailed {
                        frames: self.rejected_in_a_row,
                        last: rejection,
                    }));
                }
                Ok(Painted::Rejected(rejection))
            }
        }
    }

    /// Build a frame's bytes and track the live area they leave. `Diff`
    /// rewrites only the blocks that changed (a frame with history rows
    /// redraws the live area below them); `Full` erases the live area and
    /// writes it whole.
    fn frame_bytes(
        &mut self,
        redraw: Redraw,
        old: &[Row],
        history: &[Row],
        encoded: Vec<Row>,
        cursor: Option<LiveCursor>,
    ) -> String {
        let mut buf = String::from(PAINT_BEGIN);
        match redraw {
            Redraw::Diff if history.is_empty() => self.diff_live(&mut buf, old, encoded),
            Redraw::Diff | Redraw::Full => {
                // One erase from the live area's top clears everything
                // below; an erase after the last row would delete the
                // last cell of a row that fills the width (the cursor
                // stays on it).
                self.move_to(&mut buf, 0);
                buf.push_str("\x1b[J");
                if !history.is_empty() {
                    push_fresh_rows(&mut buf, history);
                    buf.push_str("\r\n");
                }
                push_fresh_rows(&mut buf, &encoded);
                self.cursor_row = encoded.len().saturating_sub(1);
                self.live = encoded;
            }
        }
        self.place_cursor(&mut buf, cursor);
        buf.push_str(PAINT_END);
        buf
    }

    /// Run `bytes` on a copy of the shadow screen and compare the result
    /// with what the writer tracks: the rows above the live area (written
    /// before: committed text) keep their cells, the last `height` history
    /// rows (the ones still on screen; rows that scroll past the screen
    /// are not checked) end right above the live area, each live block
    /// that changed from `old` (the live rows before the frame) or that
    /// the bytes rewrote reads as it does written fresh on a blank screen
    /// (a block that did not change and that the bytes left alone passed
    /// when it was written), the rows below the live area are blank, and
    /// the cursor is on the row (and the caret's column) tracked.
    fn check(
        &self,
        bytes: String,
        old: &[Row],
        history: &[Row],
        cursor: Option<LiveCursor>,
    ) -> Candidate {
        let mut screen = self.shadow.clone();
        screen.feed(&bytes);
        let top = self.top + history.len();
        let failure = 'check: {
            for at in 0..self.top {
                if !screen.shares_row(at, &self.shadow, at)
                    && screen.row_at(at) != self.shadow.row_at(at)
                {
                    break 'check Some(format!(
                        "row {} above the live area shows {:?}, expected {:?}",
                        self.top - at,
                        excerpt(screen.row_at(at)),
                        excerpt(self.shadow.row_at(at))
                    ));
                }
            }
            if !history.is_empty() {
                let mut from = history.len().saturating_sub(self.height);
                while from > 0 && history[from].joins_above {
                    from -= 1;
                }
                let reference = fresh_screen(self.width, &history[from..]);
                for at in from..history.len() {
                    let (got, want) = (screen.row_at(self.top + at), reference.row_at(at - from));
                    if got != want {
                        break 'check Some(format!(
                            "history row {at} shows {:?}, expected {:?}",
                            excerpt(got),
                            excerpt(want)
                        ));
                    }
                }
            }
            let mut start = 0;
            while start < self.live.len() {
                let end = block_end(&self.live, start);
                let rewritten = old.get(start..end) != Some(&self.live[start..end])
                    || (start..end)
                        .any(|at| !screen.shares_row(top + at, &self.shadow, self.top + at));
                if rewritten {
                    let reference = fresh_screen(self.width, &self.live[start..end]);
                    for at in start..end {
                        let (got, want) = (screen.row_at(top + at), reference.row_at(at - start));
                        if got != want {
                            break 'check Some(format!(
                                "live row {at} shows {:?}, expected {:?}",
                                excerpt(got),
                                excerpt(want)
                            ));
                        }
                    }
                }
                start = end;
            }
            let below = top + self.live.len();
            for at in below..screen.rows_len() {
                let got = screen.row_at(at);
                if got.is_some_and(|row| *row != VtRow::default()) {
                    break 'check Some(format!(
                        "row {} below the live area shows {:?}",
                        at - below,
                        excerpt(got)
                    ));
                }
            }
            let got = screen.cursor();
            let row = top + self.cursor_row;
            let placed = match cursor {
                Some(c) if c.row < self.live.len() => Some(c.col.min(self.width - 1)),
                Some(_) | None => None,
            };
            let col_differs = placed.is_some_and(|col| col != got.col);
            if got.row != row || col_differs {
                break 'check Some(format!(
                    "the cursor is on row {} col {}, expected row {row}{}",
                    got.row,
                    got.col,
                    placed.map(|col| format!(" col {col}")).unwrap_or_default()
                ));
            }
            None
        };
        Candidate {
            bytes,
            screen,
            failure,
        }
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
        self.shadow.feed(&buf);
        self.live.clear();
        self.shown_cursor = None;
        self.cursor_row = 0;
        self.layout = Layout::Written;
        self.publish_rows_below_cursor();
        out.write_all(buf.as_bytes())?;
        out.flush()
    }

    /// Leave the live area on screen as final output, put the cursor on
    /// the line below it, and show the cursor. Use at exit, suspend, and
    /// before a child process takes the terminal. The next frame starts a
    /// new live area at that line. History rows of rejected frames that
    /// are still pending are not written unchecked: the release reports
    /// them (logged, and kept for [`take_rejection`]) and keeps them for
    /// the next frame, whose check writes them.
    ///
    /// # Errors
    ///
    /// Propagates the write error of `out`.
    pub fn release(&mut self, out: &mut impl Write) -> io::Result<()> {
        if !self.pending_history.is_empty() {
            report(&Rejection {
                message: format!(
                    "{} history rows of rejected frames are not on screen yet; the next frame writes them",
                    self.pending_history.len()
                ),
            });
        }
        let mut buf = String::new();
        if !self.live.is_empty() {
            let last = self.live.len() - 1;
            self.move_to(&mut buf, last);
            buf.push_str("\r\n");
        }
        buf.push_str("\x1b[?25h");
        self.shadow.feed(&buf);
        self.shadow.forget_scrollback();
        self.top = self.shadow.cursor().row;
        self.live.clear();
        self.shown_cursor = None;
        self.cursor_row = 0;
        self.layout = Layout::Written;
        self.publish_rows_below_cursor();
        out.write_all(buf.as_bytes())?;
        out.flush()
    }

    /// Rewrite only the blocks of `encoded` that differ from `old` (a
    /// plain row is a block of one). Rows past the old live area are
    /// appended with line feeds, which scroll the screen when needed.
    fn diff_live(&mut self, buf: &mut String, old: &[Row], encoded: Vec<Row>) {
        // Rows on screen from the live area's top: the old live area, or
        // the cursor line a new one starts on.
        let mut on_screen = old.len().max(1);
        let mut start = 0;
        while start < encoded.len() {
            let end = block_end(&encoded, start);
            if end > old.len() || encoded[start..end] != old[start..end] {
                self.write_block(buf, &encoded[start..end], start, &mut on_screen);
            }
            start = end;
        }
        if encoded.len() < old.len() {
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

    /// Write one block at live row `start`. A soft-wrapped block erases
    /// all its rows first (an erase between pieces would cancel the
    /// pending wrap), then writes its pieces back to back under autowrap.
    fn write_block(
        &mut self,
        buf: &mut String,
        block: &[Row],
        start: usize,
        on_screen: &mut usize,
    ) {
        for row in start..start + block.len() {
            self.reach(buf, row, on_screen);
            buf.push_str(ERASE_LINE);
        }
        if let [row] = block {
            buf.push_str(&row.text);
            return;
        }
        self.move_to(buf, start);
        buf.push_str(AUTOWRAP_ON);
        for row in block {
            buf.push_str(&row.text);
        }
        buf.push_str(AUTOWRAP_OFF);
        self.cursor_row = start + block.len() - 1;
    }

    /// Move to column 0 of live row `row`: a row on screen, or the new
    /// row right below the last one (a line feed, scrolling at the
    /// bottom).
    fn reach(&mut self, buf: &mut String, row: usize, on_screen: &mut usize) {
        if row < *on_screen {
            self.move_to(buf, row);
        } else {
            self.move_to(buf, *on_screen - 1);
            buf.push('\n');
            self.cursor_row = row;
            *on_screen = row + 1;
        }
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

/// Encode rows and their soft-wrap joins: a continuation row joins the
/// row above only inside a block, so a block whose head was clipped
/// away starts at its first shown row.
fn encode_rows(rows: &[Line]) -> Vec<Row> {
    let mut in_block = false;
    rows.iter()
        .map(|row| {
            let wrap = crate::soft_wrap::row_wrap(row);
            let joins_above = match wrap {
                crate::soft_wrap::RowWrap::Continuation => in_block,
                crate::soft_wrap::RowWrap::Single | crate::soft_wrap::RowWrap::Head => false,
            };
            in_block = match wrap {
                crate::soft_wrap::RowWrap::Single => false,
                crate::soft_wrap::RowWrap::Head | crate::soft_wrap::RowWrap::Continuation => true,
            };
            Row {
                text: encode_row(crate::soft_wrap::content(row)),
                joins_above,
            }
        })
        .collect()
}

/// Write `rows` from the cursor line down onto blank lines (below an
/// erase, or scrolled in): each plain row on a new line, each block's
/// pieces back to back under autowrap.
fn push_fresh_rows(buf: &mut String, rows: &[Row]) {
    for (i, row) in rows.iter().enumerate() {
        let next_joins = rows.get(i + 1).is_some_and(|next| next.joins_above);
        if !row.joins_above {
            if i > 0 {
                buf.push_str("\r\n");
            }
            buf.push_str(ERASE_LINE);
            if next_joins {
                buf.push_str(AUTOWRAP_ON);
            }
        }
        buf.push_str(&row.text);
        if row.joins_above && !next_joins {
            buf.push_str(AUTOWRAP_OFF);
        }
    }
}

/// Encode one row: SGR styling, image rows raw, and every hyperlink or
/// style closed at the row end so nothing leaks into the next row or
/// into scrollback. A hyperlink still open at the row end is closed and
/// reopened on the next row by the composer's rows themselves. Text goes
/// through TS `applyLineResets` (tabs to three spaces, Thai/Lao AM
/// decomposed) so the terminal's cells match the measured widths.
fn encode_row(row: &[crate::Span]) -> String {
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
                .collect::<Vec<_>>(),
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

/// The end of the block that starts at row `start`: the row after its
/// last soft-wrap continuation.
fn block_end(rows: &[Row], start: usize) -> usize {
    start
        + 1
        + rows[start + 1..]
            .iter()
            .take_while(|row| row.joins_above)
            .count()
}

/// `rows` written fresh on a blank screen `width` cells wide: what each
/// row reads as on its own.
fn fresh_screen(width: usize, rows: &[Row]) -> Vt {
    let mut screen = Vt::new(width, rows.len());
    let mut buf = String::from(PAINT_BEGIN);
    push_fresh_rows(&mut buf, rows);
    screen.feed(&buf);
    screen
}

/// The start of a row's text, for a rejection message.
fn excerpt(row: Option<&VtRow>) -> String {
    row.map(VtRow::text)
        .unwrap_or_default()
        .chars()
        .take(EXCERPT_CHARS)
        .collect()
}

/// The crash park reads a process-global; tests that paint hold this so
/// a parallel test never moves it under the park test.
#[cfg(test)]
pub(crate) fn live_area_lock() -> std::sync::MutexGuard<'static, ()> {
    static LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());
    LOCK.lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Span;

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

    fn paint(term: &mut InlineTerminal, screen: &mut Vt, history: &[&str], live: &[&str]) {
        paint_lines(term, screen, &rows(history), &rows(live));
    }

    /// Paint a frame whose own update must pass its check, and show it
    /// on `screen`.
    fn paint_lines(term: &mut InlineTerminal, screen: &mut Vt, history: &[Line], live: &[Line]) {
        let painted = paint_frame(term, screen, history, live, None);
        assert_eq!(painted, Painted::Drawn);
    }

    fn paint_frame(
        term: &mut InlineTerminal,
        screen: &mut Vt,
        history: &[Line],
        live: &[Line],
        cursor: Option<LiveCursor>,
    ) -> Painted {
        let mut out = Vec::new();
        let painted = term
            .paint(
                &mut out,
                InlineFrame {
                    history,
                    live,
                    cursor,
                },
            )
            .unwrap();
        screen.feed(&String::from_utf8(out).unwrap());
        painted
    }

    /// `text` as a soft-wrapped block at `width`, then `after` as plain
    /// rows.
    fn block_then(text: &str, width: usize, after: &[&str]) -> Vec<Line> {
        let mut lines = crate::soft_wrap::rows(
            " ",
            text,
            crate::style::Style::default(),
            width,
            crate::soft_wrap::Link::Plain,
        );
        lines.extend(rows(after));
        lines
    }

    const LINK: &str = "https://x.example/authorize?code=true&client_id=abc&state=xyz";

    #[test]
    fn a_soft_wrapped_block_reads_as_one_logical_line() {
        let _global = live_area_lock();
        let mut term = InlineTerminal::new(20, 8);
        let mut screen = Vt::new(20, 8);
        let live = block_then(LINK, 20, &["", "> |"]);
        paint_lines(&mut term, &mut screen, &[], &live);
        assert_eq!(
            screen.all(),
            [
                " https://x.example/a",
                "uthorize?code=true&c",
                "lient_id=abc&state=x",
                "yz",
                "",
                "> |"
            ]
        );
        assert_eq!(
            screen.logical(),
            [format!(" {LINK}"), String::new(), "> |".to_string()]
        );
    }

    /// A changed piece rewrites the whole block, and the rows around it
    /// stay where the writer tracks them.
    #[test]
    fn a_changed_block_is_rewritten_whole_in_place() {
        let _global = live_area_lock();
        let mut term = InlineTerminal::new(20, 8);
        let mut screen = Vt::new(20, 8);
        paint_lines(&mut term, &mut screen, &[], &block_then(LINK, 20, &["> |"]));
        let other = LINK.replace("xyz", "q");
        paint_lines(
            &mut term,
            &mut screen,
            &[],
            &block_then(&other, 20, &["> a"]),
        );
        paint(&mut term, &mut screen, &[], &["top", "> b"]);
        assert_eq!(screen.all(), ["top", "> b"]);
        paint_lines(
            &mut term,
            &mut screen,
            &[],
            &block_then(&other, 20, &["> c"]),
        );
        assert_eq!(screen.logical(), [format!(" {other}"), "> c".to_string()]);
    }

    /// A block appended at the bottom of the screen scrolls it by its own
    /// rows only: later frames still land on the right rows.
    #[test]
    fn a_block_appended_at_the_bottom_keeps_the_row_count_exact() {
        let _global = live_area_lock();
        let mut term = InlineTerminal::new(20, 6);
        let mut screen = Vt::new(20, 6);
        screen.feed("x\r\ny\r\nz\r\n");
        paint(&mut term, &mut screen, &[], &["a", "b", "c"]);
        let mut live = rows(&["a"]);
        live.extend(block_then(LINK, 20, &["> |"]));
        paint_lines(&mut term, &mut screen, &[], &live);
        live.pop();
        live.extend(rows(&["> typed"]));
        paint_lines(&mut term, &mut screen, &[], &live);
        assert_eq!(
            screen.logical(),
            [
                "x".to_string(),
                "y".to_string(),
                "z".to_string(),
                "a".to_string(),
                format!(" {LINK}"),
                "> typed".to_string()
            ]
        );
    }

    #[test]
    fn a_block_in_history_stays_one_logical_line_in_scrollback() {
        let _global = live_area_lock();
        let mut term = InlineTerminal::new(20, 3);
        let mut screen = Vt::new(20, 3);
        paint(&mut term, &mut screen, &[], &["live"]);
        paint_lines(
            &mut term,
            &mut screen,
            &block_then(LINK, 20, &["done"]),
            &rows(&["live"]),
        );
        assert_eq!(
            screen.logical(),
            [format!(" {LINK}"), "done".to_string(), "live".to_string()]
        );
    }

    /// A block whose head is clipped off the top of the screen starts at
    /// its first shown row.
    #[test]
    fn a_clipped_block_starts_at_its_first_shown_row() {
        let _global = live_area_lock();
        let mut term = InlineTerminal::new(20, 3);
        let mut screen = Vt::new(20, 3);
        paint_lines(&mut term, &mut screen, &[], &block_then(LINK, 20, &["> |"]));
        assert_eq!(screen.all(), ["lient_id=abc&state=x", "yz", "> |"]);
        assert_eq!(screen.logical(), ["lient_id=abc&state=xyz", "> |"]);
    }

    #[test]
    fn history_lands_above_the_redrawn_live_area() {
        let _global = live_area_lock();
        let mut term = InlineTerminal::new(40, 6);
        let mut screen = Vt::new(40, 6);
        paint(&mut term, &mut screen, &[], &["thinking", "> |"]);
        paint(&mut term, &mut screen, &[], &["thinking.", "reply", "> |"]);
        paint(&mut term, &mut screen, &["you: hi", "reply"], &["> |"]);
        assert_eq!(screen.all(), ["you: hi", "reply", "> |"]);
    }

    /// Regression: a frame with history rows erased below its last live
    /// row after writing it, which cut the last cell of a row that fills
    /// the width (the editor box's corner).
    #[test]
    fn a_full_width_last_row_keeps_its_last_cell_below_history() {
        let _global = live_area_lock();
        let mut term = InlineTerminal::new(20, 6);
        let mut screen = Vt::new(20, 6);
        let corner = format!("└{}┘", "─".repeat(18));
        paint(&mut term, &mut screen, &["you: hi"], &["> |", &corner]);
        assert_eq!(screen.all(), ["you: hi", "> |", corner.as_str()]);
    }

    #[test]
    fn a_shrinking_live_area_erases_the_rows_below_it() {
        let _global = live_area_lock();
        let mut term = InlineTerminal::new(40, 6);
        let mut screen = Vt::new(40, 6);
        paint(&mut term, &mut screen, &[], &["a", "b", "c", "d"]);
        paint(&mut term, &mut screen, &[], &["a", "x"]);
        assert_eq!(screen.all(), ["a", "x"]);
    }

    #[test]
    fn history_past_the_screen_height_scrolls_into_scrollback() {
        let _global = live_area_lock();
        let mut term = InlineTerminal::new(40, 3);
        let mut screen = Vt::new(40, 3);
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
        let mut term = InlineTerminal::new(40, 2);
        let mut screen = Vt::new(40, 2);
        paint(&mut term, &mut screen, &[], &["a", "b", "c"]);
        paint(&mut term, &mut screen, &[], &["a", "b", "z"]);
        assert_eq!(screen.all(), ["b", "z"]);
    }

    #[test]
    fn release_leaves_the_live_area_as_output_and_starts_below_it() {
        let _global = live_area_lock();
        let mut term = InlineTerminal::new(40, 6);
        let mut screen = Vt::new(40, 6);
        paint(&mut term, &mut screen, &[], &["last frame", "> |"]);
        let mut out = Vec::new();
        term.release(&mut out).unwrap();
        screen.feed(&String::from_utf8(out).unwrap());
        paint(&mut term, &mut screen, &[], &["next"]);
        assert_eq!(screen.all(), ["last frame", "> |", "next"]);
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
        let mut term = InlineTerminal::new(40, 6);
        term.set_cursor_visible(false);
        let live = rows(&["> hi", "footer"]);
        let mut out = Vec::new();
        let painted = term
            .paint(
                &mut out,
                InlineFrame {
                    history: &[],
                    live: &live,
                    cursor: Some(LiveCursor { row: 0, col: 4 }),
                },
            )
            .unwrap();
        assert_eq!(painted, Painted::Drawn);
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
        let mut term = InlineTerminal::new(40, 6);
        let mut screen = Vt::new(40, 6);
        let live = rows(&["> hi", "tray", "footer"]);
        let mut out = Vec::new();
        let painted = term
            .paint(
                &mut out,
                InlineFrame {
                    history: &[],
                    live: &live,
                    cursor: Some(LiveCursor { row: 0, col: 4 }),
                },
            )
            .unwrap();
        assert_eq!(painted, Painted::Drawn);
        park_below_live(&mut out);
        screen.feed(&String::from_utf8(out).unwrap());
        screen.feed("$ ");
        assert_eq!(screen.all(), ["> hi", "tray", "footer", "$ "]);
        let mut again = Vec::new();
        park_below_live(&mut again);
        assert!(again.is_empty(), "a second park writes nothing");
    }

    /// A bordered box `width` cells wide, like the editor's.
    fn editor_box(width: usize, body: &str) -> Vec<Line> {
        let inner = width - 2;
        [
            format!("┌{}┐", "─".repeat(inner)),
            format!("│{body:<inner$}│"),
            format!("└{}┘", "─".repeat(inner)),
        ]
        .into_iter()
        .map(|text| vec![Span::raw(text)])
        .collect()
    }

    fn texts(lines: &[Line]) -> Vec<String> {
        lines
            .iter()
            .map(|line| line.iter().map(|span| span.content.as_str()).collect())
            .collect()
    }

    /// A width change keeps scrollback as written: the terminal reflows
    /// it, and the next frame redraws only the live area from where the
    /// reflow put it, never a history row or a screen or scrollback
    /// clear. A full-width box exercises the reflow both ways.
    #[test]
    fn a_resize_keeps_scrollback_and_redraws_only_the_live_area() {
        let _global = live_area_lock();
        for new_width in [30_u16, 50] {
            let mut term = InlineTerminal::new(40, 8);
            let mut screen = Vt::new(40, 8);
            let mut history: Vec<Line> = (1..=12)
                .map(|n| vec![Span::raw(format!("history {n:02} {}", "=".repeat(29)))])
                .collect();
            history.extend(block_then(LINK, 40, &["done"]));
            paint_lines(&mut term, &mut screen, &history, &editor_box(40, "> draft"));
            let before = screen.logical();
            let kept = before[..before.len() - 3].to_vec();

            screen.resize(usize::from(new_width), 8);
            term.set_width(new_width);
            let live = editor_box(usize::from(new_width), "> draft");
            let mut out = Vec::new();
            let painted = term
                .paint(
                    &mut out,
                    InlineFrame {
                        history: &[],
                        live: &live,
                        cursor: Some(LiveCursor { row: 1, col: 8 }),
                    },
                )
                .unwrap();
            assert_eq!(painted, Painted::Redrawn);
            let bytes = String::from_utf8(out).unwrap();
            for gone in ["\x1b[3J", "\x1b[2J", "history", "done", "example"] {
                assert!(!bytes.contains(gone), "{gone:?} in {bytes:?}");
            }
            screen.feed(&bytes);
            assert_eq!(screen.logical(), [kept.clone(), texts(&live)].concat());
            let all = screen.all();
            assert_eq!(all[all.len() - 3..], texts(&live));

            // The shadow screen follows the reflow: the next frame is a
            // plain update again.
            let typed = editor_box(usize::from(new_width), "> draft!");
            let painted = paint_frame(
                &mut term,
                &mut screen,
                &[],
                &typed,
                Some(LiveCursor { row: 1, col: 9 }),
            );
            assert_eq!(painted, Painted::Drawn);
            assert_eq!(screen.logical(), [kept, texts(&typed)].concat());
        }
    }

    /// A shadow screen out of step with the state tracked fails the
    /// update check; the full redraw starts from the shadow's cursor,
    /// passes, and puts the screen right.
    #[test]
    fn a_desynced_live_area_is_redrawn_whole() {
        let _global = live_area_lock();
        let mut term = InlineTerminal::new(40, 6);
        let mut screen = Vt::new(40, 6);
        paint(&mut term, &mut screen, &[], &["a", "b", "c"]);
        // The writer believes the cursor is on row 0; it is on row 2, so
        // the update's moves land two rows too low.
        term.cursor_row = 0;
        let painted = paint_frame(&mut term, &mut screen, &[], &rows(&["a", "B", "C"]), None);
        assert_eq!(painted, Painted::Redrawn);
        assert_eq!(screen.all(), ["a", "B", "C"]);
    }

    /// A changed block whose write the bytes drop fails the check, even
    /// though its rows on the screen copy are the shadow's own: the
    /// frame then goes to the full redraw (`Painted::Redrawn`). The same
    /// holds for a blank row that should now show text.
    #[test]
    fn a_changed_block_the_bytes_never_write_fails_the_check() {
        let _global = live_area_lock();
        let cases = [
            (["a", "b", "c"], r#"live row 1 shows "b", expected "B""#),
            (["a", "", "c"], r#"live row 1 shows "", expected "B""#),
        ];
        for (before, failure) in cases {
            let mut term = InlineTerminal::new(40, 6);
            let mut screen = Vt::new(40, 6);
            paint(&mut term, &mut screen, &[], &before);
            let mut probe = term.clone();
            let old = std::mem::take(&mut probe.live);
            let encoded = encode_rows(&rows(&["a", "B", "c"]));
            let write = format!("{ERASE_LINE}{}", encoded[1].text);
            let bytes = probe.frame_bytes(Redraw::Diff, &old, &[], encoded, None);
            assert!(bytes.contains(&write), "{bytes:?}");
            let dropped = bytes.replacen(&write, "", 1);
            let candidate = probe.check(dropped, &old, &[], None);
            assert_eq!(
                (candidate.failure.as_deref(), candidate.check()),
                (Some(failure), Check::Fail)
            );
        }
    }

    /// A frame no check lets through writes nothing and is reported; its
    /// history rows go out with the next frame, in order.
    #[test]
    fn a_frame_both_checks_reject_is_not_written_and_its_history_waits() {
        let _global = live_area_lock();
        let _stale = take_rejection();
        let mut term = InlineTerminal::new(40, 6);
        let mut screen = Vt::new(40, 6);
        paint(&mut term, &mut screen, &[], &["> |"]);
        // An image row whose raw text moves the cursor up.
        let image = "\x1b[2A\x1b_Ga=T;QUJD\x1b\\";
        let mut out = Vec::new();
        let painted = term
            .paint(
                &mut out,
                InlineFrame {
                    history: &rows(&["kept 1"]),
                    live: &rows(&[image, "> |"]),
                    cursor: None,
                },
            )
            .unwrap();
        let rejection = Rejection {
            message: "frame not shown: live row 0 shows \"> |\", expected \"\"; \
                      full redraw: live row 0 shows \"> |\", expected \"\""
                .to_string(),
        };
        assert_eq!(painted, Painted::Rejected(rejection.clone()));
        assert_eq!(take_rejection(), Some(rejection));
        assert!(out.is_empty());
        paint(&mut term, &mut screen, &["kept 2"], &["> |"]);
        assert_eq!(screen.all(), ["kept 1", "kept 2", "> |"]);
    }

    /// Rejections are logged as they happen; a release with history
    /// still pending reports it instead of dropping it; and the
    /// `REJECTED_FRAMES_LIMIT`th rejection in a row fails the paint with
    /// `ScreenCheckFailed`, so the surface ends instead of freezing. A
    /// frame shown in between starts the count again.
    #[test]
    fn rejections_in_a_row_end_the_surface_and_are_logged() {
        let _global = live_area_lock();
        let _stale = take_rejection();
        let logged = std::sync::Arc::new(Mutex::new(Vec::<String>::new()));
        let sink = std::sync::Arc::clone(&logged);
        log_rejections_with(Box::new(move |message| {
            sink.lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(message.to_string());
        }));
        let mut term = InlineTerminal::new(40, 6);
        let mut screen = Vt::new(40, 6);
        paint(&mut term, &mut screen, &[], &["> |"]);
        let image = "\x1b[2A\x1b_Ga=T;QUJD\x1b\\";
        let bad = rows(&[image, "> |"]);
        let reject = |term: &mut InlineTerminal, history: &[&str]| {
            term.paint(
                &mut Vec::new(),
                InlineFrame {
                    history: &rows(history),
                    live: &bad,
                    cursor: None,
                },
            )
        };
        let message = "frame not shown: live row 0 shows \"> |\", expected \"\"; \
                       full redraw: live row 0 shows \"> |\", expected \"\""
            .to_string();
        let rejection = Rejection {
            message: message.clone(),
        };
        assert_eq!(
            reject(&mut term, &["kept"]).unwrap(),
            Painted::Rejected(rejection.clone())
        );
        term.release(&mut Vec::new()).unwrap();
        assert_eq!(
            take_rejection(),
            Some(Rejection {
                message: "1 history rows of rejected frames are not on screen yet; \
                          the next frame writes them"
                    .to_string()
            })
        );
        let mut term = InlineTerminal::new(40, 6);
        let mut screen = Vt::new(40, 6);
        paint(&mut term, &mut screen, &["above"], &["> |"]);
        assert_eq!(
            reject(&mut term, &[]).unwrap(),
            Painted::Rejected(rejection.clone())
        );
        paint(&mut term, &mut screen, &[], &["> a"]);
        for _ in 1..REJECTED_FRAMES_LIMIT {
            assert_eq!(
                reject(&mut term, &[]).unwrap(),
                Painted::Rejected(rejection.clone())
            );
        }
        let error = reject(&mut term, &[]).unwrap_err();
        assert_eq!(
            error
                .get_ref()
                .and_then(|inner| inner.downcast_ref::<ScreenCheckFailed>()),
            Some(&ScreenCheckFailed {
                frames: REJECTED_FRAMES_LIMIT,
                last: rejection,
            })
        );
        let release_report = "1 history rows of rejected frames are not on screen yet; \
                              the next frame writes them";
        let mut expected = vec![message.clone(), release_report.to_string()];
        expected.extend(std::iter::repeat_n(message, REJECTED_FRAMES_LIMIT + 1));
        assert_eq!(
            *logged.lock().unwrap_or_else(PoisonError::into_inner),
            expected
        );
        *REJECTION_LOG.lock().unwrap_or_else(PoisonError::into_inner) = None;
    }

    /// `present` is the model's table: the full redraw runs only when the
    /// first check fails, and a double failure keeps the first frame.
    #[test]
    fn present_follows_the_model_table() {
        let table = [
            (
                Check::Pass,
                Check::Pass,
                Shown::Drawn {
                    frame: 1,
                    redraw: Redraw::Diff,
                },
                0,
            ),
            (
                Check::Pass,
                Check::Fail,
                Shown::Drawn {
                    frame: 1,
                    redraw: Redraw::Diff,
                },
                0,
            ),
            (
                Check::Fail,
                Check::Pass,
                Shown::Drawn {
                    frame: 2,
                    redraw: Redraw::Full,
                },
                1,
            ),
            (Check::Fail, Check::Fail, Shown::Error { frame: 1 }, 1),
        ];
        for (first, second, shown, runs) in table {
            let ran = std::cell::Cell::new(0);
            let got = present(1, first, || {
                ran.set(ran.get() + 1);
                (2, second)
            });
            assert_eq!((got, ran.get()), (shown, runs));
        }
    }

    /// A styled transcript row 80 to 120 cells wide.
    fn styled_row(n: usize) -> Line {
        use crate::style::{Color, Modifier, Style};
        const PROSE: &str = "the quick brown fox jumps over the lazy dog while the agent streams ";
        let width = 80 + n * 7 % 41;
        vec![
            Span::styled("│ ", Style::new().fg(Color::Indexed(8))),
            Span::raw(
                PROSE
                    .chars()
                    .cycle()
                    .skip(n % 13)
                    .take(width - 24)
                    .collect::<String>(),
            ),
            Span::styled(
                format!(" `fn row_{:05}()` ", n % 100_000),
                Style::new()
                    .fg(Color::Rgb(161, 161, 170))
                    .add_modifier(Modifier::BOLD),
            ),
            Span::styled("→ ok", Style::new().fg(Color::Indexed(2))),
        ]
    }

    /// The cost of the off-screen check: a first frame with 5,000
    /// history rows under a 40-row live area, then 300 streaming frames.
    /// Run with `--ignored --nocapture`.
    #[test]
    #[ignore = "measurement; prints timings"]
    fn verify_cost_on_a_large_transcript() {
        use std::time::{Duration, Instant};
        let _global = live_area_lock();
        let mut term = InlineTerminal::new(120, 50);
        let mut sink = Vec::new();
        let history: Vec<Line> = (0..5_000).map(styled_row).collect();
        let live_at = |frame: usize| -> Vec<Line> {
            let mut live: Vec<Line> = (0..37).map(|n| styled_row(10_000 + n)).collect();
            for (offset, row) in live[34..].iter_mut().enumerate() {
                row.push(Span::raw(format!(" {}", frame * 3 + offset)));
            }
            live.extend(editor_box(120, "> draft"));
            live
        };
        let mut measure = |term: &mut InlineTerminal, history: &[Line], live: &[Line]| {
            let mut probe = term.clone();
            let started = Instant::now();
            let painted = term
                .paint(
                    &mut sink,
                    InlineFrame {
                        history,
                        live,
                        cursor: None,
                    },
                )
                .unwrap();
            let total = started.elapsed();
            assert_eq!(painted, Painted::Drawn);
            let old = std::mem::take(&mut probe.live);
            let encoded_history = encode_rows(history);
            let bytes = probe.frame_bytes(
                Redraw::Diff,
                &old,
                &encoded_history,
                encode_rows(live),
                None,
            );
            let started = Instant::now();
            let candidate = probe.check(bytes, &old, &encoded_history, None);
            let verify = started.elapsed();
            assert_eq!(candidate.failure, None);
            sink.clear();
            (total, verify)
        };
        let (first_total, first_verify) = measure(&mut term, &history, &live_at(0));
        let frames: Vec<(Duration, Duration)> = (1..=300)
            .map(|frame| measure(&mut term, &[], &live_at(frame)))
            .collect();
        let micros = |pick: &dyn Fn(&(Duration, Duration)) -> Duration| {
            let all: Vec<f64> = frames.iter().map(|f| pick(f).as_secs_f64() * 1e6).collect();
            (
                all.iter().sum::<f64>() / all.len() as f64,
                all.iter().copied().fold(0.0, f64::max),
            )
        };
        let with = micros(&|f| f.0);
        let check = micros(&|f| f.1);
        let without = micros(&|f| f.0.saturating_sub(f.1));
        println!(
            "first frame: paint {:.0} us, check {:.0} us",
            first_total.as_secs_f64() * 1e6,
            first_verify.as_secs_f64() * 1e6
        );
        println!("300 frames, mean/max us: paint with check {:.1}/{:.1}, check {:.1}/{:.1}, paint without check {:.1}/{:.1}",
            with.0, with.1, check.0, check.1, without.0, without.1);
    }
}
