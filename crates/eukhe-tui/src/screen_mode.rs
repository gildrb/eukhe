//! Inline or fullscreen surfaces (the `terminal.fullscreen` setting).
//!
//! Inline, a surface paints into the normal screen and finished output
//! goes into native scrollback. Fullscreen, every surface paints a
//! screen-sized frame into the alternate screen (`?1049h`) with SGR
//! wheel reporting on (`?1000h` + `?1006h`, no motion modes). The
//! alternate screen is process-global state: a handoff between two
//! fullscreen surfaces keeps it (the next surface repaints everything),
//! and every exit route leaves it ([`leave_alt_screen`] runs in the
//! exit restore).

use std::io::{self, Write};
use std::sync::atomic::{AtomicBool, Ordering};

use crate::inline_term::{InlineFrame, InlineTerminal, LiveCursor};

/// How the interactive surfaces use the terminal.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ScreenMode {
    /// Paint into the normal screen; finished rows go to scrollback.
    #[default]
    Inline,
    /// Paint screen-sized frames into the alternate screen.
    Fullscreen,
}

impl ScreenMode {
    /// The mode the `terminal.fullscreen` setting selects.
    #[must_use]
    pub fn from_fullscreen_setting(fullscreen: bool) -> Self {
        if fullscreen {
            ScreenMode::Fullscreen
        } else {
            ScreenMode::Inline
        }
    }
}

/// Rows one mouse wheel notch scrolls.
pub(crate) const WHEEL_ROWS: usize = 3;

/// Whether this process has the alternate screen (and the wheel
/// reporting that comes with it) switched on.
static ALT_SCREEN_ACTIVE: AtomicBool = AtomicBool::new(false);

const ALT_SCREEN_ON: &str = "\x1b[?1049h";
const ALT_SCREEN_OFF: &str = "\x1b[?1049l";
/// Button reporting (the wheel is a button) in SGR encoding.
const MOUSE_ON: &str = "\x1b[?1000h\x1b[?1006h";
const MOUSE_OFF: &str = "\x1b[?1006l\x1b[?1000l";
/// Start a synchronized update, clear the screen, and home the cursor:
/// the origin a fresh [`crate::inline_term::InlineTerminal`] paints a
/// full frame from (its paint ends the update, so the clear and the new
/// frame show together).
const CLEAR_HOME: &str = "\x1b[?2026h\x1b[H\x1b[2J";

/// Switch to the alternate screen (kept when already on) and turn wheel
/// reporting on. Whatever the screen shows stays until the caller's
/// [`clear_for_repaint`] and full frame.
///
/// # Errors
///
/// Propagates the write error of `out`.
pub(crate) fn enter_alt_screen(out: &mut impl Write) -> io::Result<()> {
    let mut buf = String::new();
    if !ALT_SCREEN_ACTIVE.swap(true, Ordering::SeqCst) {
        buf.push_str(ALT_SCREEN_ON);
    }
    buf.push_str(MOUSE_ON);
    // A live area painted in the normal screen is not on this screen.
    crate::inline_term::forget_live_area();
    out.write_all(buf.as_bytes())?;
    out.flush()
}

/// Clear the alternate screen and home the cursor for a full repaint;
/// a frame paint must follow.
///
/// # Errors
///
/// Propagates the write error of `out`.
pub(crate) fn clear_for_repaint(out: &mut impl Write) -> io::Result<()> {
    out.write_all(CLEAR_HOME.as_bytes())
}

/// Turn wheel reporting off and leave the alternate screen, if on. The
/// terminal restores the normal screen and its cursor. Returns whether
/// the alternate screen was on.
pub(crate) fn leave_alt_screen(out: &mut impl Write) -> bool {
    if !ALT_SCREEN_ACTIVE.swap(false, Ordering::SeqCst) {
        return false;
    }
    crate::inline_term::forget_live_area();
    let _ = out.write_all(format!("{MOUSE_OFF}{ALT_SCREEN_OFF}").as_bytes());
    let _ = out.flush();
    true
}

/// Fit a fullscreen frame to exactly `height` rows: blank rows pad the
/// bottom, extra rows are cut from the bottom.
pub(crate) fn fill_height(rows: &mut Vec<crate::Line>, height: usize) {
    rows.resize_with(height, Vec::new);
}

/// The writer of a surface that paints its whole frame each time (the
/// agents view, the config selector): inline, a live area at the cursor
/// line; fullscreen, a frame of exactly the terminal's height in the
/// alternate screen.
#[derive(Debug)]
pub(crate) struct SurfaceTerminal {
    term: InlineTerminal,
    mode: ScreenMode,
    /// Whether the screen is set up for `mode` (false until the first
    /// paint, and after a fullscreen resize: the next paint repaints
    /// the whole screen).
    ready: bool,
}

impl SurfaceTerminal {
    #[must_use]
    pub(crate) fn new(mode: ScreenMode, height: u16) -> Self {
        SurfaceTerminal {
            term: InlineTerminal::new(height),
            mode,
            ready: false,
        }
    }

    /// Paint one frame. The first fullscreen paint enters the alternate
    /// screen (a previous fullscreen surface's frame stays until this
    /// one replaces it); the first inline paint leaves it if a previous
    /// surface left it on.
    ///
    /// # Errors
    ///
    /// Propagates the write error of `out`.
    pub(crate) fn paint(
        &mut self,
        out: &mut impl Write,
        mut rows: Vec<crate::Line>,
        cursor: Option<LiveCursor>,
        height: u16,
    ) -> io::Result<()> {
        match self.mode {
            ScreenMode::Inline => {
                if !self.ready && leave_alt_screen(out) {
                    self.term = InlineTerminal::new(height);
                }
            }
            ScreenMode::Fullscreen => {
                fill_height(&mut rows, usize::from(height));
                if !self.ready {
                    enter_alt_screen(out)?;
                    clear_for_repaint(out)?;
                    self.term = InlineTerminal::new(height);
                }
            }
        }
        self.ready = true;
        self.term.set_height(height);
        self.term.paint(
            out,
            InlineFrame {
                history: &[],
                live: &rows,
                cursor,
            },
        )
    }

    /// The terminal resized: the next paint redraws the whole frame at
    /// the new size.
    ///
    /// # Errors
    ///
    /// Propagates the write error of `out`.
    pub(crate) fn resize(&mut self, out: &mut impl Write, height: u16) -> io::Result<()> {
        match self.mode {
            ScreenMode::Inline => {
                self.term.set_height(height);
                self.term.clear_live(out)
            }
            ScreenMode::Fullscreen => {
                self.ready = false;
                Ok(())
            }
        }
    }

    /// Leave no frame behind: inline erases the live area (the next
    /// surface, or the shell, starts at its first row); fullscreen keeps
    /// the alternate screen for the next surface to repaint (an exit
    /// leaves it through the exit restore).
    ///
    /// # Errors
    ///
    /// Propagates the write error of `out`.
    pub(crate) fn clear(&mut self, out: &mut impl Write) -> io::Result<()> {
        match self.mode {
            ScreenMode::Inline => self.term.clear_live(out),
            ScreenMode::Fullscreen => Ok(()),
        }
    }
}

/// The scroll step of a wheel event, `None` for every other mouse
/// event (buttons, drags, and motion are never acted on).
pub(crate) fn wheel_scroll(event: crossterm::event::MouseEvent) -> Option<WheelDirection> {
    use crossterm::event::MouseEventKind;
    match event.kind {
        MouseEventKind::ScrollUp => Some(WheelDirection::Up),
        MouseEventKind::ScrollDown => Some(WheelDirection::Down),
        MouseEventKind::Down(_)
        | MouseEventKind::Up(_)
        | MouseEventKind::Drag(_)
        | MouseEventKind::Moved
        | MouseEventKind::ScrollLeft
        | MouseEventKind::ScrollRight => None,
    }
}

/// One wheel notch.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WheelDirection {
    Up,
    Down,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rows(texts: &[&str]) -> Vec<crate::Line> {
        texts
            .iter()
            .map(|text| vec![crate::Span::raw(*text)])
            .collect()
    }

    /// A fullscreen surface enters the alternate screen with wheel
    /// reporting at its first paint and pads its frame to the full
    /// height; the next surface of a handoff keeps the alternate screen
    /// (no `?1049l`/`?1049h` flash) and repaints the whole screen; the
    /// leave turns reporting off and restores the normal screen.
    #[test]
    fn fullscreen_surfaces_share_the_alternate_screen_across_a_handoff() {
        let _state = crate::exit_restore::TEST_STATE_LOCK.lock();
        leave_alt_screen(&mut Vec::new());

        let mut out = Vec::new();
        let mut first = SurfaceTerminal::new(ScreenMode::Fullscreen, 6);
        first
            .paint(&mut out, rows(&["agents"]), None, 6)
            .expect("paint");
        first.clear(&mut out).expect("handoff");
        let first_text = String::from_utf8(std::mem::take(&mut out)).expect("utf8");
        assert_eq!(first_text.matches("\x1b[?1049h").count(), 1);
        assert!(first_text.contains("\x1b[?1000h\x1b[?1006h"));
        assert!(!first_text.contains("\x1b[?1003h") && !first_text.contains("\x1b[?1002h"));
        // One row plus five blank ones: five row breaks; the handoff
        // leaves the alternate screen on.
        assert!(first_text.contains("agents"));
        assert_eq!(first_text.matches("\r\n").count(), 5, "{first_text:?}");
        assert!(!first_text.contains("\x1b[?1049l"));

        let mut second = SurfaceTerminal::new(ScreenMode::Fullscreen, 6);
        second
            .paint(&mut out, rows(&["chat"]), None, 6)
            .expect("paint");
        let second_text = String::from_utf8(std::mem::take(&mut out)).expect("utf8");
        assert!(!second_text.contains("\x1b[?1049"), "{second_text:?}");
        assert!(second_text.contains("\x1b[H\x1b[2J"), "{second_text:?}");

        assert!(leave_alt_screen(&mut out));
        assert_eq!(
            String::from_utf8(out).expect("utf8"),
            "\x1b[?1006l\x1b[?1000l\x1b[?1049l"
        );
        assert!(!leave_alt_screen(&mut Vec::new()));
    }

    /// An inline surface never touches the alternate screen or mouse
    /// reporting, and paints only its own rows.
    #[test]
    fn inline_surfaces_stay_on_the_normal_screen() {
        let _state = crate::exit_restore::TEST_STATE_LOCK.lock();
        leave_alt_screen(&mut Vec::new());
        let mut out = Vec::new();
        let mut surface = SurfaceTerminal::new(ScreenMode::Inline, 6);
        surface
            .paint(&mut out, rows(&["one", "two"]), None, 6)
            .expect("paint");
        let text = String::from_utf8(out).expect("utf8");
        assert!(!text.contains("\x1b[?1049") && !text.contains("\x1b[?1000"));
        assert_eq!(text.matches("\r\n").count(), 1, "{text:?}");
    }
}
