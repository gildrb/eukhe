//! The chat frame for the inline terminal (docs/interface.md S8): newly
//! committed entries as history, then the live area -- unsettled
//! entries, the transcript tail, toasts, and the dock or the open panel
//! -- and the caret.
//!
//! Committed rows are never written again. A new width, theme, detail
//! level, image setting, or code indent applies to the live area and to
//! the rows committed after it; the scrollback keeps what it holds.

use super::{ledger, AgentView};
use crate::inline_term::LiveCursor;
use crate::style::Modifier;
use crate::Line;

/// The inputs the fullscreen window's cached rows were rendered at. A
/// fullscreen frame at another shape renders them again and repaints.
pub(super) struct RenderShape {
    width: usize,
    detail: crate::chat::Detail,
    theme: crate::theme::Theme,
    code_block_indent: String,
    show_images: bool,
}

/// What the inline terminal holds of the current transcript.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Scrollback {
    /// Nothing: the next inline frame is the first paint.
    Empty,
    /// The rows of a transcript the chat replaced: they stay as written.
    /// The next inline frame writes one separator row that names the
    /// break, and the new transcript's history goes below it.
    Replaced(TranscriptBreak),
    /// The committed rows of this transcript.
    Written,
}

/// Why the chat holds a new transcript; the separator row names it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TranscriptBreak {
    /// Another session: a switch, `/new`, a resume, a rebind.
    Session,
    /// The same session, fetched again after a reconnect.
    Resync,
    /// The same session, rebuilt: a fork or tree move, `/reload`, a
    /// refetch after a compaction.
    Rebuild,
}

/// One composed chat frame for [`crate::inline_term::InlineTerminal`].
#[derive(Debug)]
pub struct ChatFrame {
    /// How this frame relates to what the terminal shows.
    pub start: FrameStart,
    /// Rows that move into scrollback with this frame.
    pub history: Vec<Line>,
    /// The live area, top to bottom.
    pub live: Vec<Line>,
    /// The caret within `live`, when the editor has focus.
    pub(crate) cursor: Option<LiveCursor>,
}

/// How a composed frame relates to the frames before it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FrameStart {
    /// The surface's first frame: the splash, then the history so far.
    First,
    /// Fullscreen only: the size, a render setting, or the transcript
    /// changed, so the alternate screen is painted again in full. An
    /// inline frame never has it: the inline terminal redraws its live
    /// area on a width change and keeps the scrollback.
    Reshaped,
    /// The rows composed before still hold.
    Continue,
}

impl AgentView {
    /// Refresh the loader's elapsed time for this frame.
    pub(super) fn refresh_loader(&mut self) {
        if let (Some(working), Some(since)) = (&mut self.working, self.working_since) {
            working.elapsed_secs = since.elapsed().as_secs();
        }
    }

    /// Compare the render inputs with the fullscreen window's last shape
    /// and keep the new one. Returns how the fullscreen frame starts.
    pub(super) fn begin_fullscreen_frame(&mut self, width: usize) -> FrameStart {
        let layout_holds = |shape: &RenderShape| {
            shape.width == width
                && shape.detail == self.detail
                && shape.show_images == self.show_images
                && shape.code_block_indent == self.code_block_indent
        };
        // The theme compares by generation first: an unchanged theme costs
        // one integer compare, a re-resolved one its tables.
        let start = match &self.fullscreen_shape {
            None => FrameStart::First,
            Some(shape)
                if self.viewport.stale || !layout_holds(shape) || shape.theme != self.theme =>
            {
                FrameStart::Reshaped
            }
            Some(_) => FrameStart::Continue,
        };
        self.viewport.stale = false;
        // The shape is rebuilt only when something in it changed.
        let current = self.fullscreen_shape.as_ref().is_some_and(|shape| {
            layout_holds(shape) && shape.theme.generation() == self.theme.generation()
        });
        if !current {
            self.fullscreen_shape = Some(RenderShape {
                width,
                detail: self.detail,
                theme: self.theme.clone(),
                code_block_indent: self.code_block_indent.clone(),
                show_images: self.show_images,
            });
        }
        start
    }

    /// Compose the next frame for a `width` x `height` terminal. One
    /// frame is one step of the transcript protocol: the streamed text
    /// reveals one more paced step, the ledger opens a block for each new
    /// entry and finishes each settled one up to the first that is not,
    /// and the flush commits the final prefix: those entries' rows become
    /// history, written once at the current width. Then the live area is
    /// laid out.
    pub fn compose(&mut self, width: usize, height: usize) -> ChatFrame {
        self.refresh_loader();
        // The splash goes into scrollback once, with the first frame; a
        // new transcript starts below one separator row.
        let (start, mut history) = match self.scrollback {
            Scrollback::Empty => (FrameStart::First, self.splash_rows(width)),
            Scrollback::Replaced(why) => (
                FrameStart::Continue,
                vec![self.transcript_break_row(why, width)],
            ),
            Scrollback::Written => (FrameStart::Continue, Vec::new()),
        };
        self.scrollback = Scrollback::Written;
        let mut events = Vec::new();
        if self.ledger.width() != width {
            events.push(ledger::Event::Resize(width));
        }
        self.advance_paces();
        events.extend((self.ledger.len()..self.chat.len()).map(|_| ledger::Event::Open));
        for index in self.ledger.committed()..self.chat.len() {
            if !self.entry_settled(index) {
                break;
            }
            events.push(ledger::Event::Finish(index));
        }
        events.push(ledger::Event::Flush);
        for index in self.ledger.apply(&events) {
            history.extend(self.render_entry_at(index, width));
            self.paces.remove(&index);
        }
        let (live, cursor) = self.compose_live(width, height);
        ChatFrame {
            start,
            history,
            live,
            cursor,
        }
    }

    /// The separator row above a new transcript: a dim rule that names
    /// the break and the session, cut to `width`.
    fn transcript_break_row(&self, why: TranscriptBreak, width: usize) -> Line {
        let label = match why {
            TranscriptBreak::Session => "new session",
            TranscriptBreak::Resync => "reconnected",
            TranscriptBreak::Rebuild => "transcript rebuilt",
        };
        let rule = crate::glyphs::RULE;
        let mut text = match &self.chrome.session_name {
            Some(name) => format!("{rule}{rule} {label}: {name} "),
            None => format!("{rule}{rule} {label} "),
        };
        let used = crate::width::str_width(&text);
        text.push_str(&rule.repeat(width.saturating_sub(used)));
        vec![self.theme.fg(
            crate::theme::ThemeColor::Dim,
            crate::width::truncate_to_width(&text, width, ""),
        )]
    }

    /// The live area: the dock (or the open panel) at the bottom, and
    /// above it a vertical stack (`stack::vstack`) of the unsettled
    /// entries, the transcript tail, and the toasts, in the rows the dock
    /// leaves free. The children are cut from their top, newest first, so
    /// they fit: the stack then draws each one whole. The onboarding pane
    /// owns the whole area.
    fn compose_live(&mut self, width: usize, height: usize) -> (Vec<Line>, Option<LiveCursor>) {
        if let Some(screen) = self.onboarding.as_mut() {
            let kb = self.editor.keybindings();
            return (screen.render(&self.theme, width, height, kb), None);
        }
        let (dock, editor_focused) = self.compose_dock(width);
        let budget = height.saturating_sub(dock.len());
        // Bottom-up: the toasts, the transcript tail, then the unsettled
        // entries newest first until the budget fills -- entries wholly
        // above the live area never render, and a streaming message
        // copies only the rows that show.
        let mut children: Vec<Vec<Line>> = Vec::new();
        let mut filled: usize = 0;
        for mut child in [self.toast_rows(width), self.render_transcript_tail(width)] {
            child.drain(..child.len().saturating_sub(budget - filled));
            filled += child.len();
            children.push(child);
        }
        for index in (self.ledger.committed()..self.chat.len()).rev() {
            if filled >= budget {
                break;
            }
            let entry = self.render_entry_tail(index, width, budget - filled);
            filled += entry.len();
            children.push(entry);
        }
        children.reverse();
        let mut rows = super::stack::stack_rows(children, budget);
        let cursor = self
            .dock_cursor
            .filter(|_| editor_focused)
            .map(|(row, col)| LiveCursor {
                row: rows.len() + row,
                col,
            });
        rows.extend(dock);
        (rows, cursor)
    }

    /// The active action toasts as rows.
    pub(super) fn toast_rows(&self, width: usize) -> Vec<Line> {
        let toasts = self.toasts.active(std::time::Instant::now());
        if toasts.is_empty() {
            return Vec::new();
        }
        // The action ack renders as the brand-purple pill: the theme's
        // Accent token flipped onto the pill's background.
        let style = self
            .theme
            .fg_style(crate::theme::ThemeColor::Accent)
            .add_modifier(Modifier::REVERSED);
        crate::toast::render_toasts(&toasts, width, style)
    }

    /// The dock rows and whether the editor holds the focus: the docked
    /// pickers and panels replace the composer and the status line (TS
    /// `showConfigurationMenu`/`showSelector` replace the editor
    /// container).
    pub(super) fn compose_dock(&mut self, width: usize) -> (Vec<Line>, bool) {
        // The read-only info panel's CURRENT row budget (a terminal resize
        // re-budgets an open panel every frame, never a stale open-time
        // value): read before the panel borrow below.
        let info_viewport_rows = crate::session_ui::picker_viewport_rows(self.terminal_rows());
        let dock_height = self.terminal_rows();
        let kb = self.editor.keybindings();
        let picker_dock: Option<Vec<Line>> = if let Some(picker) = self.model_picker.as_mut() {
            Some(picker.render(&self.theme, width, kb))
        } else if let Some(picker) = &self.effort_picker {
            Some(picker.render(&self.theme, width, kb))
        } else if let Some(picker) = &self.workflow_size_picker {
            Some(picker.render(&self.theme, width, kb))
        } else if let Some(mcp_view) = self.mcp_view.as_mut() {
            Some(mcp_view.render(&self.theme, width, kb))
        } else if let Some(factory_view) = self.factory_view.as_ref() {
            Some(factory_view.render(&self.theme, width, kb))
        } else if let Some(page) = self.workflow_view.as_ref() {
            Some(page.render(&self.theme, width, kb))
        } else if let Some(picker) = &self.heartbeats_picker {
            Some(picker.render(&self.theme, width, kb))
        } else if let Some(panel) = &self.goal_panel {
            Some(crate::goal_surface::render_goal_panel(
                panel,
                &self.theme,
                width,
                kb,
            ))
        } else if let Some(view) = self.bash_view.as_ref() {
            Some(view.render(&self.theme, width, kb))
        } else if let Some(panel) = self.info_panel.as_mut() {
            Some(panel.render(
                &self.theme,
                width,
                kb,
                &self.code_block_indent,
                info_viewport_rows,
            ))
        } else if let Some(tree) = self.memory_tree.as_mut() {
            Some(tree.render(&self.theme, width, kb, info_viewport_rows))
        } else {
            None
        };
        // The tree and fork selectors mount in the editor container (TS
        // `showSelector`): an auto-height pane in the dock's place with the
        // transcript above it.
        let selector_dock: Option<Vec<Line>> = if let Some(selector) = self.tree_selector.as_ref() {
            Some(selector.render(&self.theme, width, kb))
        } else if let Some(selector) = self.fork_selector.as_ref() {
            Some(selector.render(&self.theme, width, kb))
        } else if let Some(confirm) = self.confirm.as_ref() {
            Some(confirm.render(&self.theme, width, kb))
        } else if let Some(selector) = self.provider_auth.as_mut() {
            Some(selector.render(&self.theme, width, kb))
        } else if let Some(panel) = self.auth_panel.as_mut() {
            Some(panel.render(&self.theme, width, usize::from(dock_height), kb))
        } else if let Some(message) = self.reload_box.as_ref() {
            Some(self.render_reload_box(message, width))
        } else if let Some(menu) = self.settings_menu.as_ref() {
            Some(menu.render(&self.theme, width, kb))
        } else {
            picker_dock
        };
        match selector_dock {
            // The replacement surfaces swap only the editor part of the
            // dock; the `/speed` footer stays the dock's last row under
            // them (TS `footerSlot` renders while `showSelector`/the
            // pickers own the frame).
            Some(mut dock) => {
                if let Some(speed) = &self.chrome.speed_text {
                    dock.push(crate::chrome::render_speed_footer(
                        speed,
                        &self.theme,
                        width,
                    ));
                }
                (dock, false)
            }
            None => (self.render_dock(width), true),
        }
    }
}
