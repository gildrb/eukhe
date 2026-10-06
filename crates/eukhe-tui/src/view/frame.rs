//! The chat frame for the inline terminal: newly settled entries as
//! history, then the live area -- unsettled entries, the transcript tail,
//! toasts, and the dock or the open panel -- and the caret.

use super::AgentView;
use crate::chrome::render_splash;
use crate::inline_term::LiveCursor;
use crate::style::{Modifier, Style};
use crate::width::str_width;
use crate::{Line, Span};

/// What the scrollback was rendered at. A frame at another shape
/// replays the history.
#[derive(Debug, Clone, PartialEq)]
pub(super) struct HistoryShape {
    width: usize,
    detail: crate::chat::Detail,
    theme: crate::theme::Theme,
    code_block_indent: String,
    show_images: bool,
}

/// One composed chat frame for [`crate::inline_term::InlineTerminal`].
#[derive(Debug, Default)]
pub struct ChatFrame {
    /// The screen and scrollback must be cleared before this frame:
    /// `history` is the full replay (splash and every settled entry).
    pub replay: bool,
    /// Rows that move into scrollback with this frame.
    pub history: Vec<Line>,
    /// The live area, top to bottom.
    pub live: Vec<Line>,
    /// The caret within `live`, when the editor has focus.
    pub(crate) cursor: Option<LiveCursor>,
}

/// How a composed frame relates to the frames before it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum FrameStart {
    /// The surface's first frame.
    First,
    /// The shape changed or a replay was requested: every row is redone.
    Replay,
    /// The rows composed before still hold.
    Continue,
}

impl AgentView {
    /// Start a frame at `width`: refresh the loader's elapsed time and
    /// decide whether the frame replays. A first or replay frame starts
    /// the commit cursor over.
    pub(super) fn begin_frame(&mut self, width: usize) -> FrameStart {
        if let (Some(working), Some(since)) = (&mut self.working, self.working_since) {
            working.elapsed_secs = since.elapsed().as_secs();
        }
        let shape = HistoryShape {
            width,
            detail: self.detail,
            theme: self.theme.clone(),
            code_block_indent: self.code_block_indent.clone(),
            show_images: self.show_images,
        };
        let start = match &self.history_shape {
            None => FrameStart::First,
            Some(previous) if self.replay_requested || *previous != shape => FrameStart::Replay,
            Some(_) => FrameStart::Continue,
        };
        if start != FrameStart::Continue {
            self.committed = 0;
        }
        self.replay_requested = false;
        self.history_shape = Some(shape);
        start
    }

    /// Compose the next frame for a `width` x `height` terminal: advance
    /// the commit cursor over the settled prefix of the chat (their rows
    /// become history), then lay out the live area. A changed shape or a
    /// change that reached scrollback makes this a replay frame.
    pub fn compose(&mut self, width: usize, height: usize) -> ChatFrame {
        let start = self.begin_frame(width);
        let mut history = Vec::new();
        // The splash goes into scrollback once, with the surface's first
        // frame, and again with every replay.
        if start != FrameStart::Continue && !self.splash_suppressed {
            history = render_splash(&self.chrome, &self.theme, width);
        }
        while self.committed < self.chat.len() && self.entry_settled(self.committed) {
            history.extend(self.render_entry_at(self.committed, width));
            self.committed += 1;
        }
        let (live, cursor) = self.compose_live(width, height);
        ChatFrame {
            replay: start == FrameStart::Replay,
            history,
            live,
            cursor,
        }
    }

    /// The live area: the dock (or the open panel) at the bottom, and
    /// above it the unsettled entries, the transcript tail, and the
    /// toasts, clipped from the top to the rows the dock leaves free. The
    /// onboarding pane owns the whole area.
    fn compose_live(&mut self, width: usize, height: usize) -> (Vec<Line>, Option<LiveCursor>) {
        if let Some(screen) = self.onboarding.as_mut() {
            let kb = self.editor.keybindings();
            return (screen.render(&self.theme, width, height, kb), None);
        }
        let (dock, editor_focused) = self.compose_dock(width);
        let mut rows: Vec<Line> = Vec::new();
        for index in self.committed..self.chat.len() {
            rows.extend(self.render_entry_at(index, width));
        }
        rows.extend(self.render_transcript_tail(width));
        rows.extend(self.toast_rows(width));
        let budget = height.saturating_sub(dock.len());
        if rows.len() > budget {
            rows.drain(..rows.len() - budget);
        }
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
    /// pickers and panels replace the editor part of the dock (TS
    /// `showConfigurationMenu`/`showSelector` replace the editor
    /// container) and keep the prompt context above them.
    pub(super) fn compose_dock(&mut self, width: usize) -> (Vec<Line>, bool) {
        let prompt_context = self.prompt_context_rows(width);
        // The read-only info panel's CURRENT row budget (a terminal resize
        // re-budgets an open panel every frame, never a stale open-time
        // value): read before the panel borrow below.
        let info_viewport_rows = crate::session_ui::picker_viewport_rows(self.terminal_rows());
        let picker_dock: Option<Vec<Line>> = if let Some(picker) = self.model_picker.as_mut() {
            let mut dock = prompt_context;
            dock.extend(picker.render(&self.theme, width, self.editor.keybindings()));
            Some(dock)
        } else if let Some(picker) = &self.effort_picker {
            let mut dock = prompt_context;
            dock.extend(picker.render(&self.theme, width, self.editor.keybindings()));
            Some(dock)
        } else if let Some(mcp_view) = self.mcp_view.as_mut() {
            let mut dock = prompt_context;
            dock.extend(mcp_view.render(&self.theme, width, self.editor.keybindings()));
            Some(dock)
        } else if let Some(factory_view) = self.factory_view.as_ref() {
            let mut dock = prompt_context;
            dock.extend(factory_view.render(&self.theme, width, self.editor.keybindings()));
            Some(dock)
        } else if let Some(picker) = &self.heartbeats_picker {
            let mut dock = prompt_context;
            dock.extend(picker.render(&self.theme, width, self.editor.keybindings()));
            Some(dock)
        } else if let Some(panel) = &self.goal_panel {
            let mut dock = prompt_context;
            dock.extend(crate::goal_surface::render_goal_panel(
                panel,
                &self.theme,
                width,
                self.editor.keybindings(),
            ));
            Some(dock)
        } else if let Some(view) = self.bash_view.as_ref() {
            let mut dock = prompt_context;
            dock.extend(view.render(&self.theme, width, self.editor.keybindings()));
            Some(dock)
        } else if let Some(panel) = self.info_panel.as_mut() {
            let mut dock = prompt_context;
            dock.extend(panel.render(
                &self.theme,
                width,
                self.editor.keybindings(),
                &self.code_block_indent,
                info_viewport_rows,
            ));
            Some(dock)
        } else {
            None
        };
        // The tree and fork selectors mount in the editor container (TS
        // `showSelector`): an auto-height pane over the dock's rows with the
        // transcript above it.
        let selector_dock: Option<Vec<Line>> = if self.tree_selector.is_some()
            || self.fork_selector.is_some()
            || self.share_loader.is_some()
            || self.confirm.is_some()
            || self.provider_auth.is_some()
            || self.auth_panel.is_some()
            || self.reload_box.is_some()
            || self.settings_menu.is_some()
        {
            // TS's editor container holds the prompt context (the detail
            // hint) and the editor; `showSelector` replaces only the editor
            // part, so the hint stays above the pane.
            let mut dock = self.prompt_context_rows(width);
            if let Some(selector) = self.tree_selector.as_ref() {
                dock.extend(selector.render(&self.theme, width, self.editor.keybindings()));
            } else if let Some(selector) = self.fork_selector.as_ref() {
                dock.extend(selector.render(&self.theme, width, self.editor.keybindings()));
            } else if let Some(loader) = self.share_loader.as_ref() {
                dock.extend(self.render_share_loader(loader, width));
            } else if let Some(confirm) = self.confirm.as_ref() {
                dock.extend(confirm.render(&self.theme, width, self.editor.keybindings()));
            } else if let Some(selector) = self.provider_auth.as_mut() {
                dock.extend(selector.render(&self.theme, width, self.editor.keybindings()));
            } else if let Some(panel) = self.auth_panel.as_mut() {
                let kb = self.editor.keybindings();
                dock.extend(panel.render(&self.theme, width, kb));
            } else if let Some(message) = self.reload_box.as_ref() {
                dock.extend(self.render_reload_box(message, width));
            } else if let Some(menu) = self.settings_menu.as_ref() {
                dock.extend(menu.render(&self.theme, width, self.editor.keybindings()));
            }
            Some(dock)
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

    /// The prompt-context rows above the editor or the open panel.
    pub(super) fn prompt_context_rows(&self, width: usize) -> Vec<Line> {
        crate::chrome::render_prompt_context(&self.chrome, &self.detail_label(), &self.theme, width)
    }
}

/// One scroll-indicator surface row (`^ N more` on the editor background).
pub(super) fn indicator_row(indicator: &str, bg: Style, border: Style, width: usize) -> Line {
    // The indicator text paints on the editor surface's background too
    // (operator directive 2026-09-26): the bar's `up/down N more` rows read
    // as part of the prompt bar, not as text floating on the terminal's
    // bare background.
    let mut row: Line = vec![Span::styled(indicator.to_string(), border.patch(bg))];
    let used = str_width(indicator);
    row.push(Span::styled(" ".repeat(width.saturating_sub(used)), bg));
    row
}
