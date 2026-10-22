//! The panel assembly: the dock -- the queued-input strip, the
//! autocomplete overlay, the borderless composer, the status line, and
//! the `/speed` footer -- plus the reload-box panel that replaces the
//! composer in flight.

use super::editor_surface;
use super::AgentView;
use crate::theme::ThemeColor;
use crate::{Line, Span};

impl AgentView {
    /// Render the dock: the pinned agents block (while anything runs), the
    /// queued-input strip, the autocomplete overlay (when showing), the
    /// composer, and the status line under it.
    pub fn render_dock(&mut self, width: usize) -> Vec<Line> {
        // The pinned agents block heads the dock (omp's subagent HUD above
        // the editor), in fullscreen and inline alike.
        let mut lines = self.render_agents_panel(width);
        // The queued-input strip sits directly above the prompt (TS
        // `queuedMessagesContainer` above the editor).
        let browse_key = {
            let kb = self.editor.keybindings();
            crate::keybindings::format_key_text(&kb.get_keys("app.message.navigateOlder").join("/"))
        };
        lines.extend(crate::queued::render_queue(
            &self.theme,
            &self.queued,
            &browse_key,
            width,
        ));
        lines.extend(self.render_autocomplete_overlay(width));
        let editor_row = lines.len();
        let (editor_rows, cursor) = self.render_editor_surface(width);
        self.dock_cursor = cursor.map(|(row, col)| (editor_row + row, col));
        lines.extend(editor_rows);
        lines.push(crate::status_line::render_status_line(
            &self.chrome,
            self.detail,
            &self.theme,
            width,
        ));
        // The `/speed` footer (TS `footerSlot`, the main container's last
        // child): a dim row only while the display is on with a sample.
        if let Some(speed) = &self.chrome.speed_text {
            lines.push(crate::chrome::render_speed_footer(
                speed,
                &self.theme,
                width,
            ));
        }
        lines
    }

    /// Whether the pinned agents block shows (something runs and the
    /// setting leaves it on): the block's durations tick while it does.
    #[must_use]
    pub fn agents_panel_shown(&self) -> bool {
        self.agents_panel.shown(self.pinned_agents)
    }

    /// The pinned agents block's rows at this frame's clock.
    fn render_agents_panel(&self, width: usize) -> Vec<Line> {
        if !self.agents_panel_shown() {
            return Vec::new();
        }
        let kb = self.editor.keybindings();
        let open_key = kb.key_text("app.subagents.focus");
        let expand_key = kb.key_text("app.subagents.pinned");
        let focused = self.chrome.activity.as_ref().is_some_and(|dock| {
            dock.focused && dock.selected == crate::chrome::ActivityGroup::Subagents
        });
        crate::agents_panel::render_agents_panel(
            &self.agents_panel,
            &crate::agents_panel::PanelView {
                mode: self.pinned_agents,
                stuck_after_secs: self.stuck_after_secs,
                focused,
                open_key: &open_key,
                expand_key: &expand_key,
                frame: self.pulse_frame,
                now: std::time::Instant::now(),
                now_ms: crate::agents_view_state::now_ms(),
            },
            &self.theme,
            width,
        )
    }

    /// The autocomplete dropdown, mounted just above the prompt.
    fn render_autocomplete_overlay(&mut self, width: usize) -> Vec<Line> {
        editor_surface::overlay(&self.editor, &self.theme, width)
    }

    /// The composer (omp `composer.shape: borderless`): the `> ` prompt
    /// row and its wrapped rows, the queue-browse header above them while
    /// a parked message is selected.
    fn render_editor_surface(&mut self, width: usize) -> (Vec<Line>, Option<(usize, usize)>) {
        // TS `getQueueSelectionHeader` (the editor's header line while a
        // parked message is selected): the dim browse text.
        let header = self.queue_selected.as_ref().map(|selected| {
            let keys = {
                let kb = self.editor.keybindings();
                let display =
                    |id: &str| crate::keybindings::format_key_text(&kb.get_keys(id).join("/"));
                crate::queued::QueueBrowseKeys {
                    navigate_older: display("app.message.navigateOlder"),
                    navigate_newer: display("app.message.navigateNewer"),
                    move_earlier: display("app.message.moveEarlier"),
                    move_later: display("app.message.moveLater"),
                    follow_up: display("app.message.followUp"),
                }
            };
            let dim = self.theme.fg_style(ThemeColor::Dim);
            vec![Span::styled(
                crate::queued::browse_header_text(selected, &keys),
                dim,
            )]
        });
        let surface = editor_surface::render(
            &mut self.editor,
            &self.theme,
            width,
            self.terminal_rows,
            header,
            None,
        );
        (surface.rows, surface.cursor)
    }

    /// The `/reload` box (TS `handleReloadCommand`): `DynamicBorder`, blank,
    /// the muted message, blank, `DynamicBorder` -- the editor container's
    /// replacement while the reload runs.
    pub(super) fn render_reload_box(&self, message: &str, width: usize) -> Vec<Line> {
        let border = self.theme.fg_style(ThemeColor::Border);
        let muted = self.theme.fg_style(ThemeColor::Muted);
        let rule = crate::glyphs::RULE.repeat(width.max(1));
        let rows: Vec<Line> = vec![
            vec![Span::styled(rule.clone(), border)],
            vec![Span::raw(String::new())],
            vec![
                Span::raw(" ".to_string()),
                Span::styled(message.to_string(), muted),
            ],
            vec![Span::raw(String::new())],
            vec![Span::styled(rule, border)],
        ];
        rows
    }
}
