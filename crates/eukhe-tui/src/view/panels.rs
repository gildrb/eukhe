//! The panel assembly: the dock -- the queued-input strip, the
//! autocomplete overlay, the borderless composer, the status line, and
//! the `/speed` footer -- plus the share loader and reload-box panels
//! that replace the composer in flight.

use super::editor_surface;
use super::{AgentView, ShareLoader};
use crate::style::Style;
use crate::theme::ThemeColor;
use crate::{Line, Span};

impl AgentView {
    /// Render the dock: the queued-input strip, the autocomplete overlay
    /// (when showing), the composer, and the status line under it.
    pub fn render_dock(&mut self, width: usize) -> Vec<Line> {
        // The queued-input strip sits directly above the prompt (TS
        // `queuedMessagesContainer` above the editor).
        let browse_key = {
            let kb = self.editor.keybindings();
            crate::keybindings::format_key_text(&kb.get_keys("app.message.navigateOlder").join("/"))
        };
        let queue_rows = crate::queued::render_queue(&self.theme, &self.queued, &browse_key, width);
        let mut lines = queue_rows;
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

    /// The `/share` loader rows (TS `BorderedLoader` + `CancellableLoader`):
    /// border, spinner + message, cancel hint, border -- replacing the
    /// editor in the dock while `gh gist create` runs.
    pub(super) fn render_share_loader(&self, loader: &ShareLoader, width: usize) -> Vec<Line> {
        let border = self.theme.fg_style(ThemeColor::Border);
        let muted = self.theme.fg_style(ThemeColor::Muted);
        let dim = self.theme.fg_style(ThemeColor::Dim);
        let spinner = crate::glyphs::SPINNER[self.pulse_frame % crate::glyphs::SPINNER.len()];
        let mut rows: Vec<Line> = Vec::with_capacity(7);
        rows.push(vec![Span::styled(
            crate::glyphs::RULE.repeat(width.max(1)),
            border,
        )]);
        let mut row: Line = vec![Span::styled(" ".to_string(), Style::default())];
        // TS `BorderedLoader` wraps a `Loader` with the muted spinner and
        // muted message color fns; the gap between them is the unstyled
        // plain space (the `Loader` pen reset -- see `chat::render_loader`).
        row.push(Span::styled(spinner.to_string(), muted));
        row.push(Span::raw(" ".to_string()));
        row.push(Span::styled(loader.message.clone(), muted));
        rows.push(row);
        rows.push(vec![Span::raw(String::new())]);
        // TS `keyHint("tui.select.cancel", "cancel")`: every key of the
        // binding, first letter capitalized, then the description.
        let key_text = self.editor.keybindings().key_text("tui.select.cancel");
        let mut hint: Line = vec![Span::styled(" ".to_string(), Style::default())];
        hint.push(Span::styled(key_text, dim));
        hint.push(Span::styled(" cancel".to_string(), muted));
        rows.push(hint);
        rows.push(vec![Span::raw(String::new())]);
        rows.push(vec![Span::styled(
            crate::glyphs::RULE.repeat(width.max(1)),
            border,
        )]);
        rows
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
