//! The yes/no confirm selector: the shared menu grammar (the `>` marker
//! rows and the key-hint status row every picker renders with) over the
//! title, the message as its description lines, and a small option list
//! that answers the pending question.

use crate::keybindings::KeybindingsManager;
use crate::menu_panel::{hint_row, key_hint, menu_row};
use crate::theme::{Theme, ThemeColor};
use crate::width::{truncate_line, wrap_line};
use crate::Line;

/// One answer to the pending question.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConfirmAction {
    /// Enter on an option: its label.
    Select(String),
    /// Escape or ctrl+c: the question was declined.
    Cancel,
    /// Navigation only.
    None,
}

/// A pending confirm. Owns the editor dock while open.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConfirmPanel {
    title: String,
    message: Vec<String>,
    options: Vec<String>,
    selected: usize,
    /// How a message line wider than the pane shows.
    fit: Fit,
}

/// How a message line wider than the pane shows.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Fit {
    /// Cut at the pane's width.
    Truncate,
    /// Wrapped onto more rows: every character shows.
    Wrap,
}

impl ConfirmPanel {
    /// The Yes/No confirm of a pending question (`title`, `message`).
    pub fn yes_no(title: &str, message: &str) -> Self {
        ConfirmPanel {
            title: title.to_string(),
            message: message
                .lines()
                .map(str::trim)
                .filter(|line| !line.is_empty())
                .map(str::to_string)
                .collect(),
            options: vec!["Yes".to_string(), "No".to_string()],
            selected: 0,
            fit: Fit::Truncate,
        }
    }

    /// The Yes/No confirm of a step that may run (a `bash` step, an
    /// `ipython` cell): every line of `message` shows whole and wrapped,
    /// none trimmed or dropped, so the user reads exactly what runs; Enter
    /// alone answers No.
    pub fn approval(title: &str, message: &str) -> Self {
        ConfirmPanel {
            title: title.to_string(),
            message: message.split('\n').map(str::to_string).collect(),
            options: vec!["Yes".to_string(), "No".to_string()],
            selected: 1,
            fit: Fit::Wrap,
        }
    }

    /// One key id (TS `handleInput`: up/down move, confirm selects, escape
    /// and ctrl+c cancel).
    pub fn handle_key(&mut self, kb: &KeybindingsManager, id: &str) -> ConfirmAction {
        if id == "ctrl+c" {
            return ConfirmAction::Cancel;
        }
        if kb.matches(id, "tui.select.cancel") {
            return ConfirmAction::Cancel;
        }
        if kb.matches(id, "tui.select.up") {
            self.selected = self.selected.saturating_sub(1);
            return ConfirmAction::None;
        }
        if kb.matches(id, "tui.select.down") {
            self.selected = (self.selected + 1).min(self.options.len().saturating_sub(1));
            return ConfirmAction::None;
        }
        if kb.matches(id, "tui.select.confirm") {
            return ConfirmAction::Select(
                self.options.get(self.selected).cloned().unwrap_or_default(),
            );
        }
        ConfirmAction::None
    }

    /// The pane's rendered rows.
    #[must_use]
    pub fn render(&self, theme: &Theme, width: usize, kb: &KeybindingsManager) -> Vec<Line> {
        let mut lines: Vec<Line> = Vec::new();
        lines.push(Vec::new());
        lines.push(vec![crate::Span::raw(format!("  {}", self.title))]);
        for line in &self.message {
            let row = vec![theme.fg_span(ThemeColor::Muted, format!("  {line}"))];
            match self.fit {
                Fit::Truncate => lines.push(truncate_line(&row, width, "")),
                Fit::Wrap => lines.extend(wrap_line(&row, width)),
            }
        }
        lines.push(Vec::new());
        for (index, option) in self.options.iter().enumerate() {
            lines.push(menu_row(
                theme,
                width,
                vec![crate::Span::raw(option.clone())],
                &[],
                index == self.selected,
            ));
        }
        lines.push(Vec::new());
        lines.push(hint_row(theme, width, &hint(kb)));
        lines
    }
}

/// The pane's key hint: the shared hint-row grammar, this surface's
/// vocabulary (an unbound action is omitted, never advertised with a
/// default key).
fn hint(kb: &KeybindingsManager) -> String {
    [
        key_hint(kb, &["tui.select.up", "tui.select.down"], "navigate"),
        key_hint(kb, &["tui.select.confirm"], "select"),
        key_hint(kb, &["tui.select.cancel"], "close"),
    ]
    .into_iter()
    .flatten()
    .collect::<Vec<String>>()
    .join(crate::glyphs::SEP)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn kb() -> KeybindingsManager {
        KeybindingsManager::new()
    }

    #[test]
    fn yes_no_moves_and_selects() {
        let mut panel = ConfirmPanel::yes_no("Import session", "Replace current session?");
        assert_eq!(panel.handle_key(&kb(), "down"), ConfirmAction::None);
        assert_eq!(
            panel.handle_key(&kb(), "enter"),
            ConfirmAction::Select("No".to_string())
        );
        assert_eq!(panel.handle_key(&kb(), "up"), ConfirmAction::None);
        assert_eq!(
            panel.handle_key(&kb(), "enter"),
            ConfirmAction::Select("Yes".to_string())
        );
    }

    /// Regression (audit M3): the step question answered Yes on Enter and
    /// trimmed or dropped the lines of the step.
    #[test]
    fn an_approval_answers_no_on_enter_and_keeps_every_line() {
        let mut panel = ConfirmPanel::approval("Allow?", "  indented\n\nlast ");
        assert_eq!(
            (panel.message.clone(), panel.handle_key(&kb(), "enter")),
            (
                vec!["  indented".to_string(), String::new(), "last ".to_string()],
                ConfirmAction::Select("No".to_string())
            )
        );
    }

    #[test]
    fn escape_and_ctrl_c_cancel() {
        let mut panel = ConfirmPanel::yes_no("t", "m");
        assert_eq!(panel.handle_key(&kb(), "escape"), ConfirmAction::Cancel);
        assert_eq!(panel.handle_key(&kb(), "ctrl+c"), ConfirmAction::Cancel);
    }

    #[test]
    fn the_message_lines_render() {
        let theme = crate::theme::Theme::builtin("eukhe", crate::theme::ColorMode::TrueColor);
        let panel = ConfirmPanel::yes_no(
            "Session cwd not found",
            "cwd from session file does not exist\n/old/path\n\ncontinue in current cwd\n/new/path",
        );
        let rows = panel.render(&theme, 80, &kb());
        let text = rows
            .iter()
            .map(|line| {
                line.iter()
                    .map(|span| span.content.clone())
                    .collect::<String>()
            })
            .collect::<Vec<_>>();
        assert!(text.iter().any(|row| row.contains("Session cwd not found")));
        assert!(text
            .iter()
            .any(|row| row.contains("continue in current cwd")));
        assert!(text.iter().any(|row| row.contains("> Yes")));
        assert!(text.iter().any(|row| row.contains("  No")));
        // The shared hint-row grammar (the pickers' vocabulary shape).
        assert!(text
            .iter()
            .any(|row| row.contains("up/down navigate - Enter select - Esc close")));
    }
}
