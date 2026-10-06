//! Shared tool-card row output: the rows a card paints, then the panel
//! shell around them.

use crate::style::Style;

use super::{image_rows, panel_header, panel_line, ToolCallCard, ToolResultView};
use crate::theme::{Theme, ThemeBg};
use crate::width::{wrap_line, wrap_text};
use crate::Line;

pub(super) fn panel_content_width(width: usize) -> usize {
    width.saturating_sub(4).max(1)
}

pub(super) struct RowOutput(Vec<Line>);

impl RowOutput {
    pub(super) fn new() -> Self {
        Self(Vec::new())
    }
    pub(super) fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    pub(super) fn push(&mut self, row: Line) {
        self.0.push(row);
    }
    pub(super) fn blank(&mut self) {
        self.push(Vec::new());
    }
    pub(super) fn wrapped_line(&mut self, line: &Line, width: usize) {
        self.0.extend(wrap_line(line, width));
    }
    pub(super) fn wrapped_text(&mut self, text: &str, style: Style, width: usize) {
        self.0.extend(wrap_text(text, width).into_iter().map(|row| {
            row.into_iter()
                .map(|mut span| {
                    span.style = style;
                    span
                })
                .collect()
        }));
    }
    pub(super) fn images(
        &mut self,
        result: Option<&ToolResultView>,
        show_images: bool,
        theme: &Theme,
    ) {
        self.0.extend(image_rows(result, show_images, theme));
    }
    /// Wrap the rows so far in the tool panel: the header row, then (when
    /// any rows exist) a blank row and every row on the panel background.
    pub(super) fn panel(&mut self, card: &ToolCallCard, frame: usize, theme: &Theme, width: usize) {
        let bg = theme.bg_style(ThemeBg::ToolPanelBg);
        let children = std::mem::take(&mut self.0);
        self.0
            .push(panel_line(panel_header(card, frame, theme), bg, width));
        if !children.is_empty() {
            self.0.push(panel_line(Vec::new(), bg, width));
            self.0.extend(
                children
                    .into_iter()
                    .map(|child| panel_line(child, bg, width)),
            );
        }
    }
    pub(super) fn into_lines(self) -> Vec<Line> {
        self.0
    }
}
