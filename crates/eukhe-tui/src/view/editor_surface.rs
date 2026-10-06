//! The borderless composer: the shared renderer for every editor-bearing
//! surface -- the chat's prompt and the agents view's action composers.
//! The surfaces compose it with their own headers and placeholders.
//!
//! The row shape (omp `composer.shape: borderless`): the caller's header
//! line when one is set, then the content rows -- `> ` on the first row,
//! wrapped rows indented under it, the reverse-video cursor -- on the
//! terminal's own background. A `^ N more` / `v N more` row shows only
//! while content hides above or below the editor's window. An empty
//! editor with a placeholder shows the cursor cell, then the dim
//! placeholder.

use super::chunk_selection;
use crate::editor::Editor;
use crate::prompt_highlight::{
    command_token, editor_chunk_highlights, editor_text_spans, find_arg_tokens, ArgTokenSpan,
};
use crate::style::{Modifier, Style};
use crate::theme::{Theme, ThemeBg, ThemeColor};
use crate::width::{str_width, truncate_to_width};
use crate::{Line, Span};
use eukhe_types::slash_commands::SlashCommandRegistry;

/// The composed editor rows and the cursor's cell.
pub(crate) struct EditorBox {
    /// The rows, the header (when set) first.
    pub(crate) rows: Vec<Line>,
    /// The cursor's row within `rows` and its column (`None` while the
    /// editor's window shows no cursor).
    pub(crate) cursor: Option<(usize, usize)>,
}

/// Compose the editor rows. `header` carries the caller's header line
/// (the chat's queue-browse header, an action composer's own header).
/// `placeholder` replaces the first content row while the editor is empty
/// (TS `renderPlaceholderLine`, the placeholder dim).
pub(crate) fn render(
    editor: &mut Editor,
    theme: &Theme,
    width: usize,
    terminal_rows: u16,
    header: Option<Line>,
    placeholder: Option<&str>,
) -> EditorBox {
    let plain = Style::default();
    let dim = theme.fg_style(ThemeColor::Dim);
    // TS `getPromptPrefix`: a bang first line swaps the `> ` for the
    // `! `/`!! ` prompt (styled through the bash-mode color), which also
    // narrows the input width.
    let bash_prompt = editor.bash_prompt_prefix();
    let prompt = bash_prompt.unwrap_or("> ");
    let prompt_style = if bash_prompt.is_some() {
        theme.fg_style(ThemeColor::BashMode)
    } else {
        plain
    };
    let prompt_width = str_width(prompt);
    let input_width = width.saturating_sub(prompt_width).max(1);
    let (visible, scroll_offset, _hidden_above, hidden_below) =
        editor.visible_window(input_width, terminal_rows);
    let mut rows: Vec<Line> = Vec::new();
    if let Some(header) = header {
        rows.push(crate::width::truncate_line(&header, width, "..."));
    }
    if scroll_offset > 0 {
        rows.push(vec![Span::styled(
            format!("{} {scroll_offset} more", crate::glyphs::UP),
            dim,
        )]);
    }
    let content_offset = rows.len();
    // TS `CustomEditor.render`: a bare `--` separator highlights only
    // while the first line opens with an argument-taking slash command.
    let selection = editor.selection_range();
    let editor_lines = editor.get_lines();
    let registry = SlashCommandRegistry::builtin_cached();
    let include_bare_separator = editor_lines
        .first()
        .and_then(|first| command_token(first))
        .is_some_and(|token| registry.takes_argument(&token.name));
    let arg_token_spans: Vec<Vec<ArgTokenSpan>> = editor_lines
        .iter()
        .map(|line| find_arg_tokens(line, 0, include_bare_separator))
        .collect();
    let mut cursor: Option<(usize, usize)> = None;
    let placeholder_row = placeholder.filter(|_| editor.get_text().is_empty());
    for (index, line) in visible.iter().enumerate() {
        let lead = if index == 0 && scroll_offset == 0 {
            Span::styled(prompt.to_string(), prompt_style)
        } else {
            Span::raw(" ".repeat(prompt_width))
        };
        if let (0, Some(text)) = (index, placeholder_row) {
            let text = truncate_to_width(text, input_width.saturating_sub(1), "");
            rows.push(vec![
                lead,
                Span::styled(" ".to_string(), plain.add_modifier(Modifier::REVERSED)),
                Span::styled(text, dim),
            ]);
            cursor = Some((content_offset, prompt_width));
            continue;
        }
        let mut row: Line = vec![lead];
        let text: &str = &line.text;
        let cursor_pos = line
            .has_cursor
            .then(|| line.cursor_pos.min(text.chars().count()));
        // The prompt-highlight spans of this chunk: argument tokens, and
        // the command token of the first layout line in accent unless
        // the cursor sits inside it (TS `styleDisplayText`).
        let command = (scroll_offset + index == 0)
            .then(|| command_token(text))
            .flatten();
        let highlights = editor_chunk_highlights(
            text,
            arg_token_spans
                .get(line.source_line)
                .map_or(&[][..], |spans| spans),
            line.source_start,
            command.as_ref(),
            cursor_pos,
        );
        row.extend(editor_text_spans(
            theme,
            text,
            &highlights,
            chunk_selection(selection, line.source_line, line.source_start, text),
            cursor_pos,
            plain,
        ));
        if let Some(position) = cursor_pos {
            let head = split_at_chars(text, position).0;
            cursor = Some((content_offset + index, str_width(head) + prompt_width));
        }
        rows.push(row);
    }
    if hidden_below > 0 {
        rows.push(vec![Span::styled(
            format!("{} {hidden_below} more", crate::glyphs::DOWN),
            dim,
        )]);
    }
    EditorBox { rows, cursor }
}

/// The autocomplete dropdown, mounted just above the prompt (TS anchors
/// the overlay immediately above the cursor row; the editor's first
/// content row carries the cursor in the common single-line case). The
/// panel opens with the one full-width muted rule every inline menu panel
/// opens with (the operator's 2026-09-26 top-border directive), its rows
/// start under the input column and float on the popup background, and
/// the selected row's wash spans the panel's full width like the
/// `/model` picker's selected row.
pub(crate) fn overlay(editor: &Editor, theme: &Theme, width: usize) -> Vec<Line> {
    let Some(state) = editor.autocomplete_state() else {
        return Vec::new();
    };
    let bg = theme.bg_style(ThemeBg::ToolPanelBg);
    let selection = theme.soft_selection_style();
    // The overlay anchors against the live prompt prefix (TS
    // `getRenderMetrics`'s `promptPrefixWidth`, the `!`/`!!` prompts
    // included).
    let prompt_width = str_width(editor.bash_prompt_prefix().unwrap_or("> "));
    let input_width = width.saturating_sub(prompt_width).max(1);
    // The panel's top border: the muted rule that separates an
    // inline menu panel from the rows above it, drawn on the panel
    // surface.
    let border = theme.fg_style(ThemeColor::BorderMuted).patch(bg);
    let mut rows: Vec<Line> = vec![vec![Span::styled(
        crate::glyphs::RULE.repeat(width.max(1)),
        border,
    )]];
    let mut overlay = Vec::new();
    overlay.extend(state.render(theme, input_width));
    overlay.push(Vec::new());
    for mut line in overlay {
        // The shared menu rows pad to the full input width with
        // unstyled spans, so the remaining-width fill below never
        // lands: the popup background must ride on every span the
        // row left unstyled. The selected row is the one whose spans
        // carry the selection band: its edge padding washes with the
        // selection too, so the band spans the panel's full width
        // instead of stopping at the input's edges.
        let selected = line.iter().any(|span| span.style.bg.is_some());
        for span in &mut line {
            if span.style.bg.is_none() {
                span.style = span.style.patch(bg);
            }
        }
        let used: usize = line.iter().map(|s| str_width(&s.content)).sum();
        let edge = if selected { bg.patch(selection) } else { bg };
        let mut row: Line = vec![Span::styled(" ".repeat(prompt_width), edge)];
        row.extend(line);
        row.push(Span::styled(
            " ".repeat(input_width.saturating_sub(used)),
            edge,
        ));
        rows.push(row);
    }
    rows
}

/// Split `text` after its first `at` chars (the whole text when shorter).
fn split_at_chars(text: &str, at: usize) -> (&str, &str) {
    match text.char_indices().nth(at) {
        Some((index, _)) => (&text[..index], &text[index..]),
        None => (text, ""),
    }
}
