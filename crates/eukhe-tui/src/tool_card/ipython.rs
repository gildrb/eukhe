//! The `ipython` tool-call card, a port of the TS `ipython-cell.ts`:
//! a fixed collapsed summary line (marker, language, preview, line counts,
//! duration, error name) plus, in the expanded conversation-detail mode,
//! the full cell source and its output below. The top line never changes
//! with expansion, so toggling detail never shifts the layout.

mod output;

use output::render_output;
use serde_json::Value;

use super::ipython_details::{
    format_duration, is_agent_message_receipt, parse_sent_agent_message, read_background_shell,
    BackgroundShell, BashCommands, IpythonDetails, IpythonError,
};
use super::layout::images;
use super::{highlight, ToolCallCard};
use crate::chat::Detail;
use crate::code_preview::{
    parse_ipython_bash_cell, preview_bash_command, preview_ipython_code, python_statement_lines,
    CodePreviewLanguage,
};
use crate::custom_message::AgentMessageDirection;
use crate::element::{self, Element, Fit, Inline, Status, Tick};
use crate::error_summary::{normalize_error_details, summarize_error_details};
use crate::theme::{Theme, ThemeColor};
use crate::width::str_width;
use crate::Line;

/// The output continuation indent (TS `OUTPUT_INDENT`).
const OUTPUT_INDENT: &str = "   ";

/// The cell status (TS `statusKind`).
fn cell_status(card: &ToolCallCard, details: &IpythonDetails) -> Status {
    let result = card.result.as_ref();
    let is_error = result.is_some_and(|r| r.is_error);
    if !card.result_partial {
        if let Some(background) =
            result.and_then(|r| read_background_shell(cell_code(card), &r.details))
        {
            return match background.exit_code {
                Some(0) => Status::Done,
                Some(_) => Status::Error,
                None => Status::Running,
            };
        }
    }
    let status = details.status.as_deref();
    if is_error || status == Some("error") {
        return Status::Error;
    }
    if status == Some("aborted") {
        return Status::Aborted;
    }
    let has_result = result.is_some_and(|r| {
        details.error.is_some() || !details.sent_agent_messages.is_empty() || !r.content.is_empty()
    });
    if !card.result_partial && (status.is_some() || card.started || has_result) {
        return Status::Done;
    }
    if card.result_partial || card.started {
        Status::Running
    } else {
        Status::Queued
    }
}

fn cell_code(card: &ToolCallCard) -> &str {
    card.args
        .get("code")
        .and_then(Value::as_str)
        .unwrap_or_default()
}

/// Render the ipython cell card: the fixed summary line, then the expanded
/// code and output rows when conversation detail is `all`.
#[must_use]
pub fn render(
    card: &ToolCallCard,
    frame: usize,
    detail: Detail,
    theme: &Theme,
    width: usize,
    show_images: bool,
) -> Vec<Line> {
    let code = cell_code(card).trim_end();
    let details = card.result.as_ref().map_or_else(
        || IpythonDetails::parse(&Value::Null),
        |result| IpythonDetails::parse(&result.details),
    );
    let background = card
        .result
        .as_ref()
        .and_then(|result| read_background_shell(code, &result.details));

    // The top line is identical collapsed or expanded, so detail toggles
    // never shift the layout or indentation.
    let mut rows = vec![collapsed_line(card, &details, background.as_ref(), code)];
    // TS renders the sent-message receipt rows below the code (and below
    // the diff rows, which this card does not render) even when the cell
    // is collapsed; the body opens up only when expanded.
    if detail.tool_output_expanded() {
        let has_code = render_code(&mut rows, code, theme);
        render_sent_agent_messages(&mut rows, &details, true, theme, width);
        render_output(card, &details, &mut rows, has_code, show_images);
        // Image blocks render below the card when shown (TS the
        // `N images rendered below` note refers to these rows, which
        // `tool-execution.ts` adds for every tool shell).
        rows.extend(images(card.result.as_ref(), show_images, theme));
    } else {
        render_sent_agent_messages(&mut rows, &details, false, theme, width);
    }
    element::render(&Element::Column(rows), theme, width, Tick(frame))
}

/// The fixed marker + summary line (TS `collapsedLine`).
fn collapsed_line(
    card: &ToolCallCard,
    details: &IpythonDetails,
    background: Option<&BackgroundShell>,
    code: &str,
) -> Element {
    let dominant = dominant_bash(details, code);
    let preview = preview_ipython_code(code);
    let is_bash_cell = parse_ipython_bash_cell(code).is_some();
    let language_label = if dominant.is_some() {
        "bash".to_string()
    } else {
        match (is_bash_cell, &preview.language) {
            (true, CodePreviewLanguage::Python) => "bash - python".to_string(),
            (true | false, CodePreviewLanguage::Bash) => "bash".to_string(),
            (false, CodePreviewLanguage::Python) => "python".to_string(),
        }
    };

    let mut parts: Vec<Inline> = vec![
        Inline::Status {
            status: cell_status(card, details),
        },
        Inline::plain(" "),
        Inline::role(language_label, ThemeColor::Muted),
    ];
    let mut part = |text: String, role: ThemeColor| {
        parts.push(Inline::role(crate::glyphs::SEP, ThemeColor::Dim));
        parts.push(Inline::role(text, role));
    };
    if let Some(bash) = dominant {
        let preview = preview_bash_command(&bash.first);
        if !preview.text.is_empty() {
            part(preview.text, ThemeColor::Dim);
        }
        if bash.count > 1 {
            part(format!("+{} more", bash.count - 1), ThemeColor::Dim);
        }
    } else if !preview.text.is_empty() {
        part(preview.text, ThemeColor::Dim);
    } else if !card.started {
        part("waiting for code".to_string(), ThemeColor::Dim);
    }
    if let Some(counts) = line_counts(card, details, code) {
        part(counts, ThemeColor::Dim);
    }
    if let Some(duration) = details.duration_ms {
        let label = if background.is_some() {
            format!("cell {}", format_duration(duration))
        } else {
            format_duration(duration)
        };
        part(label, ThemeColor::Dim);
    }
    if !card.result_partial {
        let error_name = details
            .error
            .as_ref()
            .map(|e| e.ename.clone())
            .or_else(|| details.error_ename.clone());
        if let Some(ename) = error_name {
            part(ename, ThemeColor::Error);
        }
    }
    if let Some(exit_code) = background.and_then(|shell| shell.exit_code) {
        if exit_code != 0 {
            part(format!("exit {exit_code}"), ThemeColor::Error);
        }
    }
    Element::Inset {
        left: 1,
        child: Box::new(Element::text(Fit::Keep, parts)),
    }
}

/// A cell renders as bash when its executed `bash()` lines are at least
/// `1/BASH_DOMINANCE_DIVISOR` of the cell's non-blank lines. 2 means the bash
/// lines are at least as many as the remaining Python lines (B >= P - B):
/// literal commands also appear in the cell source, so P - B estimates
/// the non-bash Python.
const BASH_DOMINANCE_DIVISOR: usize = 2;

fn input_line_count(code: &str) -> usize {
    let body = parse_ipython_bash_cell(code).map_or_else(|| code.to_string(), |cell| cell.body);
    body.lines().filter(|line| !line.trim().is_empty()).count()
}

fn dominant_bash<'a>(details: &'a IpythonDetails, code: &str) -> Option<&'a BashCommands> {
    details
        .bash_commands
        .as_ref()
        .filter(|bash| bash.lines * BASH_DOMINANCE_DIVISOR >= input_line_count(code))
}

/// `^in vout lines` (TS `lineCounts`): non-empty input
/// lines, output lines of the result text.
fn line_counts(card: &ToolCallCard, details: &IpythonDetails, code: &str) -> Option<String> {
    let input = input_line_count(code);

    let blocks_text = text_from_blocks(card);
    let output_text =
        if is_agent_message_receipt(Some(blocks_text.as_str()), &details.sent_agent_messages) {
            String::new()
        } else {
            blocks_text
        };
    let output = if output_text.trim().is_empty() {
        0
    } else {
        output_text.trim().lines().count()
    };

    let mut segments: Vec<String> = Vec::new();
    if input > 0 {
        segments.push(format!("{} {input}", crate::glyphs::UP));
    }
    if output > 0 {
        segments.push(format!("{} {output}", crate::glyphs::DOWN));
    }
    if segments.is_empty() {
        None
    } else {
        Some(format!("{} lines", segments.join(" ")))
    }
}

/// The text of the result's text blocks (TS `textFromBlocks`).
fn text_from_blocks(card: &ToolCallCard) -> String {
    card.result
        .as_ref()
        .map(|result| {
            result
                .content
                .iter()
                .filter(|block| block.get("type").and_then(Value::as_str) == Some("text"))
                .map(|block| {
                    block
                        .get("text")
                        .and_then(Value::as_str)
                        .unwrap_or_default()
                })
                .collect::<Vec<_>>()
                .join("\n")
        })
        .unwrap_or_default()
}

/// `True` when the line is a magic `!command` line (TS `MAGIC_LINE_PATTERN`).
fn is_magic_line(statement: &str) -> bool {
    statement.trim_start().starts_with('!')
}

/// The expanded source rows (TS `renderCode`): the first line guttered
/// `BRANCH`, continuation lines indented; bash cells and magic
/// lines render in bashMode, python lines syntax highlighted.
fn render_code(rows: &mut Vec<Element>, code: &str, theme: &Theme) -> bool {
    let branch = || vec![Inline::role(crate::glyphs::BRANCH, ThemeColor::Dim)];
    if code.is_empty() {
        rows.push(wrapped(
            branch(),
            vec![Inline::role("waiting for code", ThemeColor::Muted)],
        ));
        return false;
    }
    let is_bash_cell = parse_ipython_bash_cell(code).is_some();
    let mut highlighted = if is_bash_cell {
        Vec::new()
    } else {
        highlight::highlight_python(code, &highlight::SyntaxPalette::from_theme(theme))
    }
    .into_iter();
    let statements = python_statement_lines(code);
    for (index, raw_line) in code.split('\n').enumerate() {
        let gutter = if index == 0 {
            branch()
        } else {
            vec![Inline::plain(OUTPUT_INDENT)]
        };
        let highlighted_line = highlighted.next();
        let statement = statements.get(index).map_or("", String::as_str);
        let magic = is_magic_line(statement) || parse_ipython_bash_cell(statement).is_some();
        let body: Vec<Inline> = if is_bash_cell || magic {
            vec![Inline::role(raw_line, ThemeColor::BashMode)]
        } else {
            highlighted_line.map_or_else(
                || vec![Inline::role(raw_line, ThemeColor::MdCodeBlock)],
                |line| line.into_iter().map(Inline::from).collect(),
            )
        };
        let body = if body.is_empty() {
            vec![Inline::plain(" ")]
        } else {
            body
        };
        rows.push(wrapped(gutter, body));
    }
    true
}

/// TS `renderSentAgentMessages`: one summary row per sent receipt below
/// the code (blank-separated when expanded), the `BRANCH`-guttered body only
/// in the expanded view. The summary carries no body preview (the TS
/// sent rows are the receipt summary alone).
fn render_sent_agent_messages(
    rows: &mut Vec<Element>,
    details: &IpythonDetails,
    expanded: bool,
    theme: &Theme,
    width: usize,
) {
    for sent in &details.sent_agent_messages {
        let Some(sent) = parse_sent_agent_message(sent) else {
            continue;
        };
        if expanded {
            rows.push(Element::blank());
        }
        let direction = if sent.delivered {
            AgentMessageDirection::Sent
        } else {
            AgentMessageDirection::Queued
        };
        // TS: truncateToWidth(summary, max(1, width - 1), "...") then the
        // one-space `addPlain` margin.
        let summary = crate::custom_message::render::agent_message_summary_line(
            direction,
            &sent.counterpart,
            theme,
        );
        rows.push(Element::Inset {
            left: 1,
            child: Box::new(Element::text(
                Fit::Ellipsis,
                summary.into_iter().map(Inline::from).collect(),
            )),
        });
        if expanded {
            rows.extend(
                crate::custom_message::render::agent_message_body(&sent.message, theme, width)
                    .into_iter()
                    .map(Element::line),
            );
        }
    }
}

/// One indented card row (TS `addWrapped`): the first wrapped row carries
/// `gutter`, continuation rows the matching indent, all after a one-space
/// margin; each row is cut at the width so a narrow pane cannot overflow.
fn wrapped(gutter: Vec<Inline>, body: Vec<Inline>) -> Element {
    Element::Inset {
        left: 1,
        child: Box::new(Element::Row { gutter, body }),
    }
}

#[cfg(test)]
mod tests;
