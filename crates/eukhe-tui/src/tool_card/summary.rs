//! The one-row summary every native tool card leads with, on the step
//! gutter: `ok bash  <argument summary> - <result summary> - <duration>`
//! (`x` on failure, the working icon while running), and the rows that hang
//! below it at the tool quote column: a failed call's output, the expanded
//! arguments as `key: value` rows, and the expanded output behind a dim
//! `| ` bar.

use serde_json::Value;

use super::ipython_details::format_duration;
use super::ToolCallCard;
use crate::element::{Element, Fit, Inline, Status};
use crate::rows::Gutter;
use crate::theme::{Theme, ThemeColor};
use crate::width::{str_width, truncate_to_width, wrap_line};
use crate::{Line, Span};

/// The row's left margin: the status mark sits on the step gutter.
pub(super) const MARGIN: usize = Gutter::Step.mark_col();

/// The column the rows below the summary start at.
const BODY_COLUMN: usize = Gutter::ToolQuote.mark_col();

/// The least width the argument summary keeps when a long error summary
/// competes for the row.
const MIN_ARGUMENT_WIDTH: usize = 12;

/// The gap between the tool name and its argument.
const NAME_GAP: &str = "  ";

/// The lines a failed call shows of its output before the cut, and after.
const FAILED_HEAD_LINES: usize = 2;
const FAILED_TAIL_LINES: usize = 3;

/// One summary row: the tool name, its argument after a two-space gap,
/// then the result parts `SEP`-joined. The argument summary shrinks first
/// when the row is wider than the pane; the error summary shrinks next;
/// the rest is fixed.
pub(super) struct SummaryRow<'a> {
    pub(super) status: Status,
    pub(super) name: &'a str,
    /// The one-line argument summary (the command, the path, the pattern).
    pub(super) argument: String,
    /// The result summary (`12 lines`, `+6 -2`, `exit 1`), in `role`.
    pub(super) results: Vec<(String, ThemeColor)>,
    pub(super) duration: Option<String>,
    /// The error summary (the error type or its first line).
    pub(super) error: Option<String>,
}

impl SummaryRow<'_> {
    /// The row as one element, fitted to `width`.
    pub(super) fn element(self, width: usize) -> Element {
        let SummaryRow {
            status,
            name,
            argument,
            results,
            duration,
            error,
        } = self;
        let sep = crate::glyphs::SEP;
        let mut tail: Vec<(String, ThemeColor)> = results;
        if let Some(duration) = duration {
            tail.push((duration, ThemeColor::Dim));
        }
        let sep_width = str_width(sep);
        let gap_width = str_width(NAME_GAP);
        // The first part after the name follows the two-space gap, every
        // later one a separator.
        let lead_width = |index: usize| if index == 0 { gap_width } else { sep_width };
        let has_argument = !argument.is_empty();
        let first_tail = usize::from(has_argument);
        // The status mark's two cells plus the space before the name.
        let fixed: usize = crate::element::STATUS_MARK_WIDTH
            + 1
            + str_width(name)
            + tail
                .iter()
                .enumerate()
                .map(|(index, (text, _))| lead_width(index + first_tail) + str_width(text))
                .sum::<usize>();
        let budget = width.saturating_sub(MARGIN + fixed);
        let error_lead = lead_width(first_tail + tail.len());
        let error_width = error
            .as_ref()
            .map_or(0, |text| error_lead + str_width(text));
        // The argument keeps at least `MIN_ARGUMENT_WIDTH` cells against a
        // long error; the error takes what the argument leaves.
        let argument_budget = if has_argument {
            let room = budget
                .saturating_sub(error_width)
                .max(MIN_ARGUMENT_WIDTH + gap_width)
                .min(budget);
            (gap_width + str_width(&argument)).min(room)
        } else {
            0
        };
        let error_budget = budget.saturating_sub(argument_budget);

        let mut parts: Vec<Inline> = vec![
            Inline::Status { status },
            Inline::plain(" "),
            Inline::role(name, ThemeColor::Muted),
        ];
        let mut part = |text: String, role: ThemeColor| {
            if parts.len() == 3 {
                parts.push(Inline::plain(NAME_GAP));
            } else {
                parts.push(Inline::role(sep, ThemeColor::Dim));
            }
            parts.push(Inline::role(text, role));
        };
        if argument_budget > gap_width {
            part(
                truncate_to_width(
                    &argument,
                    argument_budget - gap_width,
                    crate::glyphs::ELLIPSIS,
                ),
                ThemeColor::Muted,
            );
        }
        for (text, role) in tail {
            part(text, role);
        }
        // A row too narrow to show more than the ellipsis drops the error
        // text; the `x` mark still says the call failed.
        let error_room = error_budget.saturating_sub(error_lead);
        if let Some(error) = error.filter(|_| error_room > str_width(crate::glyphs::ELLIPSIS)) {
            part(
                truncate_to_width(&error, error_room, crate::glyphs::ELLIPSIS),
                ThemeColor::Error,
            );
        }
        Element::Inset {
            left: MARGIN,
            child: Box::new(Element::text(Fit::Keep, parts)),
        }
    }
}

/// The card's run time, from the live execution clock: `12ms`, `3.2s`.
/// `None` until the card started or while it still runs.
pub(super) fn duration(card: &ToolCallCard) -> Option<String> {
    if card.result_partial || card.result.is_none() {
        return None;
    }
    let started = card.started_at?;
    let ended = card.ended_at?;
    let elapsed = ended.saturating_duration_since(started);
    Some(format_duration(elapsed.as_secs_f64() * 1000.0))
}

/// The output's non-blank line count as a result summary: `12 lines`
/// (`1 line`); `None` for an empty output.
pub(super) fn line_count(text: &str) -> Option<String> {
    let count = text.lines().filter(|line| !line.trim().is_empty()).count();
    match count {
        0 => None,
        1 => Some("1 line".to_string()),
        count => Some(format!("{count} lines")),
    }
}

/// The first non-blank line of a multi-line argument (the command, the
/// patch), whitespace-trimmed.
pub(super) fn first_line(text: &str) -> &str {
    text.lines()
        .map(str::trim)
        .find(|line| !line.is_empty())
        .unwrap_or_default()
}

/// A string argument of the call, `None` when absent or not a string.
pub(super) fn string_arg<'a>(args: &'a Value, key: &str) -> Option<&'a str> {
    args.get(key).and_then(Value::as_str)
}

/// A row below the summary, at the tool quote column; wrapped rows keep
/// the column.
pub(super) fn body_row(body: Vec<Inline>) -> Element {
    Element::Inset {
        left: BODY_COLUMN,
        child: Box::new(Element::Row {
            gutter: Vec::new(),
            body,
        }),
    }
}

/// The call's arguments as `key: value` rows below the summary, the keys
/// in `skip` left out: a string value as it is (its later lines under its
/// first), any other value as compact JSON.
pub(super) fn argument_rows(rows: &mut Vec<Element>, args: &Value, skip: &[&str]) {
    let Value::Object(args) = args else {
        if !args.is_null() {
            rows.push(body_row(vec![Inline::role(
                args.to_string(),
                ThemeColor::Muted,
            )]));
        }
        return;
    };
    for (key, value) in args.iter().filter(|(key, _)| !skip.contains(&key.as_str())) {
        let label = format!("{key}: ");
        let indent = " ".repeat(str_width(&label));
        let compact;
        let text = match value {
            Value::String(text) => text.as_str(),
            value => {
                compact = value.to_string();
                compact.as_str()
            }
        };
        for (index, line) in text.split('\n').enumerate() {
            let gutter = if index == 0 {
                Inline::role(label.as_str(), ThemeColor::Dim)
            } else {
                Inline::plain(indent.as_str())
            };
            rows.push(Element::Inset {
                left: BODY_COLUMN,
                child: Box::new(Element::Row {
                    gutter: vec![gutter],
                    body: vec![Inline::role(
                        if line.is_empty() { " " } else { line },
                        ThemeColor::Muted,
                    )],
                }),
            });
        }
    }
}

/// The output behind the tool quote bar, every line; wrapped rows keep
/// the bar.
pub(super) fn output_rows(
    rows: &mut Vec<Element>,
    text: &str,
    role: ThemeColor,
    theme: &Theme,
    width: usize,
) {
    quote(rows, text.split('\n'), role, theme, width);
}

/// A failed call's output behind the tool quote bar: its first
/// [`FAILED_HEAD_LINES`] and last [`FAILED_TAIL_LINES`] lines, with a
/// `... +N lines (Ctrl+O)` row between them for the lines left out.
pub(super) fn failed_output_rows(rows: &mut Vec<Element>, text: &str, theme: &Theme, width: usize) {
    let count = text.split('\n').count();
    let shown = FAILED_HEAD_LINES + FAILED_TAIL_LINES;
    if count <= shown {
        quote(rows, text.split('\n'), ThemeColor::Muted, theme, width);
        return;
    }
    quote(
        rows,
        text.split('\n').take(FAILED_HEAD_LINES),
        ThemeColor::Muted,
        theme,
        width,
    );
    let hidden = format!(
        "{} +{} lines (Ctrl+O)",
        crate::glyphs::ELLIPSIS,
        count - shown
    );
    quote(
        rows,
        std::iter::once(hidden.as_str()),
        ThemeColor::Dim,
        theme,
        width,
    );
    quote(
        rows,
        text.split('\n').skip(count - FAILED_TAIL_LINES),
        ThemeColor::Muted,
        theme,
        width,
    );
}

fn quote<'a>(
    rows: &mut Vec<Element>,
    lines: impl Iterator<Item = &'a str>,
    role: ThemeColor,
    theme: &Theme,
    width: usize,
) {
    let style = theme.fg_style(role);
    let body_width = Gutter::ToolQuote.body_width(width);
    for line in lines {
        let mut body = wrap_line(&vec![Span::styled(line, style)], body_width);
        if body.is_empty() {
            body.push(Line::new());
        }
        rows.extend(
            Gutter::ToolQuote
                .place(None, body, theme, width)
                .into_iter()
                .map(Element::line),
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::element::{self, Tick};
    use crate::theme::{ColorMode, Theme};

    fn text(element: &Element, width: usize) -> Vec<String> {
        let theme = Theme::builtin("forge", ColorMode::TrueColor);
        element::render(element, &theme, width, Tick(0))
            .iter()
            .map(|row| row.iter().map(|s| s.content.as_str()).collect::<String>())
            .collect()
    }

    fn row(argument: &str, error: Option<&str>) -> SummaryRow<'static> {
        SummaryRow {
            status: if error.is_some() {
                Status::Error
            } else {
                Status::Done
            },
            name: "bash",
            argument: argument.to_string(),
            results: vec![("82 lines".to_string(), ThemeColor::Dim)],
            duration: Some("0.1s".to_string()),
            error: error.map(str::to_string),
        }
    }

    #[test]
    fn the_argument_shrinks_before_the_counts_and_the_duration() {
        let long = "grep -n ".to_string() + &"x".repeat(100) + " src/media.ts";
        let rows = text(&row(&long, None).element(60), 60);
        assert_eq!(rows.len(), 1, "{rows:?}");
        let rendered = rows[0].trim_end();
        assert!(rendered.ends_with(" - 82 lines - 0.1s"), "{rendered:?}");
        assert!(rendered.contains("..."), "{rendered:?}");
        assert!(str_width(rendered) <= 60, "{rendered:?}");
    }

    #[test]
    fn a_long_error_keeps_a_minimum_argument_and_truncates_itself() {
        let error = "the user denied it. ".repeat(6);
        let rows = text(
            &row("ls -la /tmp/ref-super.png", Some(&error)).element(60),
            60,
        );
        assert_eq!(rows.len(), 1, "{rows:?}");
        let rendered = rows[0].trim_end();
        assert!(
            rendered.starts_with("   x  bash  ls -la /t..."),
            "{rendered:?}"
        );
        assert!(
            rendered.contains(" - 82 lines - 0.1s - the user"),
            "{rendered:?}"
        );
        assert!(str_width(rendered) <= 60, "{rendered:?}");
    }

    /// The tool name sits in the same column under every status mark:
    /// the one-cell `x` and the working icon pad to the width of `ok`.
    #[test]
    fn every_status_mark_aligns_the_tool_name() {
        let column = |status: Status, error: Option<&str>| {
            let rows = text(
                &SummaryRow {
                    status,
                    name: "bash",
                    argument: "ls".to_string(),
                    results: Vec::new(),
                    duration: None,
                    error: error.map(str::to_string),
                }
                .element(60),
                60,
            );
            rows[0].find("bash").unwrap_or_else(|| panic!("{rows:?}"))
        };
        assert_eq!(
            [
                column(Status::Done, None),
                column(Status::Error, Some("ENOENT")),
                column(Status::Running, None),
                column(Status::Queued, None),
                column(Status::Aborted, None),
            ],
            [6; 5]
        );
    }

    #[test]
    fn counts_and_first_lines() {
        assert_eq!(line_count(""), None);
        assert_eq!(line_count("\n  \n"), None);
        assert_eq!(line_count("one"), Some("1 line".to_string()));
        assert_eq!(line_count("one\n\ntwo\n"), Some("2 lines".to_string()));
        assert_eq!(first_line("\n  ls -la  \nrm x"), "ls -la");
        assert_eq!(first_line("   "), "");
    }

    fn quoted(text: &str, failed: bool) -> Vec<String> {
        let theme = Theme::builtin("forge", ColorMode::TrueColor);
        let mut rows = Vec::new();
        if failed {
            failed_output_rows(&mut rows, text, &theme, 60);
        } else {
            output_rows(&mut rows, text, ThemeColor::ToolOutput, &theme, 60);
        }
        rows.iter()
            .flat_map(|row| self::text(row, 60))
            .map(|row| row.trim_end().to_string())
            .collect()
    }

    #[test]
    fn a_failed_output_shows_its_head_and_tail_behind_the_bar() {
        let short = "one\n\nthree";
        assert_eq!(
            quoted(short, true),
            ["      | one", "      |", "      | three"]
        );
        let long = (1..=9)
            .map(|n| format!("line {n}"))
            .collect::<Vec<_>>()
            .join("\n");
        assert_eq!(
            quoted(&long, true),
            [
                "      | line 1",
                "      | line 2",
                "      | ... +4 lines (Ctrl+O)",
                "      | line 7",
                "      | line 8",
                "      | line 9",
            ]
        );
        assert_eq!(quoted(&long, false).len(), 9);
    }

    #[test]
    fn wrapped_output_keeps_the_bar() {
        let rows = quoted(&"word ".repeat(20), false);
        assert!(rows.len() > 1, "{rows:?}");
        assert!(
            rows.iter().all(|row| row.starts_with("      | ")),
            "{rows:?}"
        );
    }

    #[test]
    fn arguments_render_as_key_value_rows() {
        let mut rows = Vec::new();
        argument_rows(
            &mut rows,
            &serde_json::json!({ "path": "src/a.rs", "limit": 3, "input": "one\ntwo", "i": "x" }),
            &["i"],
        );
        let rendered: Vec<String> = rows
            .iter()
            .flat_map(|row| text(row, 60))
            .map(|row| row.trim_end().to_string())
            .collect();
        assert_eq!(
            rendered,
            [
                "      path: src/a.rs",
                "      limit: 3",
                "      input: one",
                "             two",
            ]
        );
    }
}
