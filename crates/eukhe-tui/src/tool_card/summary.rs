//! The one-row summary every native tool card leads with, in the shape the
//! kernel-run rows already use: `ok bash - <argument summary> - <result
//! summary> - <duration>` (`x` and the error on failure, the working icon
//! while running). The row is the whole card at the default detail level;
//! the expanded level hangs the full arguments and output below it.

use serde_json::Value;

use super::ipython_details::format_duration;
use super::ToolCallCard;
use crate::element::{Element, Fit, Inline, Status};
use crate::theme::ThemeColor;
use crate::width::{str_width, truncate_to_width};

/// The row's left margin (`Element::Inset`), the same as the kernel rows.
const MARGIN: usize = 1;

/// The least width the argument summary keeps when a long error summary
/// competes for the row.
const MIN_ARGUMENT_WIDTH: usize = 12;

/// The continuation indent of the expanded rows below the summary.
pub(super) const BODY_INDENT: &str = "   ";

/// One summary row: the parts after the status mark and the tool name,
/// `SEP`-joined. The argument summary shrinks first when the row is wider
/// than the pane; the error summary shrinks next; the rest is fixed.
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
        // The status mark is one or two cells (`ok`, `x`, the icon) plus
        // the space before the name.
        let mark_width = match status {
            Status::Done => 2,
            Status::Queued | Status::Running | Status::Error | Status::Aborted => 1,
        };
        let fixed: usize = mark_width
            + 1
            + str_width(name)
            + tail
                .iter()
                .map(|(text, _)| str_width(sep) + str_width(text))
                .sum::<usize>();
        let sep_width = str_width(sep);
        let budget = width.saturating_sub(MARGIN + fixed);
        let error_width = error.as_ref().map_or(0, |text| sep_width + str_width(text));
        // The argument keeps at least `MIN_ARGUMENT_WIDTH` cells against a
        // long error; the error takes what the argument leaves.
        let argument_budget = if argument.is_empty() {
            0
        } else {
            let room = budget
                .saturating_sub(error_width)
                .max(MIN_ARGUMENT_WIDTH + sep_width)
                .min(budget);
            (sep_width + str_width(&argument)).min(room)
        };
        let error_budget = budget.saturating_sub(argument_budget);

        let mut parts: Vec<Inline> = vec![
            Inline::Status { status },
            Inline::plain(" "),
            Inline::role(name, ThemeColor::Muted),
        ];
        let mut part = |text: String, role: ThemeColor| {
            parts.push(Inline::role(sep, ThemeColor::Dim));
            parts.push(Inline::role(text, role));
        };
        if argument_budget > sep_width {
            part(
                truncate_to_width(
                    &argument,
                    argument_budget - sep_width,
                    crate::glyphs::ELLIPSIS,
                ),
                ThemeColor::Dim,
            );
        }
        for (text, role) in tail {
            part(text, role);
        }
        // A row too narrow to show more than the ellipsis drops the error
        // text; the `x` mark still says the call failed.
        let error_room = error_budget.saturating_sub(sep_width);
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

/// The expanded body row: the first row hangs off the `BRANCH` gutter,
/// the rest indent to match (the kernel cards' `addWrapped`).
pub(super) fn body_row(first: bool, body: Vec<Inline>) -> Element {
    let gutter = if first {
        vec![Inline::role(crate::glyphs::BRANCH, ThemeColor::Dim)]
    } else {
        vec![Inline::plain(BODY_INDENT)]
    };
    Element::Inset {
        left: MARGIN,
        child: Box::new(Element::Row { gutter, body }),
    }
}

/// The expanded output rows: the first marked `>`, the rest indented;
/// blank lines keep one styled space so the row exists.
pub(super) fn output_rows(rows: &mut Vec<Element>, text: &str, role: ThemeColor) {
    let mut first = true;
    for line in text.split('\n') {
        let gutter = if first {
            vec![Inline::role(
                format!(" {} ", crate::glyphs::POINTER),
                ThemeColor::Dim,
            )]
        } else {
            vec![Inline::plain(BODY_INDENT)]
        };
        first = false;
        rows.push(Element::Inset {
            left: MARGIN,
            child: Box::new(Element::Row {
                gutter,
                body: vec![Inline::role(if line.is_empty() { " " } else { line }, role)],
            }),
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::element::{self, Tick};
    use crate::theme::{ColorMode, Theme};

    fn text(element: &Element, width: usize) -> Vec<String> {
        let theme = Theme::builtin("eukhe", ColorMode::TrueColor);
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
            rendered.starts_with(" x bash - ls -la /t..."),
            "{rendered:?}"
        );
        assert!(
            rendered.contains(" - 82 lines - 0.1s - the user"),
            "{rendered:?}"
        );
        assert!(str_width(rendered) <= 60, "{rendered:?}");
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
}
