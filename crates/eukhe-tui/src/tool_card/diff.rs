//! The `edit` card's diff: the numbered diff an edit result carries per
//! file (`details.files[].diff`, rows `-N|old`, `+N|new` and ` N|context`,
//! `-` and context rows numbered in the old text, `+` rows in the new),
//! drawn below the summary row as `  12 - old` / `  12 + new` rows banded
//! in the diff backgrounds, unchanged rows plain, and a
//! `... N unchanged lines` row where the line numbers jump.

use serde_json::Value;

use crate::chat::pad_to;
use crate::element::Element;
use crate::rows::Gutter;
use crate::style::Style;
use crate::theme::{Theme, ThemeBg, ThemeColor};
use crate::width::{str_width, wrap_text};
use crate::{Line, Span};

/// The column the diff rows start at: the tool quote column.
const COLUMN: usize = Gutter::ToolQuote.mark_col();

/// The fewest cells a line number takes.
const MIN_NUMBER_WIDTH: usize = 2;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Context,
    Removed,
    Added,
}

struct Row<'a> {
    kind: Kind,
    old_no: Option<u64>,
    new_no: Option<u64>,
    text: &'a str,
}

struct File<'a> {
    path: &'a str,
    rows: Vec<Row<'a>>,
}

/// One edit result's diff, borrowed from its details.
pub(super) struct EditDiff<'a> {
    files: Vec<File<'a>>,
}

impl<'a> EditDiff<'a> {
    /// The diff of an edit result's details; `None` when no file carries
    /// diff rows (a no-op, a result without files).
    pub(super) fn from_details(details: &'a Value) -> Option<Self> {
        let files: Vec<File<'a>> = details
            .get("files")?
            .as_array()?
            .iter()
            .filter_map(|file| {
                let rows = parse(file.get("diff")?.as_str()?);
                (!rows.is_empty()).then(|| File {
                    path: file.get("path").and_then(Value::as_str).unwrap_or_default(),
                    rows,
                })
            })
            .collect();
        (!files.is_empty()).then_some(EditDiff { files })
    }

    /// The added and the removed row counts.
    pub(super) fn counts(&self) -> (usize, usize) {
        let rows = self.files.iter().flat_map(|file| &file.rows);
        rows.fold((0, 0), |(added, removed), row| match row.kind {
            Kind::Added => (added + 1, removed),
            Kind::Removed => (added, removed + 1),
            Kind::Context => (added, removed),
        })
    }

    /// The diff rows at `width`; with `limit`, the first `limit` diff
    /// rows and a `... +N lines (Ctrl+O)` row for the rest.
    pub(super) fn elements(
        &self,
        limit: Option<usize>,
        theme: &Theme,
        width: usize,
    ) -> Vec<Element> {
        let number_width = self
            .files
            .iter()
            .flat_map(|file| &file.rows)
            .filter_map(|row| row.new_no.or(row.old_no))
            .max()
            .map_or(MIN_NUMBER_WIDTH, |max| {
                max.to_string().len().max(MIN_NUMBER_WIDTH)
            });
        let total: usize = self.files.iter().map(|file| file.rows.len()).sum();
        let mut budget = limit.unwrap_or(usize::MAX);
        let mut out = Vec::new();
        for file in &self.files {
            if budget == 0 {
                break;
            }
            if self.files.len() > 1 {
                out.push(note(file.path, ThemeColor::Muted, theme));
            }
            let (mut last_old, mut last_new) = (None, None);
            for row in file.rows.iter().take(budget) {
                let skipped = match (row.old_no, last_old, row.new_no, last_new) {
                    (Some(at), Some(last), _, _) | (None, _, Some(at), Some(last)) => {
                        at.saturating_sub(last + 1)
                    }
                    _ => 0,
                };
                if skipped > 0 {
                    let text = format!("{} {skipped} unchanged lines", crate::glyphs::ELLIPSIS);
                    out.push(note(&text, ThemeColor::Dim, theme));
                }
                last_old = row.old_no.or(last_old);
                last_new = row.new_no.or(last_new);
                draw(row, number_width, theme, width, &mut out);
                budget -= 1;
            }
        }
        let shown = limit.map_or(total, |limit| limit.min(total));
        if shown < total {
            let text = format!(
                "{} +{} lines (Ctrl+O)",
                crate::glyphs::ELLIPSIS,
                total - shown
            );
            out.push(note(&text, ThemeColor::Dim, theme));
        }
        out
    }
}

/// The rows of a numbered diff, each with both line numbers where it has
/// them: a context row's new number is its old one shifted by the rows
/// added and removed above it.
fn parse(diff: &str) -> Vec<Row<'_>> {
    let mut shift = 0_i64;
    diff.split('\n')
        .filter_map(|line| {
            let (head, text) = line.split_once('|')?;
            let kind = match head.as_bytes().first()? {
                b'-' => Kind::Removed,
                b'+' => Kind::Added,
                b' ' => Kind::Context,
                _ => return None,
            };
            let number: u64 = head[1..].parse().ok()?;
            let (old_no, new_no) = match kind {
                Kind::Removed => {
                    shift -= 1;
                    (Some(number), None)
                }
                Kind::Added => {
                    shift += 1;
                    (None, Some(number))
                }
                Kind::Context => (Some(number), number.checked_add_signed(shift)),
            };
            Some(Row {
                kind,
                old_no,
                new_no,
                text,
            })
        })
        .collect()
}

/// A plain row at the diff column.
fn note(text: &str, role: ThemeColor, theme: &Theme) -> Element {
    Element::line(vec![
        Span::raw(" ".repeat(COLUMN)),
        Span::styled(text, theme.fg_style(role)),
    ])
}

/// One diff row: its number and mark, then its text wrapped under itself;
/// a changed row's band runs to the width.
fn draw(row: &Row<'_>, number_width: usize, theme: &Theme, width: usize, out: &mut Vec<Element>) {
    let (mark, number, band, number_role, text_role) = match row.kind {
        Kind::Removed => (
            '-',
            row.old_no,
            theme.bg_style(ThemeBg::ToolDiffRemovedBg),
            ThemeColor::Error,
            ThemeColor::ToolDiffRemoved,
        ),
        Kind::Added => (
            '+',
            row.new_no,
            theme.bg_style(ThemeBg::ToolDiffAddedBg),
            ThemeColor::Success,
            ThemeColor::ToolDiffAdded,
        ),
        Kind::Context => (
            ' ',
            row.new_no,
            Style::default(),
            ThemeColor::Dim,
            ThemeColor::ToolDiffContext,
        ),
    };
    let number = number.map(|number| number.to_string()).unwrap_or_default();
    let gutter = format!("{number:>number_width$} {mark} ");
    let gutter_width = str_width(&gutter);
    let text_width = width.saturating_sub(COLUMN + gutter_width + 1).max(1);
    let text = if row.text.contains('\t') {
        std::borrow::Cow::Owned(row.text.replace('\t', "    "))
    } else {
        std::borrow::Cow::Borrowed(row.text)
    };
    let mut wrapped = wrap_text(&text, text_width);
    if wrapped.is_empty() {
        wrapped.push(Line::new());
    }
    let text_style = theme.fg_style(text_role).patch(band);
    for (index, line) in wrapped.into_iter().enumerate() {
        let mut cells: Line = vec![Span::raw(" ".repeat(COLUMN))];
        cells.push(if index == 0 {
            Span::styled(gutter.as_str(), theme.fg_style(number_role).patch(band))
        } else {
            Span::styled(" ".repeat(gutter_width), band)
        });
        cells.extend(
            line.into_iter()
                .map(|span| Span::styled(span.content, text_style)),
        );
        out.push(Element::line(if row.kind == Kind::Context {
            cells
        } else {
            pad_to(cells, width, band)
        }));
    }
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;
    use crate::element::{render, Tick};
    use crate::theme::ColorMode;

    fn theme() -> Theme {
        Theme::builtin("forge", ColorMode::TrueColor)
    }

    fn text(elements: &[Element], width: usize) -> Vec<String> {
        render(
            &Element::Column(elements.to_vec()),
            &theme(),
            width,
            Tick(0),
        )
        .iter()
        .map(|row| {
            row.iter()
                .map(|span| span.content.as_str())
                .collect::<String>()
                .trim_end()
                .to_string()
        })
        .collect()
    }

    fn details() -> Value {
        json!({ "files": [{ "path": "src/hello.rs", "diff": ([
            " 1|fn greet() {",
            "-2|    println!(\"Helo world\");",
            "+2|    println!(\"Hello, world!\");",
            " 3|}",
            "",
            " 40|fn main() {}",
            "+41|\tfn tail() {}",
        ].join("\n")) }]})
    }

    #[test]
    fn rows_carry_numbers_marks_and_gaps() {
        let details = details();
        let diff = EditDiff::from_details(&details).expect("rows");
        assert_eq!(diff.counts(), (2, 1));
        assert_eq!(
            text(&diff.elements(None, &theme(), 80), 80),
            [
                "       1   fn greet() {",
                "       2 -     println!(\"Helo world\");",
                "       2 +     println!(\"Hello, world!\");",
                "       3   }",
                "      ... 36 unchanged lines",
                "      40   fn main() {}",
                "      41 +     fn tail() {}",
            ]
        );
        assert_eq!(
            text(&diff.elements(Some(3), &theme(), 80), 80),
            [
                "       1   fn greet() {",
                "       2 -     println!(\"Helo world\");",
                "       2 +     println!(\"Hello, world!\");",
                "      ... +3 lines (Ctrl+O)",
            ]
        );
    }

    #[test]
    fn changed_rows_are_banded_and_numbered_in_the_status_colors() {
        let details = details();
        let diff = EditDiff::from_details(&details).expect("rows");
        let rows = render(
            &Element::Column(diff.elements(None, &theme(), 60)),
            &theme(),
            60,
            Tick(0),
        );
        let removed_bg = theme().bg_style(ThemeBg::ToolDiffRemovedBg);
        assert_eq!(
            rows[1][1].style,
            theme().fg_style(ThemeColor::Error).patch(removed_bg)
        );
        let added_bg = theme().bg_style(ThemeBg::ToolDiffAddedBg);
        assert_eq!(
            rows[2][1].style,
            theme().fg_style(ThemeColor::Success).patch(added_bg)
        );
        assert!(rows.iter().all(|row| crate::width::line_width(row) <= 60));
    }

    #[test]
    fn context_rows_take_their_new_number_from_the_rows_above() {
        let details =
            json!({ "files": [{ "path": "a.rs", "diff": "-4|a\n-5|b\n+4|c\n 6|d\n 9|e" }] });
        let diff = EditDiff::from_details(&details).expect("rows");
        assert_eq!(
            text(&diff.elements(None, &theme(), 40), 40),
            [
                "       4 - a",
                "       5 - b",
                "       4 + c",
                "       5   d",
                "      ... 2 unchanged lines",
                "       8   e",
            ]
        );
    }

    #[test]
    fn results_without_diff_rows_have_no_diff() {
        for details in [
            json!({}),
            json!({ "diff": "-1|old\n+1|new" }),
            json!({ "files": [{ "path": "a.rs" }] }),
            json!({ "files": [{ "path": "a.rs", "diff": "" }] }),
        ] {
            assert!(EditDiff::from_details(&details).is_none(), "{details}");
        }
    }
}
