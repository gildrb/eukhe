//! The generic tool card (`read`, `edit`, `write`, `grep`, `glob`, and any
//! other native tool): one summary row at the default detail, for example
//! `ok read - src/media.ts:44-52 - 12 lines - 3ms` or
//! `ok edit - src/media.ts - +6 -2`, with `x` and the error's first line on
//! failure; at the expanded detail, the call's arguments and its output
//! hang below.

use serde_json::Value;

use super::layout::images;
use super::summary::{
    body_row, duration, first_line, line_count, output_rows, string_arg, SummaryRow,
};
use super::{format_size, panel_status, ToolCallCard};
use crate::chat::Detail;
use crate::element::{self, Element, Inline, Status, Tick};
use crate::error_summary::summarize_error_details;
use crate::theme::{Theme, ThemeColor};
use crate::Line;

#[must_use]
pub fn render(
    card: &ToolCallCard,
    frame: usize,
    detail: Detail,
    theme: &Theme,
    width: usize,
    show_images: bool,
) -> Vec<Line> {
    let output = card
        .result
        .as_ref()
        .map(|result| result.text_output(show_images))
        .unwrap_or_default();
    let output = output.trim();
    let mut rows = vec![summary_row(card, output).element(width)];
    if detail.tool_output_expanded() {
        let args = match &card.args {
            Value::Null => String::new(),
            args => serde_json::to_string_pretty(args).unwrap_or_default(),
        };
        let mut first = true;
        for line in args.split('\n').filter(|line| !line.is_empty()) {
            rows.push(body_row(first, vec![Inline::role(line, ThemeColor::Dim)]));
            first = false;
        }
        if !output.is_empty() {
            output_rows(&mut rows, output, ThemeColor::ToolOutput);
        }
        rows.extend(images(card.result.as_ref(), show_images, theme));
    }
    element::render(&Element::Column(rows), theme, width, Tick(frame))
}

/// The one-row summary (the whole card at the default detail).
fn summary_row<'a>(card: &'a ToolCallCard, output: &str) -> SummaryRow<'a> {
    let (argument, mut results) = call_summary(&card.name, &card.args);
    let mut status = panel_status(card);
    let mut error = None;
    if let Some(result) = &card.result {
        if card.name != "edit" {
            if let Some(count) = line_count(output) {
                results.push((count, ThemeColor::Dim));
            }
        }
        if !card.result_partial && result.is_error {
            status = Status::Error;
            error = Some(summarize_error_details(output));
        }
    }
    SummaryRow {
        status,
        name: &card.name,
        argument,
        results,
        duration: duration(card),
        error,
    }
}

/// The argument summary and the argument-derived result parts of one call:
/// `read` its path (selector included); `edit` the patched path(s) and the
/// `+N -M` row counts; `write` its path and the content's size; `grep` the
/// pattern and the path; `glob` the path; any other tool its first string
/// argument, else its `i` intent.
fn call_summary(name: &str, args: &Value) -> (String, Vec<(String, ThemeColor)>) {
    let path = string_arg(args, "path").unwrap_or_default();
    match name {
        "read" | "glob" => (path.to_string(), Vec::new()),
        "edit" => edit_summary(string_arg(args, "input").unwrap_or_default()),
        "write" => {
            let content = string_arg(args, "content").unwrap_or_default();
            let mut results = Vec::new();
            if let Some(count) = line_count(content) {
                results.push((
                    format!("{count} ({})", format_size(content.len())),
                    ThemeColor::Dim,
                ));
            }
            (path.to_string(), results)
        }
        "grep" => {
            let pattern = string_arg(args, "pattern").unwrap_or_default();
            let argument = if path.is_empty() {
                pattern.to_string()
            } else {
                format!("{pattern} in {path}")
            };
            (argument, Vec::new())
        }
        _ => {
            let first_string = args.as_object().and_then(|object| {
                object
                    .iter()
                    .filter(|(key, _)| key.as_str() != "i")
                    .find_map(|(_, value)| value.as_str())
            });
            let argument = first_string
                .or_else(|| string_arg(args, "i"))
                .map(first_line)
                .unwrap_or_default();
            (argument.to_string(), Vec::new())
        }
    }
}

/// A hashline patch's summary: the distinct `[PATH#TAG]` headers' paths
/// (` ; `-joined), and `+N` added rows (the `+` body lines) with `-M`
/// removed rows (the `CUT N.=M` / `PUT N.=M:` ranges; `-M` only when any).
fn edit_summary(input: &str) -> (String, Vec<(String, ThemeColor)>) {
    let mut paths: Vec<&str> = Vec::new();
    let mut added = 0usize;
    let mut removed = 0usize;
    for line in input.lines() {
        if let Some(path) = patch_header_path(line) {
            if !paths.contains(&path) {
                paths.push(path);
            }
        } else if line.starts_with('+') {
            added += 1;
        } else if let Some(count) = replaced_range_rows(line) {
            removed += count;
        }
    }
    let counts = if removed > 0 {
        format!("+{added} -{removed}")
    } else {
        format!("+{added}")
    };
    (paths.join(" ; "), vec![(counts, ThemeColor::Dim)])
}

/// The path of a `[PATH#TAG]` patch header line.
fn patch_header_path(line: &str) -> Option<&str> {
    let inner = line.strip_prefix('[')?.strip_suffix(']')?;
    let (path, _tag) = inner.rsplit_once('#')?;
    (!path.is_empty()).then_some(path)
}

/// The rows a `CUT N.=M` / `CUT N` / `PUT N.=M:` op removes.
fn replaced_range_rows(line: &str) -> Option<usize> {
    let rest = line
        .strip_prefix("CUT ")
        .or_else(|| line.strip_prefix("PUT "))?;
    let spec = rest.split_whitespace().next()?.trim_end_matches(':');
    let (from, to) = if let Some((from, to)) = spec.split_once(".=") {
        (from.parse::<usize>().ok()?, to.parse::<usize>().ok()?)
    } else {
        if line.starts_with("PUT ") {
            return None;
        }
        let at = spec.parse::<usize>().ok()?;
        (at, at)
    };
    Some(to.checked_sub(from)? + 1)
}

#[cfg(test)]
mod tests {
    use std::time::{Duration, Instant};

    use super::*;
    use crate::theme::{ColorMode, Theme};
    use serde_json::json;

    fn theme() -> Theme {
        Theme::builtin("eukhe", ColorMode::TrueColor)
    }

    fn flat(rows: &[Line]) -> Vec<String> {
        rows.iter()
            .map(|row| {
                row.iter()
                    .map(|s| s.content.as_str())
                    .collect::<String>()
                    .trim_end()
                    .to_string()
            })
            .collect()
    }

    fn done_card(name: &str, args: Value, output: &str) -> ToolCallCard {
        let start = Instant::now();
        ToolCallCard {
            id: "t".into(),
            name: name.into(),
            args,
            started: true,
            started_at: Some(start),
            ended_at: Some(start + Duration::from_millis(3)),
            result: Some(super::super::ToolResultView {
                content: vec![json!({ "type": "text", "text": output })],
                details: json!({}),
                is_error: false,
            }),
            result_partial: false,
            aborted: false,
        }
    }

    fn image_card() -> ToolCallCard {
        let png = tiny_png(64, 32);
        ToolCallCard {
            id: "t".into(),
            name: "custom".into(),
            args: json!({}),
            started: true,
            result: Some(super::super::ToolResultView {
                content: vec![
                    json!({ "type": "text", "text": "done" }),
                    json!({ "type": "image", "data": png, "mimeType": "image/png" }),
                ],
                details: json!({}),
                is_error: false,
            }),
            result_partial: false,
            ..Default::default()
        }
    }

    fn tiny_png(width: u32, height: u32) -> String {
        use base64::Engine;
        let mut bytes = vec![0x89, b'P', b'N', b'G'];
        bytes.extend(vec![0u8; 12]);
        bytes.extend(width.to_be_bytes());
        bytes.extend(height.to_be_bytes());
        base64::engine::general_purpose::STANDARD.encode(bytes)
    }

    #[test]
    fn a_read_renders_one_row_with_its_selector_and_line_count() {
        let output = "[src/media.ts#AA10]\n".to_string()
            + &(43..=54)
                .map(|n| format!("{n}:    height: 1036,"))
                .collect::<Vec<_>>()
                .join("\n");
        let card = done_card(
            "read",
            json!({ "path": "src/media.ts:44-52", "i": "Reading the media table" }),
            &output,
        );
        for detail in [Detail::Overview, Detail::Details] {
            assert_eq!(
                flat(&render(&card, 0, detail, &theme(), 120, true)),
                vec![" ok read - src/media.ts:44-52 - 13 lines - 3ms"]
            );
        }
    }

    #[test]
    fn an_edit_renders_its_path_and_row_counts() {
        let input = "[src/media.ts#AA10]\nPUT >45:\n+  /** wallpaper */\n+  \"heph-forge\": {\n+    width: 2952,\n+  },\nCUT 50.=51\nPUT 60.=60:\n+    alt: \"x\",";
        let card = done_card(
            "edit",
            json!({ "input": input, "i": "Registering the wallpaper" }),
            "[src/media.ts#2F60]\n38:  \"ben-davis-site-tour\": {\n... 11 more lines",
        );
        assert_eq!(
            flat(&render(&card, 0, Detail::Overview, &theme(), 120, true)),
            vec![" ok edit - src/media.ts - +5 -3 - 3ms"]
        );
        let additions_only = done_card(
            "edit",
            json!({ "input": "[a.rs#1111]\nPUT >2:\n+x\n[b.rs#2222]\nPUT <1:\n+y" }),
            "ok",
        );
        assert_eq!(
            flat(&render(
                &additions_only,
                0,
                Detail::Overview,
                &theme(),
                120,
                true
            )),
            vec![" ok edit - a.rs ; b.rs - +2 - 3ms"]
        );
    }

    #[test]
    fn write_grep_glob_and_other_tools_summarize_their_arguments() {
        let write = done_card(
            "write",
            json!({ "path": "notes.txt", "content": "one\ntwo\nthree\n" }),
            "wrote notes.txt",
        );
        assert_eq!(
            flat(&render(&write, 0, Detail::Overview, &theme(), 120, true)),
            vec![" ok write - notes.txt - 3 lines (14B) - 1 line - 3ms"]
        );
        let grep = done_card(
            "grep",
            json!({ "pattern": "fn main", "path": "src", "i": "Finding main" }),
            "[src/main.rs#1234]\n*1:fn main() {}",
        );
        assert_eq!(
            flat(&render(&grep, 0, Detail::Overview, &theme(), 120, true)),
            vec![" ok grep - fn main in src - 2 lines - 3ms"]
        );
        let glob = done_card("glob", json!({ "path": "**/*.rs" }), "a.rs\nb.rs");
        assert_eq!(
            flat(&render(&glob, 0, Detail::Overview, &theme(), 120, true)),
            vec![" ok glob - **/*.rs - 2 lines - 3ms"]
        );
        let other = done_card(
            "web_search",
            json!({ "i": "Searching the docs", "query": "ratatui wrap", "limit": 3 }),
            "result",
        );
        assert_eq!(
            flat(&render(&other, 0, Detail::Overview, &theme(), 120, true)),
            vec![" ok web_search - ratatui wrap - 1 line - 3ms"]
        );
        let intent_only = done_card("memo", json!({ "i": "Noting the plan", "count": 2 }), "");
        assert_eq!(
            flat(&render(
                &intent_only,
                0,
                Detail::Overview,
                &theme(),
                120,
                true
            )),
            vec![" ok memo - Noting the plan - 3ms"]
        );
    }

    #[test]
    fn a_failed_call_is_an_error_row_with_the_first_error_line() {
        let mut card = done_card(
            "read",
            json!({ "path": "src/lib.rs" }),
            "no such file: src/lib.rs\n  at read",
        );
        card.result.as_mut().expect("result").is_error = true;
        assert_eq!(
            flat(&render(&card, 0, Detail::Overview, &theme(), 120, true)),
            vec![" x read - src/lib.rs - 2 lines - 3ms - no such file: src/lib.rs"]
        );
    }

    #[test]
    fn a_running_card_is_one_row_that_settles_in_place() {
        let card = ToolCallCard {
            id: "t".into(),
            name: "read".into(),
            args: json!({ "path": "src/lib.rs" }),
            started: true,
            started_at: Some(Instant::now()),
            ..Default::default()
        };
        assert_eq!(
            flat(&render(&card, 0, Detail::Overview, &theme(), 120, true)),
            vec![" . read - src/lib.rs"]
        );
        let settled = done_card("read", json!({ "path": "src/lib.rs" }), "one\ntwo");
        assert_eq!(
            flat(&render(&settled, 0, Detail::Overview, &theme(), 120, true)),
            vec![" ok read - src/lib.rs - 2 lines - 3ms"]
        );
    }

    #[test]
    fn the_expanded_detail_hangs_the_arguments_and_the_output_below() {
        let card = done_card("read", json!({ "path": "src/lib.rs" }), "one\ntwo");
        assert_eq!(
            flat(&render(&card, 0, Detail::All, &theme(), 120, true)),
            vec![
                " ok read - src/lib.rs - 2 lines - 3ms",
                " `- {",
                "      \"path\": \"src/lib.rs\"",
                "    }",
                "  > one",
                "    two",
            ]
        );
    }

    #[test]
    fn shown_image_blocks_render_their_metadata_row_below_the_output() {
        let card = image_card();
        let rows = flat(&render(&card, 0, Detail::All, &theme(), 120, true));
        assert!(
            rows.iter()
                .any(|r| r.contains("    `- [image/png - 64x32]")),
            "got: {rows:?}"
        );
        assert!(!rows.iter().any(|r| r.contains("[Image:")));
    }

    #[test]
    fn hidden_image_blocks_fall_back_to_placeholder_text() {
        let card = image_card();
        let rows = flat(&render(&card, 0, Detail::All, &theme(), 120, false));
        // TS renders the hidden-image text without dimensions
        // (includeImageDimensions: false in the interactive transcript).
        assert!(
            rows.iter().any(|r| r.contains("[Image: [image/png]]")),
            "got: {rows:?}"
        );
        assert!(!rows.iter().any(|r| r.contains("[image/png -")));
    }

    #[test]
    fn image_blocks_without_payload_data_render_no_rows() {
        let mut card = image_card();
        card.result = Some(super::super::ToolResultView {
            content: vec![json!({ "type": "image", "mimeType": "image/png" })],
            details: json!({}),
            is_error: false,
        });
        let rows = flat(&render(&card, 0, Detail::All, &theme(), 120, true));
        assert!(!rows.iter().any(|r| r.contains("[image/png")));
    }
}
