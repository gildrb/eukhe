//! The `bash` tool-call card: one summary row at the default detail
//! (`ok bash - <script's first line> - <N lines> - <duration>`, `x` with
//! `exit N` or the refusal on failure, the working icon while running);
//! the expanded detail hangs the whole script, its output and the
//! truncation warning below the same row.

use serde_json::Value;

use super::layout::images;
use super::summary::{
    body_row, duration, first_line, line_count, output_rows, string_arg, SummaryRow,
};
use super::{panel_status, ToolCallCard, ToolResultView};
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
    let script = script(card);
    let output = card
        .result
        .as_ref()
        .map(|result| result.text_output(show_images))
        .unwrap_or_default();
    let output = output.trim();
    let mut rows = vec![summary_row(card, script, output).element(width)];
    if detail.tool_output_expanded() {
        let mut first = true;
        for line in script
            .filter(|script| !script.is_empty())
            .into_iter()
            .flat_map(|script| script.split('\n'))
        {
            let text = if first {
                format!("$ {line}")
            } else {
                line.to_string()
            };
            rows.push(body_row(
                first,
                vec![Inline::role(text, ThemeColor::BashMode)],
            ));
            first = false;
        }
        if !output.is_empty() {
            output_rows(&mut rows, output, ThemeColor::ToolOutput);
        }
        if let Some(warning) = card.result.as_ref().and_then(truncation_warning) {
            rows.push(body_row(
                false,
                vec![Inline::role(warning, ThemeColor::Warning)],
            ));
        }
        rows.extend(images(card.result.as_ref(), show_images, theme));
    }
    element::render(&Element::Column(rows), theme, width, Tick(frame))
}

/// The script argument: eukhe's `bash@1` sends `script`; sessions
/// recorded by the pi-era tool carry `command`. `None` when neither is a
/// string (the streamed call has not filled it yet, or the arg is invalid).
fn script(card: &ToolCallCard) -> Option<&str> {
    string_arg(&card.args, "script").or_else(|| string_arg(&card.args, "command"))
}

/// The script's exit status from the result details (`end.status`), the
/// refusal word when a step was refused, and `detached` when the script
/// outlived the blocking budget and went on as a job.
enum Outcome {
    Exited(i64),
    Refused(String),
    Detached,
    Unknown,
}

fn outcome(result: &ToolResultView) -> Outcome {
    if result.details.get("status").and_then(Value::as_str) == Some("detached") {
        return Outcome::Detached;
    }
    let Some(end) = result.details.get("end") else {
        return Outcome::Unknown;
    };
    match end.get("kind").and_then(Value::as_str) {
        Some("refused") => Outcome::Refused(
            end.get("refusal")
                .and_then(Value::as_str)
                .unwrap_or("refused")
                .replace('_', " "),
        ),
        Some("finished" | "exited") => end
            .get("status")
            .and_then(Value::as_i64)
            .map_or(Outcome::Unknown, Outcome::Exited),
        Some(_) | None => Outcome::Unknown,
    }
}

/// The one-row summary (the whole card at the default detail).
fn summary_row<'a>(card: &'a ToolCallCard, script: Option<&str>, output: &str) -> SummaryRow<'a> {
    let argument = match script {
        Some(script) => first_line(script).to_string(),
        None if card.args.get("script").is_some() || card.args.get("command").is_some() => {
            "[invalid arg]".to_string()
        }
        None => String::new(),
    };
    let mut status = panel_status(card);
    let mut results = Vec::new();
    let mut error = None;
    if let Some(result) = &card.result {
        if let Some(count) = line_count(output) {
            results.push((count, ThemeColor::Dim));
        }
        if !card.result_partial {
            match outcome(result) {
                Outcome::Exited(0) | Outcome::Unknown => {}
                Outcome::Exited(code) => {
                    status = Status::Error;
                    results.push((format!("exit {code}"), ThemeColor::Error));
                }
                Outcome::Refused(refusal) => {
                    status = Status::Error;
                    results.push((refusal, ThemeColor::Error));
                }
                Outcome::Detached => results.push(("detached".to_string(), ThemeColor::Dim)),
            }
            if result.is_error && results.iter().all(|(_, role)| *role != ThemeColor::Error) {
                error = Some(summarize_error_details(output));
            }
        }
    }
    SummaryRow {
        status,
        name: "bash",
        argument,
        results,
        duration: duration(card),
        error,
    }
}

/// The truncation notice (`[Full output: ... . Truncated: ...]`, warning
/// color) when the engine cut the output or spilled it to a file.
fn truncation_warning(result: &ToolResultView) -> Option<String> {
    let details = result.details.as_object();
    let truncation = details.and_then(|d| d.get("truncation"));
    let full_output_path = details
        .and_then(|d| d.get("fullOutputPath"))
        .and_then(Value::as_str)
        .filter(|p| !p.is_empty());
    let truncated =
        truncation.is_some_and(|t| t.get("truncated").and_then(Value::as_bool).unwrap_or(false));
    if !truncated && full_output_path.is_none() {
        return None;
    }
    let mut warnings: Vec<String> = Vec::new();
    if let Some(path) = full_output_path {
        warnings.push(format!("Full output: {path}"));
    }
    if truncated {
        let truncation = truncation.expect("checked");
        let output_lines = truncation.get("outputLines").and_then(Value::as_u64);
        let total_lines = truncation.get("totalLines").and_then(Value::as_u64);
        let truncated_by_lines = truncation
            .get("truncatedBy")
            .and_then(Value::as_str)
            .is_some_and(|kind| kind == "lines");
        match (output_lines, total_lines) {
            (Some(output), Some(total)) if truncated_by_lines => {
                warnings.push(format!("Truncated: showing {output} of {total} lines"));
            }
            (Some(output), Some(_)) => {
                let max_bytes = truncation
                    .get("maxBytes")
                    .and_then(Value::as_u64)
                    .unwrap_or(eukhe_types::output::DEFAULT_MAX_BYTES)
                    as usize;
                warnings.push(format!(
                    "Truncated: {output} lines shown ({} limit)",
                    super::format_size(max_bytes)
                ));
            }
            _ => {}
        }
    }
    if warnings.is_empty() {
        return None;
    }
    Some(format!("[{}]", warnings.join(". ")))
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

    fn done_card(script: &str, output: &str, details: Value) -> ToolCallCard {
        let start = Instant::now();
        ToolCallCard {
            id: "toolu_1".into(),
            name: "bash".into(),
            args: json!({ "script": script }),
            started: true,
            started_at: Some(start),
            ended_at: Some(start + Duration::from_millis(120)),
            result: Some(ToolResultView {
                content: vec![json!({ "type": "text", "text": output })],
                details,
                is_error: false,
            }),
            result_partial: false,
            aborted: false,
        }
    }

    fn finished(status: i64) -> Value {
        json!({ "version": "bash@1", "steps": [], "end": { "kind": "finished", "status": status } })
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

    #[test]
    fn the_default_detail_is_one_row_with_the_real_script() {
        // The brief's capture: the pi-era card read `command`, so eukhe's
        // `script` argument rendered as `$ ...` plus a 5-line output tail
        // under a `bash - done` header. The one row names the script.
        let output = "$ grep -n width src/media.ts\n".to_string()
            + &(1..=82)
                .map(|n| format!("{n}-    width: 1682,"))
                .collect::<Vec<_>>()
                .join("\n");
        let card = done_card("grep -n width src/media.ts", &output, finished(0));
        for detail in [Detail::Overview, Detail::Details] {
            assert_eq!(
                flat(&render(&card, 0, detail, &theme(), 120, true)),
                vec![" ok bash - grep -n width src/media.ts - 83 lines - 120ms"]
            );
        }
    }

    #[test]
    fn the_first_script_line_is_the_argument_summary() {
        let card = done_card("\ncd /tmp\nls -la\n", "a\nb", finished(0));
        assert_eq!(
            flat(&render(&card, 0, Detail::Overview, &theme(), 120, true)),
            vec![" ok bash - cd /tmp - 2 lines - 120ms"]
        );
    }

    #[test]
    fn a_non_zero_exit_is_an_error_row() {
        let card = done_card("false", "$ false\n[step 1 exited 1]", finished(1));
        assert_eq!(
            flat(&render(&card, 0, Detail::Overview, &theme(), 120, true)),
            vec![" x bash - false - 2 lines - exit 1 - 120ms"]
        );
    }

    #[test]
    fn a_refused_step_names_the_refusal() {
        let mut card = done_card(
            "rm -rf /",
            "[stopped at step 1 (write): `rm -rf /` and the steps after it did not run: the user denied it. Do not try it again unless the user asks for it.]",
            json!({ "version": "bash@1", "steps": [], "end": { "kind": "refused", "step": 1, "command": "rm -rf /", "effects": ["write"], "refusal": "denied" } }),
        );
        card.result.as_mut().expect("result").is_error = true;
        assert_eq!(
            flat(&render(&card, 0, Detail::Overview, &theme(), 120, true)),
            vec![" x bash - rm -rf / - 1 line - denied - 120ms"]
        );
    }

    #[test]
    fn an_error_result_without_an_end_summarizes_the_text() {
        let mut card = done_card("ls", "bash needs a `script` string", json!({}));
        card.result.as_mut().expect("result").is_error = true;
        assert_eq!(
            flat(&render(&card, 0, Detail::Overview, &theme(), 120, true)),
            vec![" x bash - ls - 1 line - 120ms - bash needs a `script` string"]
        );
    }

    #[test]
    fn the_expanded_detail_hangs_the_script_and_the_whole_output_below() {
        let output = (1..=12)
            .map(|n| n.to_string())
            .collect::<Vec<_>>()
            .join("\n");
        let card = done_card("seq 1 12", &output, finished(0));
        let rows = flat(&render(&card, 0, Detail::All, &theme(), 120, true));
        assert_eq!(rows[0], " ok bash - seq 1 12 - 12 lines - 120ms");
        assert_eq!(rows[1], " `- $ seq 1 12");
        assert_eq!(rows[2], "  > 1");
        assert_eq!(rows[13], "    12");
        assert_eq!(rows.len(), 14, "{rows:?}");
    }

    #[test]
    fn truncation_warning_renders_expanded_only() {
        let card = done_card(
            "cat big.txt",
            "line1\nline2",
            json!({
                "truncation": {
                    "truncated": true,
                    "truncatedBy": "lines",
                    "outputLines": 2,
                    "totalLines": 10,
                },
                "fullOutputPath": "/tmp/pi-bash-abc",
            }),
        );
        let collapsed = flat(&render(&card, 0, Detail::Overview, &theme(), 120, true));
        assert_eq!(collapsed.len(), 1, "{collapsed:?}");
        let expanded = flat(&render(&card, 0, Detail::All, &theme(), 120, true));
        assert!(
            expanded
                .iter()
                .any(|r| r
                    .contains("[Full output: /tmp/pi-bash-abc. Truncated: showing 2 of 10 lines]")),
            "got: {expanded:?}"
        );
    }

    #[test]
    fn byte_truncation_warning_shape() {
        let card = done_card(
            "cat big.txt",
            "x",
            json!({
                "truncation": {
                    "truncated": true,
                    "truncatedBy": "bytes",
                    "outputLines": 3,
                    "totalLines": 9,
                },
            }),
        );
        let rows = flat(&render(&card, 0, Detail::All, &theme(), 120, true));
        assert!(
            rows.iter()
                .any(|r| r.contains("Truncated: 3 lines shown (50.0KB limit)")),
            "got: {rows:?}"
        );
    }

    #[test]
    fn a_running_card_is_one_row_with_the_working_icon_and_no_duration() {
        // The bash tool emits an empty partial result the moment it starts,
        // so a running card carries an (empty) partial result.
        let card = ToolCallCard {
            id: "t".into(),
            name: "bash".into(),
            args: json!({ "script": "sleep 1" }),
            started: true,
            started_at: Some(Instant::now()),
            result: Some(ToolResultView::default()),
            result_partial: true,
            ..Default::default()
        };
        let rows = flat(&render(&card, 3, Detail::Overview, &theme(), 120, true));
        assert_eq!(rows, vec![" o bash - sleep 1"]);
        // Settling the same card turns the row into the settled row.
        let settled = ToolCallCard {
            ended_at: Some(card.started_at.expect("started") + Duration::from_millis(1000)),
            result: Some(ToolResultView {
                content: vec![json!({ "type": "text", "text": "$ sleep 1" })],
                details: finished(0),
                is_error: false,
            }),
            result_partial: false,
            ..card
        };
        assert_eq!(
            flat(&render(&settled, 3, Detail::Overview, &theme(), 120, true)),
            vec![" ok bash - sleep 1 - 1 line - 1.0s"]
        );
    }

    #[test]
    fn invalid_and_missing_script_shapes() {
        let card = ToolCallCard {
            id: "t".into(),
            name: "bash".into(),
            args: json!({ "script": 5 }),
            started: false,
            ..Default::default()
        };
        assert_eq!(
            flat(&render(&card, 0, Detail::Overview, &theme(), 120, true)),
            vec![" o bash - [invalid arg]"]
        );
        let card = ToolCallCard {
            id: "t".into(),
            name: "bash".into(),
            args: json!({ "script": "" }),
            started: false,
            ..Default::default()
        };
        assert_eq!(
            flat(&render(&card, 0, Detail::Overview, &theme(), 120, true)),
            vec![" o bash"]
        );
        // A pi-era session's `command` still names the command.
        let card = ToolCallCard {
            id: "t".into(),
            name: "bash".into(),
            args: json!({ "command": "ls" }),
            started: false,
            ..Default::default()
        };
        assert_eq!(
            flat(&render(&card, 0, Detail::Overview, &theme(), 120, true)),
            vec![" o bash - ls"]
        );
    }
}
