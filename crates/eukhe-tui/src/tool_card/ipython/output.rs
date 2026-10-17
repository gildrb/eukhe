//! Expanded cell output; painting and counting share the same output decisions.

use super::{
    is_agent_message_receipt, normalize_error_details, str_width, summarize_error_details, wrapped,
    Element, Inline, IpythonDetails, IpythonError, ThemeColor, ToolCallCard, Value, OUTPUT_INDENT,
};

/// `splitTraceback`: the lines before the traceback opener are ordinary
/// output; the rest is the traceback proper.
fn split_traceback(text: &str, error_name: Option<&str>) -> Option<(String, String)> {
    let normalized = normalize_error_details(text);
    if normalized.trim().is_empty() {
        return None;
    }
    let lines: Vec<&str> = normalized.split('\n').collect();
    let mut traceback_index = lines
        .iter()
        .position(|line| line.contains("Traceback (most recent call last):"));
    if traceback_index.is_none() {
        if let Some(error_name) = error_name {
            traceback_index = lines
                .iter()
                .position(|line| line.trim_start().starts_with(&format!("{error_name}:")));
        }
    }
    let traceback_index = traceback_index?;
    let output = lines[..traceback_index].join("\n").trim_end().to_string();
    let traceback = lines[traceback_index..].join("\n").trim().to_string();
    Some((output, traceback))
}

/// The error summary line for a cell that failed without a traceback (TS
/// `formatIpythonErrorSummary`).
fn format_ipython_error_summary(error: &IpythonError) -> String {
    let normalized_value = normalize_error_details(&error.evalue);
    if normalized_value.trim().is_empty() {
        return error.ename.clone();
    }
    let value = summarize_error_details(&normalized_value);
    if value == "Error" {
        return error.ename.clone();
    }
    if str_width(&value) <= 48 {
        format!("{}: {value}", error.ename)
    } else {
        error.ename.clone()
    }
}

/// The expanded output rows (TS `renderOutput`).
pub(super) fn render_output(
    card: &ToolCallCard,
    details: &IpythonDetails,
    rows: &mut Vec<Element>,
    has_code: bool,
    show_images: bool,
) {
    let blocks = card
        .result
        .as_ref()
        .map(|result| result.content.as_slice())
        .unwrap_or_default();
    let text = blocks
        .iter()
        .filter(|block| block.get("type").and_then(Value::as_str) == Some("text"))
        .map(|block| {
            block
                .get("text")
                .and_then(Value::as_str)
                .unwrap_or_default()
        })
        .collect::<Vec<_>>()
        .join("\n");
    let image_count = blocks
        .iter()
        .filter(|block| block.get("type").and_then(Value::as_str) == Some("image"))
        .count();
    let is_error = card.result.as_ref().is_some_and(|r| r.is_error);
    let traceback = if is_error || details.status.as_deref() == Some("error") {
        split_traceback(&text, details.error_ename.as_deref())
    } else {
        None
    };

    let mut output_started = false;
    let mut output_marker_pending = true;
    let mut rendered_text_output = false;
    let start_output = |output_started: &mut bool, rows: &mut Vec<Element>| {
        if *output_started {
            return;
        }
        *output_started = true;
        if has_code {
            rows.push(Element::blank());
        }
    };

    if let Some((output, _)) = &traceback {
        if !output.is_empty() {
            start_output(&mut output_started, rows);
            rendered_text_output = true;
            render_output_text(rows, output, &OutputLabel::Out, &mut output_marker_pending);
        }
    } else if !text.trim().is_empty()
        && !is_agent_message_receipt(Some(text.as_str()), &details.sent_agent_messages)
    {
        start_output(&mut output_started, rows);
        rendered_text_output = true;
        let label = if is_error {
            OutputLabel::Err
        } else {
            OutputLabel::Out
        };
        render_output_text(
            rows,
            &normalize_error_details(&text),
            &label,
            &mut output_marker_pending,
        );
    }

    if !rendered_text_output && card.result_partial {
        start_output(&mut output_started, rows);
        rows.push(wrapped(
            output_prefix(&mut output_marker_pending),
            vec![Inline::role("waiting for output...", ThemeColor::Muted)],
        ));
    } else if !rendered_text_output
        && traceback.is_none()
        && details.error.is_none()
        && details.sent_agent_messages.is_empty()
        && card.started
        && image_count == 0
    {
        start_output(&mut output_started, rows);
        rows.push(wrapped(
            output_prefix(&mut output_marker_pending),
            vec![Inline::role("no output", ThemeColor::Muted)],
        ));
    }

    if let Some((_, traceback)) = &traceback {
        start_output(&mut output_started, rows);
        render_output_text(
            rows,
            traceback,
            &OutputLabel::Err,
            &mut output_marker_pending,
        );
    } else if let Some(error) = &details.error {
        start_output(&mut output_started, rows);
        render_output_text(
            rows,
            &format_ipython_error_summary(error),
            &OutputLabel::Err,
            &mut output_marker_pending,
        );
    }

    if image_count > 0 {
        start_output(&mut output_started, rows);
        let noun = if image_count == 1 { "image" } else { "images" };
        let text = if show_images {
            format!("{image_count} {noun} rendered below")
        } else {
            format!("{image_count} {noun} hidden")
        };
        rows.push(wrapped(
            output_prefix(&mut output_marker_pending),
            vec![Inline::role(text, ThemeColor::Muted)],
        ));
    }
}

/// The output gutter: the `>` marker on the first output row, the
/// continuation indent after it.
fn output_prefix(output_marker_pending: &mut bool) -> Vec<Inline> {
    if *output_marker_pending {
        *output_marker_pending = false;
        vec![Inline::role(
            format!(" {} ", crate::glyphs::POINTER),
            ThemeColor::Dim,
        )]
    } else {
        vec![Inline::plain(OUTPUT_INDENT)]
    }
}

enum OutputLabel {
    Out,
    Err,
}

/// One output section: `out` lines in toolOutput, `err` lines muted
/// (stderr and tracebacks), the first line marked `>`.
fn render_output_text(
    rows: &mut Vec<Element>,
    text: &str,
    label: &OutputLabel,
    output_marker_pending: &mut bool,
) {
    let role = match label {
        OutputLabel::Out => ThemeColor::ToolOutput,
        OutputLabel::Err => ThemeColor::Muted,
    };
    for line in text.split('\n') {
        // Blank rows render one styled space (TS `theme.fg(color, line || " ")`).
        rows.push(wrapped(
            output_prefix(output_marker_pending),
            vec![Inline::role(if line.is_empty() { " " } else { line }, role)],
        ));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn split_traceback_parts() {
        let (output, traceback) = split_traceback(
            "before\nTraceback (most recent call last):\n  File x\nValueError: boom",
            None,
        )
        .unwrap();
        assert_eq!(output, "before");
        assert!(traceback.starts_with("Traceback"));
        assert!(traceback.ends_with("boom"));
    }
}
