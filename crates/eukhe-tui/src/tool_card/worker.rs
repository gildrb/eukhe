//! Main's worker cards (`worker_assign`, `worker_forward`): the summary
//! row names the kind and the worker (`ok worker_forward - context -> worker`),
//! and the body always shows what went, from the result's details: the
//! user's messages verbatim, in order, then main's labelled note
//! (`crate::custom_message::forward`). Before the result lands the card
//! shows the call's kind and note.

use super::summary::{body_row, duration, string_arg, SummaryRow};
use super::{panel_status, ToolCallCard};
use crate::custom_message::forward::Forward;
use crate::element::{self, Element, Inline, Status, Tick};
use crate::error_summary::summarize_error_details;
use crate::theme::{Theme, ThemeColor};
use crate::Line;

/// The card's rows (one body at every detail: what went is never folded).
#[must_use]
pub fn render(card: &ToolCallCard, frame: usize, theme: &Theme, width: usize) -> Vec<Line> {
    let forward = card
        .result
        .as_ref()
        .and_then(|result| Forward::from_details(&result.details));
    let kind = forward.as_ref().map_or_else(
        || {
            string_arg(&card.args, "kind")
                .unwrap_or(if card.name == "worker_assign" {
                    "task"
                } else {
                    ""
                })
                .to_string()
        },
        |forward| forward.kind.label().to_lowercase(),
    );
    let worker = forward
        .as_ref()
        .and_then(|forward| forward.worker.clone())
        .or_else(|| string_arg(&card.args, "worker").map(str::to_string))
        .unwrap_or_else(|| "worker".to_string());
    let mut status = panel_status(card);
    let mut error = None;
    if let Some(result) = &card.result {
        if !card.result_partial && result.is_error {
            status = Status::Error;
            error = Some(summarize_error_details(result.text_output(false).trim()));
        }
    }
    let argument = if kind.is_empty() {
        format!("{} {worker}", crate::glyphs::ARROW)
    } else {
        format!("{kind} {} {worker}", crate::glyphs::ARROW)
    };
    let mut rows = vec![SummaryRow {
        status,
        name: &card.name,
        argument,
        results: Vec::new(),
        duration: duration(card),
        error,
    }
    .element(width)];
    let body = match &forward {
        Some(forward) => forward.body(),
        None => string_arg(&card.args, "note")
            .map(|note| format!("[note from main] {note}"))
            .unwrap_or_default(),
    };
    let mut first = true;
    for line in body.split('\n') {
        if body.is_empty() {
            break;
        }
        rows.push(body_row(
            first,
            vec![Inline::role(
                if line.is_empty() { " " } else { line },
                ThemeColor::CustomMessageText,
            )],
        ));
        first = false;
    }
    element::render(&Element::Column(rows), theme, width, Tick(frame))
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::render;
    use crate::theme::{ColorMode, Theme};
    use crate::tool_card::{ToolCallCard, ToolResultView};

    fn text(card: &ToolCallCard) -> Vec<String> {
        let theme = Theme::builtin("eukhe", ColorMode::TrueColor);
        render(card, 0, &theme, 70)
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

    #[test]
    fn a_forward_card_shows_the_users_words_and_the_note_at_every_detail() {
        let card = ToolCallCard {
            id: "c1".to_string(),
            name: "worker_forward".to_string(),
            args: json!({"kind": "redirect", "note": "stop the refactor"}),
            started: true,
            result: Some(ToolResultView {
                content: vec![json!({"type": "text", "text": "forwarded"})],
                details: json!({
                    "deliveryKind": "redirect",
                    "userMessages": [{"text": "actually, keep the old API"}],
                    "note": "stop the refactor",
                    "worker": "worker",
                }),
                is_error: false,
            }),
            ..Default::default()
        };
        let rows = text(&card);
        assert_eq!(rows.len(), 4, "{rows:?}");
        assert!(
            rows[0].contains("worker_forward - redirect -> worker"),
            "{rows:?}"
        );
        assert!(rows[1].ends_with("actually, keep the old API"), "{rows:?}");
        assert!(
            rows[3].ends_with("[note from main] stop the refactor"),
            "{rows:?}"
        );
    }
}
