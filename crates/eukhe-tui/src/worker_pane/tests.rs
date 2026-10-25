use serde_json::{json, Value};

use super::*;
use crate::chat::Detail;
use crate::theme::ColorMode;

fn theme() -> Theme {
    Theme::builtin("eukhe", ColorMode::TrueColor)
}

fn text(rows: &[Line]) -> Vec<String> {
    rows.iter()
        .map(|row| {
            row.iter()
                .map(|span| span.content.as_str())
                .collect::<String>()
                .trim_end()
                .to_string()
        })
        .collect()
}

fn render(pane: &mut WorkerPane, width: usize, rows: usize) -> Vec<String> {
    let theme = theme();
    let look = PaneLook {
        theme: &theme,
        pulse_frame: 0,
        detail: Detail::Overview,
        hint: "Alt+W: hide",
    };
    text(&pane.render(&look, width, rows))
}

fn attach_data(sequence: u64, messages: &Value) -> Value {
    json!({
        "protocol": { "name": "eukhe.daemon", "version": 7 },
        "activeSessionId": "w1",
        "snapshot": {
            "activeSessionId": "w1",
            "summary": { "id": "w1", "cwd": "/tmp" },
            "state": {
                "activeSessionId": "w1",
                "sessionId": "w-sess",
                "isStreaming": true,
                "isCompacting": false,
            },
            "messages": messages,
            "lastEventSequence": sequence,
            "lastEventCursor": null,
        },
        "client": { "id": "mock", "capabilities": [] },
        "lastEventSequence": sequence,
        "lastEventCursor": null,
    })
}

fn assistant(content: &Value, stop: &str) -> eukhe_types::ai::AssistantMessage {
    serde_json::from_value(json!({
        "role": "assistant",
        "content": content,
        "api": "scripted",
        "provider": "scripted",
        "model": "faux-1",
        "usage": {
            "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
            "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
        },
        "stopReason": stop,
        "timestamp": 3,
    }))
    .expect("an assistant message")
}

fn streamed(content: &Value, event: Option<StreamUpdate>) -> TurnUpdate {
    TurnUpdate::AssistantMessage {
        message: Box::new(assistant(content, "toolUse")),
        streaming: true,
        stream_event: event,
    }
}

fn output(text: &str) -> eukhe_types::daemon::ToolOutput {
    serde_json::from_value(json!({ "content": [{ "type": "text", "text": text }] }))
        .expect("a tool output")
}

fn pane() -> WorkerPane {
    WorkerPane::new(
        "w1".to_string(),
        "worker".to_string(),
        WorkerRunState::Running,
        theme(),
    )
}

/// The right split from 140 columns on in a screen that can split, the
/// strip below that (and always inline), at most half the area tall.
#[test]
fn the_pane_splits_right_on_wide_screens_and_strips_below_otherwise() {
    assert_eq!(
        [
            placement(PaneMode::Docked, 160, 40, true),
            placement(PaneMode::Docked, 139, 40, true),
            placement(PaneMode::Docked, 160, 40, false),
            placement(PaneMode::Docked, 100, 10, true),
            placement(PaneMode::Full, 100, 10, true),
            placement(PaneMode::Hidden, 160, 40, true),
        ],
        [
            Placement::Right { width: 64 },
            Placement::Bottom { rows: STRIP_ROWS },
            Placement::Bottom { rows: STRIP_ROWS },
            Placement::Bottom { rows: 5 },
            Placement::Full,
            Placement::None,
        ]
    );
}

/// Events that arrive while the watch attach travels wait; the snapshot
/// lands, the events its cursor already holds drop, the rest apply in
/// order: the streamed text, the tool card running then settled.
#[test]
fn the_pane_seeds_from_the_snapshot_and_folds_the_live_stream() {
    let mut pane = pane();
    assert_eq!(render(&mut pane, 60, 3)[1], " attaching to the worker...");
    pane.apply(
        4,
        TurnUpdate::UserMessage("already in the snapshot".to_string()),
    );
    pane.apply(
        5,
        streamed(
            &json!([{ "type": "text", "text": "Reading the crate" }]),
            Some(StreamUpdate::Start),
        ),
    );
    pane.apply(
        6,
        streamed(
            &json!([
                { "type": "text", "text": "Reading the crate layout" },
                { "type": "toolCall", "id": "t1", "name": "read", "arguments": { "path": "src/lib.rs" } },
            ]),
            None,
        ),
    );
    pane.attached(Ok(attach_data(
        4,
        &json!([{ "role": "user", "content": "already in the snapshot", "timestamp": 1 }]),
    )));
    pane.apply(
        7,
        TurnUpdate::ToolExecutionStart {
            tool_call_id: "t1".to_string(),
            tool_name: "read".to_string(),
            args: json!({ "path": "src/lib.rs" }),
        },
    );
    assert!(pane.working());
    let shown = render(&mut pane, 70, 14);
    assert_eq!(shown[0], " worker - running  Alt+W: hide");
    assert_eq!(
        shown
            .iter()
            .filter(|row| row.contains("already in the snapshot"))
            .count(),
        1,
        "the snapshot's prompt shows once: {shown:?}"
    );
    assert!(
        shown
            .iter()
            .any(|row| row.contains("Reading the crate layout")),
        "{shown:?}"
    );
    assert!(
        shown
            .iter()
            .any(|row| row.contains("read") && row.contains("src/lib.rs")),
        "{shown:?}"
    );
    pane.apply(
        8,
        TurnUpdate::ToolExecutionEnd {
            tool_call_id: "t1".to_string(),
            result: output("one\ntwo"),
            is_error: false,
        },
    );
    // A replayed frame (its sequence already seen) changes nothing.
    pane.apply(8, TurnUpdate::UserMessage("replayed".to_string()));
    pane.apply(9, TurnUpdate::Idle);
    assert!(!pane.working());
    let shown = render(&mut pane, 70, 14);
    assert!(shown.iter().any(|row| row.contains("2 lines")), "{shown:?}");
    assert!(
        !shown.iter().any(|row| row.contains("replayed")),
        "{shown:?}"
    );
    assert_eq!(shown.len(), 14);
}

/// A failed watch attach says why in the pane.
#[test]
fn a_failed_attach_says_why() {
    let mut pane = pane();
    pane.attached(Err("no such session".to_string()));
    assert_eq!(
        render(&mut pane, 60, 2),
        vec![
            " worker - running  Alt+W: hide".to_string(),
            " the worker pane could not attach: no such session".to_string(),
        ]
    );
}

/// The split pads each main row to its width and puts the pane's row
/// after one separator column.
#[test]
fn beside_pads_the_main_rows_and_separates_the_pane() {
    let rows = beside(
        vec![vec![Span::raw("main")]],
        vec![vec![Span::raw("pane")], vec![Span::raw("more")]],
        6,
        &theme(),
    );
    assert_eq!(text(&rows), vec!["main  |pane", "      |more"]);
}
