use eukhe_types::daemon::MemoryLine;

use super::*;

fn status() -> MemoryStatusSnapshot {
    MemoryStatusSnapshot {
        messages: 43,
        lines: 2,
        view_bytes: 87_200,
        unsummarized: 2,
        running: 1,
        model: Some("anthropic/claude-haiku-4-5".to_string()),
        last_error: None,
    }
}

fn line(id: u64, count: u64) -> MemoryLine {
    MemoryLine {
        id,
        count,
        text: format!("node {id}"),
    }
}

fn summarized(lines: Vec<MemoryLine>, view_bytes: u64) -> MemoryUpdate {
    MemoryUpdate::Summarized { lines, view_bytes }
}

fn merged(pairs: u64, before_bytes: u64, after_bytes: u64) -> MemoryUpdate {
    MemoryUpdate::Merged {
        pairs,
        before_bytes,
        after_bytes,
    }
}

#[test]
fn sizes_read_in_decimal_kilobytes() {
    assert_eq!(
        [0, 49, 87_200, 63_949, 128_000].map(format_kb),
        ["0.0 KB", "0.0 KB", "87.2 KB", "63.9 KB", "128.0 KB"].map(str::to_string)
    );
}

/// The gauge formats the sizes like the context segment: whole under
/// 1K, one decimal under 10K, whole K above.
#[test]
fn the_gauge_reads_the_size_against_the_ceiling_like_the_context_segment() {
    assert_eq!(
        [87_200, 0, 1_140, 130_600].map(|bytes| MemoryGauge::seeded(bytes).text()),
        [
            "mem 87K/128K",
            "mem 0/128K",
            "mem 1.1K/128K",
            "mem 131K/128K"
        ]
        .map(str::to_string)
    );
}

/// A live update moves the gauge to the newest view size; inside a
/// request it marks the compactor working, between requests the gauge
/// stays at rest. Neither the nodes nor the pairs nor the ids reach the
/// gauge.
#[test]
fn live_updates_move_the_gauge_and_mark_the_compactor_working_in_a_request() {
    let gauge = MemoryGauge::after(
        &summarized(vec![line(41, 1), line(42, 1)], 90_100),
        UpdateTiming::InRequest,
    );
    assert_eq!(gauge.text(), "mem 90K/128K ~");
    let gauge = MemoryGauge::after(&merged(37, 128_400, 63_900), UpdateTiming::InRequest);
    assert_eq!(gauge.text(), "mem 64K/128K ~");
    assert_eq!(
        MemoryGauge::after(&merged(1, 2_000, 1_000), UpdateTiming::Idle).text(),
        "mem 1K/128K"
    );
}

/// A request's begin or end settles the marker; the view's size stays.
#[test]
fn a_request_boundary_settles_the_marker_and_keeps_the_size() {
    let mut gauge = MemoryGauge::after(
        &summarized(vec![line(41, 1)], 90_100),
        UpdateTiming::InRequest,
    );
    gauge.settle();
    assert_eq!(gauge, MemoryGauge::seeded(90_100));
    assert_eq!(gauge.text(), "mem 90K/128K");
}

#[test]
fn a_default_model_and_plural_compactions_read_naturally() {
    assert_eq!(
        memory_status_header(&MemoryStatusSnapshot {
            messages: 1,
            lines: 1,
            running: 2,
            model: None,
            ..status()
        }),
        "memory: 1 message, view 87.2 KB / 128.0 KB (floor 64.0 KB), 1 line, 2 unsummarized, 2 compactions running, model default"
    );
    assert_eq!(
        memory_status_header(&status()),
        "memory: 43 messages, view 87.2 KB / 128.0 KB (floor 64.0 KB), 2 lines, 2 unsummarized, 1 compaction running, model anthropic/claude-haiku-4-5"
    );
}

/// Node text carrying escape sequences or control characters (a lone
/// `\r`, a tab, a backspace, a vertical tab, a line break) prints as one
/// row: each reads as a space, and none reaches the terminal to move its
/// cursor.
#[test]
fn control_characters_in_a_line_print_as_spaces() {
    assert_eq!(
        one_line("user: run \u{1b}[2Kit\tnow"),
        "user: run it now".to_string()
    );
    assert_eq!(
        one_line("\u{1b}[31mred\u{1b}[0m\u{8}done\u{b}x\u{2028}y"),
        "red done x y".to_string()
    );
    assert_eq!(
        one_line("talk: set\rh.model)\"}\nnext\r\nend"),
        "talk: set h.model)\"} next end".to_string()
    );
}
