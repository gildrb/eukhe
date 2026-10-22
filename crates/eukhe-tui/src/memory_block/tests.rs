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

#[test]
fn the_gauge_reads_whole_kilobytes_against_the_ceiling() {
    assert_eq!(
        [87_200, 0, 130_600].map(|bytes| MemoryGauge::seeded(bytes).text()),
        ["mem 87/128K", "mem 0/128K", "mem 131/128K"].map(str::to_string)
    );
}

/// Summaries accumulate their nodes behind the newest view size; a merge
/// replaces them with its pairs and later merges add theirs; a summary
/// after a merge counts afresh. The ids never reach the gauge.
#[test]
fn live_updates_move_the_gauge_and_fold_their_activity() {
    let gauge = MemoryGauge::after(None, &summarized(vec![line(41, 1), line(42, 1)], 90_100));
    assert_eq!(gauge.text(), "mem 90/128K ~2");
    let gauge = MemoryGauge::after(
        Some(MemoryGauge::seeded(87_200)),
        &summarized(vec![line(41, 1), line(42, 1)], 90_100),
    );
    assert_eq!(gauge.text(), "mem 90/128K ~2");
    let gauge = MemoryGauge::after(Some(gauge), &summarized(vec![line(40, 2)], 91_000));
    assert_eq!(gauge.text(), "mem 91/128K ~3");
    let gauge = MemoryGauge::after(Some(gauge), &merged(37, 128_400, 63_900));
    assert_eq!(gauge.text(), "mem 64/128K v37");
    let gauge = MemoryGauge::after(Some(gauge), &merged(2, 63_900, 60_000));
    assert_eq!(gauge.text(), "mem 60/128K v39");
    let gauge = MemoryGauge::after(Some(gauge), &summarized(vec![line(6, 2)], 60_400));
    assert_eq!(gauge.text(), "mem 60/128K ~1");
    assert_eq!(
        MemoryGauge::after(None, &merged(1, 2_000, 1_000)).text(),
        "mem 1/128K v1"
    );
}

/// A new request clears the activity; the view's size stays.
#[test]
fn a_request_begin_clears_the_activity_and_keeps_the_size() {
    let mut gauge = MemoryGauge::after(None, &summarized(vec![line(41, 1)], 90_100));
    gauge.begin_request();
    assert_eq!(gauge, MemoryGauge::seeded(90_100));
    assert_eq!(gauge.text(), "mem 90/128K");
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
