use eukhe_types::daemon::MemoryLine;

use super::*;
use crate::theme::ColorMode;

fn plain(rows: &[Line]) -> Vec<String> {
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

fn theme() -> Theme {
    Theme::builtin("eukhe", ColorMode::TrueColor)
}

fn summarized() -> MemoryUpdate {
    MemoryUpdate::Summarized {
        lines: vec![
            MemoryLine {
                id: 41,
                count: 1,
                text: "user: fix the\nflaky test".to_string(),
            },
            MemoryLine {
                id: 42,
                count: 1,
                text: "talk: done".to_string(),
            },
        ],
        view_bytes: 87_200,
    }
}

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

#[test]
fn sizes_read_in_decimal_kilobytes() {
    assert_eq!(
        [0, 49, 87_200, 63_949, 128_000].map(format_kb),
        ["0.0 KB", "0.0 KB", "87.2 KB", "63.9 KB", "128.0 KB"].map(str::to_string)
    );
}

/// Collapsed and at `details`, a summarized update is its one summary row;
/// at `all` each built line follows, its text on one line, wrapped under
/// the row.
#[test]
fn a_summarized_update_lists_its_lines_only_at_all() {
    let update = summarized();
    for detail in [Detail::Overview, Detail::Details] {
        assert_eq!(
            plain(&render_memory_update(&update, detail, &theme(), 80, true)),
            vec![
                String::new(),
                " memory: summarized 41+1, 42+1 (view 87.2 KB)".to_string(),
            ]
        );
    }
    assert_eq!(
        plain(&render_memory_update(
            &update,
            Detail::All,
            &theme(),
            24,
            false
        )),
        vec![
            " memory: summarized",
            "   41+1, 42+1 (view 87.2",
            "   KB)",
            "   41+1|user: fix the",
            "     flaky test",
            "   42+1|talk: done",
        ]
    );
}

fn line(id: u64, count: u64) -> MemoryLine {
    MemoryLine {
        id,
        count,
        text: format!("node {id}"),
    }
}

/// Summaries fold into one growing row (nodes accumulate, the newest view
/// size wins); merges fold among themselves; a different kind starts a
/// new row.
#[test]
fn updates_of_one_kind_fold_into_one_row() {
    let mut row = MemoryUpdate::Summarized {
        lines: vec![line(6, 1)],
        view_bytes: 1_000,
    };
    let folded = fold_memory_update(
        &mut row,
        MemoryUpdate::Summarized {
            lines: vec![line(7, 1), line(6, 2)],
            view_bytes: 2_600,
        },
    );
    assert_eq!(folded, None);
    assert_eq!(
        row,
        MemoryUpdate::Summarized {
            lines: vec![line(6, 1), line(7, 1), line(6, 2)],
            view_bytes: 2_600,
        }
    );
    let merge = MemoryUpdate::Merged {
        pairs: 3,
        before_bytes: 130_000,
        after_bytes: 64_000,
    };
    assert_eq!(
        fold_memory_update(&mut row, merge.clone()),
        Some(merge.clone())
    );
    let mut merged = merge;
    assert_eq!(
        fold_memory_update(
            &mut merged,
            MemoryUpdate::Merged {
                pairs: 2,
                before_bytes: 64_000,
                after_bytes: 60_000,
            },
        ),
        None
    );
    assert_eq!(
        merged,
        MemoryUpdate::Merged {
            pairs: 5,
            before_bytes: 130_000,
            after_bytes: 60_000,
        }
    );
}

/// A long coalesced row names only its newest node ids.
#[test]
fn a_long_row_keeps_the_newest_ids_and_counts_the_rest() {
    let update = MemoryUpdate::Summarized {
        lines: (0..20).map(|id| line(id, 1)).collect(),
        view_bytes: 2_600,
    };
    assert_eq!(
        memory_update_summary(&update),
        "memory: summarized ... +12 more, 12+1, 13+1, 14+1, 15+1, 16+1, 17+1, 18+1, 19+1 (view 2.6 KB)"
    );
}

#[test]
fn a_merge_shows_the_view_before_and_after() {
    let update = MemoryUpdate::Merged {
        pairs: 37,
        before_bytes: 128_400,
        after_bytes: 63_900,
    };
    assert_eq!(
        plain(&render_memory_update(
            &update,
            Detail::All,
            &theme(),
            80,
            false
        )),
        vec![" memory: merged 37 pairs, view 128.4 KB -> 63.9 KB"]
    );
    assert_eq!(memory_update_view_bytes(&update), 63_900);
    assert_eq!(memory_update_view_bytes(&summarized()), 87_200);
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
}

/// A live row's node text carrying escape sequences or control characters
/// (a lone `\r`, a tab, a backspace, a vertical tab) prints as one row
/// that keeps its `id+n|` prefix: each reads as a space, and none reaches
/// the terminal to move its cursor.
#[test]
fn control_characters_in_a_live_line_print_as_spaces() {
    assert_eq!(
        one_line("user: run \u{1b}[2Kit\tnow"),
        "user: run it now".to_string()
    );
    assert_eq!(
        one_line("\u{1b}[31mred\u{1b}[0m\u{8}done\u{b}x\u{2028}y"),
        "red done x y".to_string()
    );
    let update = MemoryUpdate::Summarized {
        lines: vec![MemoryLine {
            id: 2,
            count: 1,
            text: "talk: set\rh.model)\"}\nnext".to_string(),
        }],
        view_bytes: 100,
    };
    assert_eq!(
        plain(&render_memory_update(
            &update,
            Detail::All,
            &theme(),
            80,
            false
        )),
        vec![
            " memory: summarized 2+1 (view 0.1 KB)",
            "   2+1|talk: set h.model)\"} next",
        ]
    );
}

#[test]
fn the_gauge_reads_whole_kilobytes_against_the_ceiling() {
    assert_eq!(
        [memory_gauge(87_200), memory_gauge(0), memory_gauge(130_600)],
        ["mem 87/128K", "mem 0/128K", "mem 131/128K"].map(str::to_string)
    );
}
