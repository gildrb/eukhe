use eukhe_types::daemon::{MemoryKindCount, MemoryStatusSnapshot, MemoryTree, MemoryTreeLevel};

use super::*;
use crate::theme::ColorMode;

fn theme() -> Theme {
    Theme::builtin("eukhe", ColorMode::TrueColor)
}

fn kb() -> KeybindingsManager {
    KeybindingsManager::new()
}

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

fn status() -> MemoryStatusSnapshot {
    MemoryStatusSnapshot {
        messages: 3,
        lines: 2,
        view_bytes: 30,
        unsummarized: 1,
        running: 0,
        model: None,
        last_error: None,
    }
}

fn kinds(pairs: &[(&str, u64)]) -> Vec<MemoryKindCount> {
    pairs
        .iter()
        .map(|(kind, count)| MemoryKindCount {
            kind: (*kind).to_string(),
            count: *count,
        })
        .collect()
}

fn node(
    (id, count): (u64, u64),
    (first, last): (&str, &str),
    kind_counts: &[(&str, u64)],
    summary: Option<&str>,
) -> MemoryTreeNode {
    MemoryTreeNode {
        id,
        count,
        first_date: first.to_string(),
        last_date: last.to_string(),
        kinds: kinds(kind_counts),
        summary: summary.map(str::to_string),
    }
}

const OCT_1: &str = "2026-10-01T09:00:00.000+02:00";
const OCT_2: &str = "2026-10-02T10:00:00.000+02:00";
const OCT_3: &str = "2026-10-03T08:00:00.000+02:00";

fn lines_fetch(zoom: Option<MemoryZoom>, nodes: Vec<MemoryTreeNode>) -> MemoryTreeFetch {
    MemoryTreeFetch {
        node: zoom,
        reply: Ok(Some(MemoryTree {
            status: status(),
            node: zoom,
            level: MemoryTreeLevel::Lines { nodes },
        })),
    }
}

/// The view: `0+2` (two days, summarized over two lines) and `2+1` (one
/// message, not summarized yet).
fn top_level() -> MemoryTreeFetch {
    lines_fetch(
        None,
        vec![
            node(
                (0, 2),
                (OCT_1, OCT_2),
                &[("talk", 1), ("user", 1)],
                Some("user: hi\ntalk: hello"),
            ),
            node((2, 1), (OCT_3, OCT_3), &[("user", 1)], None),
        ],
    )
}

fn halves_of_0_2() -> MemoryTreeFetch {
    lines_fetch(
        Some(MemoryZoom { id: 0, count: 2 }),
        vec![
            node((0, 1), (OCT_1, OCT_1), &[("user", 1)], Some("user: hi")),
            node((1, 1), (OCT_2, OCT_2), &[("talk", 1)], Some("talk: hello")),
        ],
    )
}

fn message_0() -> MemoryTreeFetch {
    let zoom = MemoryZoom { id: 0, count: 1 };
    MemoryTreeFetch {
        node: Some(zoom),
        reply: Ok(Some(MemoryTree {
            status: status(),
            node: Some(zoom),
            level: MemoryTreeLevel::Message {
                message: MemoryTreeMessage {
                    id: 0,
                    kind: "user".to_string(),
                    date: OCT_1.to_string(),
                    text: "hi there\r\nsecond\tline".to_string(),
                },
            },
        })),
    }
}

const HEADER: &str = " memory: 3 messages, view 0.0 KB / 128.0 KB (floor 64.0 KB), 2 lines, 1 unsummarized, 0 compactions running, model default";

/// The whole frame at a width that fits every row: the rule, the
/// header, a blank, `content`, the hint and the trailing blank.
fn frame(content: &[&str]) -> Vec<String> {
    let mut rows = vec!["-".repeat(160), HEADER.to_string(), String::new()];
    rows.extend(content.iter().map(|row| (*row).to_string()));
    rows.push(format!(" {}", hint_text(&kb())));
    rows.push(String::new());
    rows
}

fn render(tree: &mut MemoryTreeView) -> Vec<String> {
    plain(&tree.render(&theme(), 160, &kb(), 40))
}

#[test]
fn date_spans_drop_what_the_end_shares_with_the_start() {
    assert_eq!(
        [
            date_span(OCT_1, OCT_1),
            date_span(OCT_1, "2026-10-01T09:00:59.000+02:00"),
            date_span(OCT_1, "2026-10-01T17:30:00.000+02:00"),
            date_span(OCT_1, OCT_2),
            date_span("2025-12-31T23:00:00.000+01:00", OCT_2),
            date_span("yesterday", "today"),
            date_span("now", "now"),
        ],
        [
            "2026-10-01 09:00",
            "2026-10-01 09:00",
            "2026-10-01 09:00 -> 17:30",
            "2026-10-01 09:00 -> 10-02 10:00",
            "2025-12-31 23:00 -> 2026-10-02 10:00",
            "yesterday -> today",
            "now",
        ]
        .map(str::to_string)
    );
    assert_eq!(message_date(OCT_3), "2026-10-03 08:00");
}

#[test]
fn kinds_and_summaries_read_as_one_sanitized_line() {
    assert_eq!(
        kind_tags(&kinds(&[("user", 3), ("talk", 2), ("tool", 4)])),
        "user 3, talk 2, tool 4"
    );
    assert_eq!(kind_tags(&[]), "");
    assert_eq!(
        summary_line("user: run \u{1b}[2Kit\tnow\nsecond line"),
        "user: run it now"
    );
    assert_eq!(summary_line(""), "");
}

/// Before the view lands the panel says it is loading; then every view
/// line is one row, the newest selected.
#[test]
fn the_view_lists_one_dated_labelled_row_per_line() {
    let mut tree = MemoryTreeView::new();
    assert_eq!(render(&mut tree), {
        let mut rows = frame(&["  loading..."]);
        rows[1] = " memory: loading...".to_string();
        rows
    });
    tree.apply(top_level());
    assert_eq!(
        render(&mut tree),
        frame(&[
            "  + 0+2  2026-10-01 09:00 -> 10-02 10:00  talk 1, user 1  user: hi",
            "> + 2+1  2026-10-03 08:00  user 1  (not summarized yet)",
        ])
    );
}

/// A row wider than the panel is cut with an ellipsis; selecting it shows
/// its whole summary wrapped under it.
#[test]
fn a_long_row_is_cut_and_its_selection_shows_the_whole_summary() {
    let mut tree = MemoryTreeView::new();
    tree.apply(lines_fetch(
        None,
        vec![node(
            (0, 4),
            (OCT_1, OCT_2),
            &[("user", 2), ("talk", 2)],
            Some("user: please fix the flaky login test and ship it"),
        )],
    ));
    let rows = plain(&tree.render(&theme(), 50, &kb(), 40));
    let row = rows
        .iter()
        .position(|row| row.starts_with("> + 0+4"))
        .expect("the node's row");
    assert_eq!(
        rows[row..row + 3].to_vec(),
        vec![
            "> + 0+4  2026-10-01 09:00 -> 10-02 10:00  user ...",
            "      user: please fix the flaky login test and",
            "        ship it",
        ]
    );
}

/// Right opens a line (fetching it, with a loading row meanwhile), its
/// halves appear indented under it, Right again steps into the first
/// half, and a one-message line opens into the message whole.
#[test]
fn opening_lines_drills_down_to_the_message() {
    let mut tree = MemoryTreeView::new();
    tree.apply(top_level());
    render(&mut tree);
    assert_eq!(tree.handle_key("up", &kb()), MemoryTreeAction::None);
    assert_eq!(
        tree.handle_key("right", &kb()),
        MemoryTreeAction::Fetch(MemoryZoom { id: 0, count: 2 })
    );
    assert_eq!(
        render(&mut tree),
        frame(&[
            "> - 0+2  2026-10-01 09:00 -> 10-02 10:00  talk 1, user 1  user: hi",
            "      user: hi",
            "      talk: hello",
            "    loading...",
            "  + 2+1  2026-10-03 08:00  user 1  (not summarized yet)",
        ])
    );
    tree.apply(halves_of_0_2());
    render(&mut tree);
    assert_eq!(tree.handle_key("right", &kb()), MemoryTreeAction::None);
    assert_eq!(
        tree.handle_key("right", &kb()),
        MemoryTreeAction::Fetch(MemoryZoom { id: 0, count: 1 })
    );
    tree.apply(message_0());
    assert_eq!(
        render(&mut tree),
        frame(&[
            "  - 0+2  2026-10-01 09:00 -> 10-02 10:00  talk 1, user 1  user: hi",
            ">   - 0+1  2026-10-01 09:00  user 1  user: hi",
            "      user  2026-10-01 09:00",
            "      hi there",
            "      second line",
            "    + 1+1  2026-10-02 10:00  talk 1  talk: hello",
            "  + 2+1  2026-10-03 08:00  user 1  (not summarized yet)",
        ])
    );
    assert_eq!(tree.handle_key("down", &kb()), MemoryTreeAction::None);
    assert_eq!(
        tree.selected,
        Some(Item::Message(NodeKey { id: 0, count: 1 }))
    );
    assert_eq!(
        render(&mut tree)[5],
        ">     user  2026-10-01 09:00".to_string()
    );
}

/// Left climbs from a message to its line, closes an open line, and from
/// a closed line selects its parent; Enter reopens a line from the cache
/// without asking the daemon again.
#[test]
fn left_collapses_and_climbs_and_reopening_uses_the_cache() {
    let mut tree = MemoryTreeView::new();
    tree.apply(top_level());
    render(&mut tree);
    tree.handle_key("up", &kb());
    tree.handle_key("enter", &kb());
    tree.apply(halves_of_0_2());
    render(&mut tree);
    tree.handle_key("right", &kb());
    tree.handle_key("enter", &kb());
    tree.apply(message_0());
    render(&mut tree);
    tree.handle_key("down", &kb());
    render(&mut tree);
    let key = |id, count| NodeKey { id, count };
    tree.handle_key("left", &kb());
    assert_eq!(tree.selected, Some(Item::Node(key(0, 1))));
    tree.handle_key("left", &kb());
    assert_eq!(
        (tree.selected, tree.expanded.clone()),
        (Some(Item::Node(key(0, 1))), HashSet::from([key(0, 2)]))
    );
    tree.handle_key("left", &kb());
    assert_eq!(tree.selected, Some(Item::Node(key(0, 2))));
    tree.handle_key("left", &kb());
    assert_eq!(tree.expanded, HashSet::new());
    tree.handle_key("left", &kb());
    assert_eq!(tree.selected, Some(Item::Node(key(0, 2))));
    assert_eq!(tree.handle_key("enter", &kb()), MemoryTreeAction::None);
    assert_eq!(tree.handle_key("right", &kb()), MemoryTreeAction::None);
    assert_eq!(tree.handle_key("right", &kb()), MemoryTreeAction::None);
    assert_eq!(
        render(&mut tree),
        frame(&[
            "  - 0+2  2026-10-01 09:00 -> 10-02 10:00  talk 1, user 1  user: hi",
            ">   - 0+1  2026-10-01 09:00  user 1  user: hi",
            "      user  2026-10-01 09:00",
            "      hi there",
            "      second line",
            "    + 1+1  2026-10-02 10:00  talk 1  talk: hello",
            "  + 2+1  2026-10-03 08:00  user 1  (not summarized yet)",
        ])
    );
}

/// A failed or empty level shows inline; closing and reopening a failed
/// line asks again.
#[test]
fn failures_and_missing_lines_show_inline_and_retry_on_reopen() {
    let mut tree = MemoryTreeView::new();
    tree.apply(top_level());
    render(&mut tree);
    let zoom = MemoryZoom { id: 2, count: 1 };
    assert_eq!(
        tree.handle_key("enter", &kb()),
        MemoryTreeAction::Fetch(zoom)
    );
    tree.apply(MemoryTreeFetch {
        node: Some(zoom),
        reply: Err("timed out".to_string()),
    });
    assert_eq!(
        render(&mut tree)[4..6].to_vec(),
        vec![
            "> - 2+1  2026-10-03 08:00  user 1  (not summarized yet)".to_string(),
            "    ! timed out".to_string(),
        ]
    );
    assert_eq!(tree.handle_key("enter", &kb()), MemoryTreeAction::None);
    assert_eq!(
        tree.handle_key("enter", &kb()),
        MemoryTreeAction::Fetch(zoom)
    );
    tree.apply(MemoryTreeFetch {
        node: Some(zoom),
        reply: Ok(Some(MemoryTree {
            status: status(),
            node: Some(zoom),
            level: MemoryTreeLevel::NoLine,
        })),
    });
    assert_eq!(render(&mut tree)[5], "    (no line here)".to_string());
    let mut empty = MemoryTreeView::new();
    empty.apply(MemoryTreeFetch {
        node: None,
        reply: Ok(None),
    });
    assert_eq!(
        render(&mut empty)[3],
        "  This session keeps no chat memory.".to_string()
    );
}

/// A message taller than the window scrolls through its own rows before
/// the selection moves on.
#[test]
fn a_tall_message_scrolls_before_the_selection_moves() {
    let mut tree = MemoryTreeView::new();
    tree.apply(lines_fetch(
        None,
        vec![
            node((0, 1), (OCT_1, OCT_1), &[("tool", 1)], Some("tool: ls")),
            node((1, 1), (OCT_2, OCT_2), &[("talk", 1)], Some("talk: done")),
        ],
    ));
    tree.handle_key("home", &kb());
    let zoom = MemoryZoom { id: 0, count: 1 };
    tree.handle_key("right", &kb());
    tree.apply(MemoryTreeFetch {
        node: Some(zoom),
        reply: Ok(Some(MemoryTree {
            status: status(),
            node: Some(zoom),
            level: MemoryTreeLevel::Message {
                message: MemoryTreeMessage {
                    id: 0,
                    kind: "tool".to_string(),
                    date: OCT_1.to_string(),
                    text: (1..=8)
                        .map(|n| format!("line {n}"))
                        .collect::<Vec<_>>()
                        .join("\n"),
                },
            },
        })),
    });
    // Twelve rows: the rule, the header and the blank, six of content,
    // the scroll indicator, the hint and its blank.
    let window = |tree: &mut MemoryTreeView| {
        let rows = plain(&tree.render(&theme(), 160, &kb(), 12));
        rows[3..rows.len() - 2].to_vec()
    };
    window(&mut tree);
    tree.handle_key("down", &kb());
    assert_eq!(
        window(&mut tree),
        vec![
            ">   tool  2026-10-01 09:00",
            "    line 1",
            "    line 2",
            "    line 3",
            "    line 4",
            "    line 5",
            "  (2/3)",
        ]
    );
    for _ in 0..3 {
        tree.handle_key("down", &kb());
    }
    assert_eq!(
        window(&mut tree),
        vec![
            "    line 3",
            "    line 4",
            "    line 5",
            "    line 6",
            "    line 7",
            "    line 8",
            "  (2/3)",
        ]
    );
    tree.handle_key("down", &kb());
    assert_eq!(tree.selected, Some(Item::Node(NodeKey { id: 1, count: 1 })));
}

#[test]
fn escape_q_and_ctrl_c_close_the_tree() {
    let mut tree = MemoryTreeView::new();
    assert_eq!(
        ["escape", "q", "ctrl+c"].map(|key| tree.handle_key(key, &kb())),
        [MemoryTreeAction::Close; 3]
    );
}
