//! The painted frame is ASCII: every byte the inline terminal writes for
//! the view's chrome (icons, markers, badges, more rows, the notice
//! panel, the scope label, hints) is 0x00-0x7F when the session data is.

use super::*;

/// One row of the given shape; the cost/age stay fixed.
fn row(title: &str, section: Section, kind: RowKind, depth: usize) -> AgentsViewRow {
    AgentsViewRow {
        section,
        identity: title.to_string(),
        summary: serde_json::json!({
            "sessionName": title,
            "sessionId": format!("{title}-id"),
            "activeSessionId": format!("{title}-live"),
        }),
        title: title.to_string(),
        model: "mock-1".to_string(),
        cost: 0.5,
        age: "1s".to_string(),
        depth,
        descendant_count: 0,
        running_subagent_count: 0,
        expanded: false,
        parent_identity: None,
        kind,
        has_spawn_code: false,
    }
}

#[test]
fn the_painted_frame_is_ascii_for_ascii_session_data() {
    let (mut mode, _) = mode_with_row("holder", "mock-1");
    let mut rows = vec![
        row("runner", Section::Running, RowKind::Agent, 0),
        row(
            "2 subagents (1 running)",
            Section::Running,
            RowKind::SubagentSummary,
            1,
        ),
    ];
    let mut expanded = row(
        "open subagents",
        Section::Running,
        RowKind::SubagentSummary,
        1,
    );
    expanded.expanded = true;
    rows.push(expanded);
    rows.push(row("child", Section::Running, RowKind::Subagent, 2));
    rows.push(row("print('hi')", Section::Running, RowKind::Code, 2));
    for n in 0..20 {
        rows.push(row(&format!("idle {n}"), Section::Idle, RowKind::Agent, 0));
    }
    rows.push(row("gone", Section::Inactive, RowKind::Agent, 0));
    mode.rows = rows;
    mode.pulse = 1;
    mode.heartbeats = vec![crate::heartbeats_picker::HeartbeatEntry {
        job: crate::heartbeats_picker::parse_heartbeat_job(&serde_json::json!({
            "id": "hb-1",
            "status": "active",
            "source": "heartbeat",
            "activeSessionId": "runner-live",
            "sessionId": "runner-id",
            "schedule": { "expression": "every 30m" },
        }))
        .expect("job parses"),
        session_name: None,
        first_message: None,
    }];
    mode.options.scope = Some(AgentsViewScope {
        session_id: Some("root".to_string()),
        active_session_id: None,
        session_name: Some("root agent".to_string()),
    });
    mode.scope_active = true;
    mode.notice = Some("refused\ntry again later".to_string());
    // The selection at the top shows the running rows and the trailing
    // more row; at the bottom, the leading more row and the last row.
    let mut out: Vec<u8> = Vec::new();
    let mut term = crate::inline_term::InlineTerminal::new(40);
    let mut text = String::new();
    for selected in [0, mode.rows.len() - 1] {
        mode.selected = selected;
        let (lines, cursor) = mode.render_frame(80, 40);
        text.push_str(&render::frame_text(&lines));
        text.push('\n');
        term.paint(
            &mut out,
            crate::inline_term::InlineFrame {
                history: &[],
                live: &lines,
                cursor: cursor.map(|(row, col)| crate::inline_term::LiveCursor { row, col }),
            },
        )
        .expect("paint");
    }
    for needle in [
        "< back - root agent > subagents",
        "  ^ ",
        "  v ",
        " more",
        "@ 1 runner",
        "+ 2 subagents (1 running)",
        "- open subagents",
        "* gone",
        "+---",
        "| refused",
    ] {
        assert!(text.contains(needle), "{needle:?} renders:\n{text}");
    }
    let foreign: Vec<char> = String::from_utf8_lossy(&out)
        .chars()
        .filter(|ch| !ch.is_ascii())
        .collect();
    assert!(
        foreign.is_empty(),
        "non-ASCII bytes painted: {foreign:?}\n{text}"
    );
}
