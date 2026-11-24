//! The subagent summary line: the scoped view, the header counts, and
//! the ONE merged line under live transitions.

use super::*;

/// The scoped view (the subagents summary line's open action) never
/// lists the anchor -- the scope root is excluded -- so the first-row
/// default stands there.
#[test]
fn scoped_view_keeps_the_first_row_default() {
    let mut mode = scoped_mode(
        Some("p"),
        vec![
            roster_entry("p", "idle", &parent_summary("p")),
            roster_entry("c", "running", &child_summary("c", "p", "worker one")),
        ],
    );
    assert_eq!(mode.rows.len(), 1, "the scope root is excluded");
    assert_eq!(mode.selected, 0);
    assert_eq!(mode.rows[0].summary["sessionId"], "c");
    assert!(mode.anchor_selection_pending, "the wait never resolves");
    // The unresolved wait never blocks the scoped view's own opens:
    // Enter opens the first listed row.
    mode.handle_key("enter");
    let opened = mode
        .opened
        .expect("the scoped view opens despite the never-resolving wait");
    assert_eq!(
        opened.selection,
        SessionSelection::Attach("c-live".to_string())
    );
}

/// A scoped view whose scope root has no children (the all-zero dock's
/// Subagents destination): the roster carries the root alone.
fn childless_scope() -> AgentsViewMode {
    scoped_mode(
        Some("p"),
        vec![roster_entry("p", "idle", &parent_summary("p"))],
    )
}

/// A childless scope is an empty view that keeps its keys: the
/// TS-identical empty-state row renders, search drives the no-match
/// row, Enter on the empty list is a no-op, escape steps back (the
/// query first, then the scope root's chat), ctrl+d quits, and ctrl+n
/// dispatches the new-session action.
#[test]
fn a_childless_scope_is_an_empty_view_that_keeps_its_keys() {
    let mut mode = childless_scope();
    assert!(mode.scope_active && !mode.scope_dropped);
    assert_eq!(mode.rows, Vec::<AgentsViewRow>::new());
    let (lines, _) = mode.render_frame(120, 36);
    let frame = lines.iter().map(flat).collect::<Vec<_>>().join("\n");
    assert!(frame.contains("No sessions yet."), "frame: {frame}");
    // Search still filters the empty roster into the no-match row.
    mode.handle_key("z");
    assert_eq!(mode.query, "z");
    let (lines, _) = mode.render_frame(120, 36);
    let frame = lines.iter().map(flat).collect::<Vec<_>>().join("\n");
    assert!(
        frame.contains("No sessions match your search."),
        "frame: {frame}"
    );
    // Enter on the empty list opens nothing and leaves the view running.
    mode.handle_key("enter");
    assert!(mode.opened.is_none() && mode.running);
    // Escape clears the query; a second escape reopens the scope root.
    mode.handle_key("escape");
    assert_eq!(mode.query, "");
    mode.handle_key("escape");
    let opened = mode
        .opened
        .as_ref()
        .expect("escape reopened the scope root");
    assert_eq!(
        opened.selection,
        SessionSelection::Attach("p-live".to_string())
    );
    assert!(mode.scope_back && !mode.scope_popped && !mode.running);
    // ctrl+d quits the empty view without opening anything.
    let mut mode = childless_scope();
    mode.handle_key("ctrl+d");
    assert!(!mode.running && mode.opened.is_none());
    // ctrl+n dispatches the new-session action from the empty view too
    // (the binding's whole-object shape is pinned in the key_bindings
    // family's scoped test).
    let mut mode = childless_scope();
    mode.handle_key("ctrl+n");
    assert!(!mode.running && mode.opened.is_some());
}

/// TS `countRowsBySection` (the splash header counts) counts agent-kind
/// rows only: a nested running subagent never inflates the header.
#[test]
fn header_counts_exclude_nested_rows() {
    let mut mode = mode_with_parent_and_child();
    assert_eq!(mode.rows.len(), 2);
    assert_eq!(mode.rows[1].kind, RowKind::Subagent);
    let (lines, _) = mode.render_frame(120, 36);
    let header = lines
        .iter()
        .map(flat)
        .find(|line| line.contains("running,"))
        .expect("the splash carries the agents count line");
    // The count rides the art line (the splash paints them together):
    // assert the count, not the full line.
    assert!(
        header.contains("agents 0 running, 1 idle, 0 inactive"),
        "header: {header}"
    );
}

#[test]
fn alt_right_toggles_the_subagent_list() {
    // A settled tree: its child sits behind the ONE summary line.
    let mut mode = mode_with_parent_and_child();
    mode.roster[1]["status"] = serde_json::json!("idle");
    mode.rebuild_rows();
    // Collapsed: the parent, its summary row, nothing else.
    assert_eq!(mode.rows.len(), 2);
    assert_eq!(mode.rows[1].kind, RowKind::SubagentSummary);
    assert!(!mode.rows[1].expanded);
    // alt+right on the parent row (descendantCount > 0) expands.
    mode.handle_key("alt+right");
    assert_eq!(mode.rows.len(), 3);
    assert!(mode.rows[1].expanded);
    assert_eq!(mode.rows[2].kind, RowKind::Subagent);
    assert_eq!(mode.rows[2].depth, 1);
    // alt+right again collapses.
    mode.handle_key("alt+right");
    assert_eq!(mode.rows.len(), 2);
    assert!(!mode.rows[1].expanded);
}

/// A mode over one parent with two running and two idle children (the
/// operator's mixed roster): a live tree.
fn mode_with_mixed_children() -> AgentsViewMode {
    let mut mode = AgentsViewMode::new(AgentsViewOptions {
        socket_path: PathBuf::from("/tmp/agents-view-test.sock"),
        cwd: PathBuf::from("/tmp"),
        session_dir: None,
        theme: crate::theme::Theme::builtin("forge", crate::theme::ColorMode::TrueColor),
        version: "0.0.0".to_string(),
        anchor_session_id: None,
        return_active_session_id: None,
        scope: None,
        query: None,
        expanded_ancestors: Vec::new(),
        selected_row_identity: None,
        selected_key: None,
        status_message: None,
        keybindings: crate::keybindings::KeybindingsManager::new(),
        show_hardware_cursor: false,
        screen_mode: crate::screen_mode::ScreenMode::Inline,
        incident_notice_state: None,
        create_config: serde_json::json!({}),
    });
    mode.roster = vec![
        roster_entry("p", "idle", &parent_summary("p")),
        roster_entry("r1", "running", &child_summary("r1", "p", "runner one")),
        roster_entry("r2", "running", &child_summary("r2", "p", "runner two")),
        roster_entry("i1", "idle", &child_summary("i1", "p", "old worker one")),
        roster_entry("i2", "idle", &child_summary("i2", "p", "old worker two")),
    ];
    mode.rebuild_rows();
    mode
}

/// A live tree lists its runners as branches and folds the settled
/// children into ONE `N not running` line: Enter on it opens them in
/// spawn order, Enter again closes it, and alt+right on the parent row
/// toggles the same fold.
#[test]
fn enter_opens_the_fold_behind_the_runners() {
    let mut mode = mode_with_mixed_children();
    // Closed: the parent, the two runners, the fold.
    let titles = |mode: &AgentsViewMode| {
        mode.rows
            .iter()
            .map(|row| row.title.clone())
            .collect::<Vec<_>>()
    };
    assert_eq!(
        titles(&mode),
        ["p name", "runner one", "runner two", "2 not running"]
    );
    assert_eq!(mode.rows[3].identity, "subagents:file:/x/p.jsonl");
    // Enter on the fold: the settled children render under it.
    for _ in 0..3 {
        mode.handle_key("down");
    }
    mode.handle_key("enter");
    assert_eq!(
        titles(&mode),
        [
            "p name",
            "runner one",
            "runner two",
            "2 not running",
            "old worker one",
            "old worker two",
        ]
    );
    assert!(mode.rows[3].expanded);
    // Enter again closes it.
    mode.handle_key("enter");
    assert_eq!(mode.rows.len(), 4);
    assert!(!mode.rows[3].expanded);
    // alt+right on the parent row opens the same fold.
    let mut mode = mode_with_mixed_children();
    mode.handle_key("alt+right");
    assert_eq!(mode.rows.len(), 6);
    assert!(mode.rows[3].expanded, "alt+right opens the fold");
}

/// Live transitions (roster pushes): a selected runner that finishes
/// moves behind its parent's fold, the fold opens so the selection
/// keeps following its session, and the counts update in the same
/// rebuild; restarted, it returns to the running branches.
#[test]
fn live_transitions_move_the_branch_and_keep_the_selection() {
    let mut mode = mode_with_mixed_children();
    mode.handle_key("down");
    assert_eq!(mode.rows[mode.selected].title, "runner one");
    let selected_identity = mode.rows[mode.selected].identity.clone();
    // The runner finishes: its roster row flips to idle.
    let idle_flip = roster_entry("r1", "idle", &child_summary("r1", "p", "runner one"));
    mode.apply_roster_update(vec![idle_flip], Vec::new(), false);
    let fold = mode
        .rows
        .iter()
        .find(|row| row.kind == RowKind::SubagentSummary)
        .expect("the fold");
    assert_eq!(fold.title, "3 not running");
    assert!(fold.expanded, "the fold opened behind the selection");
    let settled = &mode.rows[mode.selected];
    assert_eq!(
        settled.identity, selected_identity,
        "the selection stays on the session it followed"
    );
    assert_ne!(settled.section, Section::Running, "the section flipped");
    // The runner restarts: it returns to the branches.
    let running_flip = roster_entry("r1", "running", &child_summary("r1", "p", "runner one"));
    mode.apply_roster_update(vec![running_flip], Vec::new(), false);
    assert_eq!(
        mode.rows
            .iter()
            .find(|row| row.kind == RowKind::SubagentSummary)
            .map(|row| row.title.as_str()),
        Some("2 not running")
    );
    assert_eq!(mode.rows[mode.selected].identity, selected_identity);
    assert_eq!(mode.rows[mode.selected].section, Section::Running);
}

/// The rendered frame draws the live tree: each running branch under
/// its parent with its guide, the settled child behind the closing
/// fold line, and no `N subagents` summary line.
#[test]
fn frame_renders_the_live_tree() {
    let mut grandchild = child_summary("gc", "c", "grandkid");
    grandchild["rlmChildId"] = serde_json::json!("child-gc");
    let mut mode = mode_with_parent_and_child();
    mode.roster.push(roster_entry("gc", "running", &grandchild));
    mode.roster.push(roster_entry(
        "i1",
        "idle",
        &child_summary("i1", "p", "old worker"),
    ));
    mode.rebuild_rows();
    let (lines, _) = mode.render_frame(120, 36);
    let frame = lines.iter().map(flat).collect::<Vec<_>>().join("\n");
    for row in ["|- . worker one", "|  `- . grandkid", "`- + 1 not running"] {
        assert!(frame.contains(row), "{row:?} renders: {frame}");
    }
    assert!(!frame.contains("subagents ("), "no summary line: {frame}");
}
