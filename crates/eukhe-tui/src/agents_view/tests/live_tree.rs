//! The live agent tree: a running tree renders nested under its root
//! with tree guides, and the arrows walk it in display order.

use super::*;

/// A running root, its two children (spawned in that order), and a
/// grandchild under the first child.
fn three_level_roster() -> Vec<serde_json::Value> {
    let spawned = |id: &str, parent: &str, name: &str, created: &str, depth: u64| {
        let mut summary = child_summary(id, parent, name);
        summary["created"] = serde_json::json!(created);
        summary["rlmDepth"] = serde_json::json!(depth);
        summary
    };
    let mut root = parent_summary("r");
    root["created"] = serde_json::json!("2026-11-24T08:00:00.000Z");
    vec![
        roster_entry("r", "running", &root),
        roster_entry(
            "b",
            "running",
            &spawned("b", "r", "batch two", "2026-11-24T08:02:00.000Z", 1),
        ),
        roster_entry(
            "a",
            "idle",
            &spawned("a", "r", "batch one", "2026-11-24T08:01:00.000Z", 1),
        ),
        roster_entry(
            "g",
            "running",
            &spawned("g", "a", "batch one helper", "2026-11-24T08:03:00.000Z", 2),
        ),
    ]
}

/// The list paints the tree: each row's guide, status icon, and title
/// lead its session cell (the model and cost/age columns follow).
#[test]
fn the_list_paints_the_running_tree_nested() {
    let mode = fresh_mode(three_level_roster());
    let session_cells: Vec<String> = mode
        .render_list(120, 12)
        .iter()
        .map(|line| {
            flat(line)
                .chars()
                .take(26)
                .collect::<String>()
                .trim_end()
                .to_string()
        })
        .collect();
    assert_eq!(
        session_cells,
        vec![
            "Session",
            "",
            "Running (1)",
            ". r name",
            "|- * batch one",
            "|  `- . batch one helper",
            "`- . batch two",
        ]
    );
}

/// Down and Up walk the tree in display order, and Enter on the
/// grandchild opens it with its ancestor chain.
#[test]
fn the_arrows_walk_the_tree_in_display_order() {
    let mut mode = fresh_mode(three_level_roster());
    let selected = |mode: &AgentsViewMode| mode.rows[mode.selected].title.clone();
    assert_eq!(selected(&mode), "r name");
    let mut walk = Vec::new();
    for _ in 0..3 {
        mode.handle_key("down");
        walk.push(selected(&mode));
    }
    assert_eq!(walk, ["batch one", "batch one helper", "batch two"]);
    mode.handle_key("up");
    assert_eq!(selected(&mode), "batch one helper");
    mode.handle_key("enter");
    let opened = mode.opened.expect("enter opens the grandchild");
    assert_eq!(
        opened.selection,
        SessionSelection::Attach("g-live".to_string())
    );
    assert_eq!(opened.expanded_ancestors, ["r", "a"]);
}

/// The program key on a live tree's root shows the spawn program above
/// the branches it launched, the code rows on the root's trunk guide;
/// a second press hides it.
#[test]
fn the_program_shows_on_the_live_trunk() {
    let mut roster = three_level_roster();
    roster[2]["summary"]["spawnCode"] = serde_json::json!("spawn(batch)");
    let mut mode = fresh_mode(roster);
    mode.handle_key("ctrl+o");
    let shape: Vec<(RowKind, &str, Option<&str>)> = mode
        .rows
        .iter()
        .map(|row| (row.kind, row.title.as_str(), row.guide.as_deref()))
        .collect();
    assert_eq!(
        shape,
        [
            (RowKind::Agent, "r name", None),
            (RowKind::Code, "", Some("|  ")),
            (RowKind::Code, "spawn(batch)", Some("|  ")),
            (RowKind::Code, "", Some("|  ")),
            (RowKind::Subagent, "batch one", Some("|- ")),
            (RowKind::Subagent, "batch one helper", Some("|  `- ")),
            (RowKind::Subagent, "batch two", Some("`- ")),
        ]
    );
    mode.handle_key("ctrl+o");
    assert!(mode.rows.iter().all(|row| row.kind != RowKind::Code));
}
