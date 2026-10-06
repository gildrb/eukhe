/// The arrows never skip an empty group (the operator's 2026-09-26
/// muscle-memory directive): one press steps to the neighboring
/// rendered group and wraps, so every group is visited in order
/// in both directions and N groups take exactly N presses to cycle.
#[test]
fn dock_arrows_visit_every_group_even_when_empty() {
    // The all-zero dock with the factory lane advertised: the
    // heartbeats, shells, and factory groups are empty and stay in
    // the cycle.
    let dock = ActivityDock {
        factory_group: true,
        ..ActivityDock::default()
    };
    assert_eq!(
        dock.groups(),
        vec![
            ActivityGroup::Subagents,
            ActivityGroup::Heartbeats,
            ActivityGroup::Bash,
            ActivityGroup::Factory,
        ]
    );
    // Right: the neighbors in order, the empty groups included,
    // wrapping back to the first.
    assert_eq!(
        dock.step(ActivityGroup::Subagents, ActivityDirection::Next),
        ActivityGroup::Heartbeats
    );
    assert_eq!(
        dock.step(ActivityGroup::Heartbeats, ActivityDirection::Next),
        ActivityGroup::Bash
    );
    assert_eq!(
        dock.step(ActivityGroup::Bash, ActivityDirection::Next),
        ActivityGroup::Factory
    );
    assert_eq!(
        dock.step(ActivityGroup::Factory, ActivityDirection::Next),
        ActivityGroup::Subagents,
        "the cycle wraps past the last group"
    );
    // Left: the same groups in reverse, wrapping past the first.
    assert_eq!(
        dock.step(ActivityGroup::Subagents, ActivityDirection::Prev),
        ActivityGroup::Factory,
        "the cycle wraps past the first group"
    );
    assert_eq!(
        dock.step(ActivityGroup::Factory, ActivityDirection::Prev),
        ActivityGroup::Bash
    );
    assert_eq!(
        dock.step(ActivityGroup::Bash, ActivityDirection::Prev),
        ActivityGroup::Heartbeats
    );
    assert_eq!(
        dock.step(ActivityGroup::Heartbeats, ActivityDirection::Prev),
        ActivityGroup::Subagents
    );
    // The press count is stable in both directions: N groups take
    // exactly N presses to return to the start, and no shorter run
    // does -- the emptiness of a group never moves another.
    for direction in [ActivityDirection::Next, ActivityDirection::Prev] {
        let mut walked = ActivityGroup::Subagents;
        let rendered = dock.groups().len();
        for presses in 1..=rendered {
            walked = dock.step(walked, direction);
            assert_eq!(
                walked == ActivityGroup::Subagents,
                presses == rendered,
                "the cycle length is exactly the rendered group count"
            );
        }
    }
}

/// The same traversal with rows in every group: filling groups
/// changes only the rendered counts, never the group order, the
/// neighbors, or the press count.
#[test]
fn dock_arrows_visit_the_same_groups_with_items() {
    let dock = ActivityDock {
        subagents_running_direct: 1,
        subagents_running_nested: 2,
        heartbeats: 2,
        heartbeats_paused: 1,
        bash_running: 1,
        factory_group: true,
        goal_label: Some("Pursuing goal (0s)".to_string()),
        ..ActivityDock::default()
    };
    assert_eq!(
        dock.groups(),
        vec![
            ActivityGroup::Subagents,
            ActivityGroup::Heartbeats,
            ActivityGroup::Bash,
            ActivityGroup::Factory,
            ActivityGroup::Goal,
        ]
    );
    // The full cycle right: every group in order, the goal group
    // included, back to the start in five presses.
    let mut walked = ActivityGroup::Subagents;
    for expected in [
        ActivityGroup::Heartbeats,
        ActivityGroup::Bash,
        ActivityGroup::Factory,
        ActivityGroup::Goal,
        ActivityGroup::Subagents,
    ] {
        walked = dock.step(walked, ActivityDirection::Next);
        assert_eq!(walked, expected);
    }
    // The full cycle left mirrors it exactly.
    let mut walked = ActivityGroup::Subagents;
    for expected in [
        ActivityGroup::Goal,
        ActivityGroup::Factory,
        ActivityGroup::Bash,
        ActivityGroup::Heartbeats,
        ActivityGroup::Subagents,
    ] {
        walked = dock.step(walked, ActivityDirection::Prev);
        assert_eq!(walked, expected);
    }
}

/// The goal group unmounts with its row (its goal ended): the cycle
/// drops it, and a stale selection on it steps to a group the dock
/// still renders -- never to a hidden segment.
#[test]
fn dock_goal_group_unmounts_with_its_row() {
    let with_goal = ActivityDock {
        goal_label: Some("Goal paused (0s)".to_string()),
        factory_group: true,
        ..ActivityDock::default()
    };
    assert!(with_goal.groups().contains(&ActivityGroup::Goal));
    let ended = ActivityDock {
        factory_group: true,
        ..ActivityDock::default()
    };
    assert!(
        !ended.groups().contains(&ActivityGroup::Goal),
        "the goal group leaves the cycle when its row unmounts"
    );
    assert_eq!(
        ended.step(ActivityGroup::Goal, ActivityDirection::Prev),
        ActivityGroup::Factory,
        "a stale goal selection lands on the row's last group"
    );
    assert_eq!(
        ended.step(ActivityGroup::Goal, ActivityDirection::Next),
        ActivityGroup::Heartbeats,
        "a stale goal selection steps from the row's first group"
    );
}

/// The factory group is the lane's opt-in surface: an unadvertised
/// `factory_activity` lane mounts no factory group -- no traversal (the
/// factory's default-off gate; the factory group exists exactly while
/// the daemon advertises the lane).
#[test]
fn an_unadvertised_factory_lane_mounts_no_factory_group() {
    // The default dock is the unadvertised lane (the opt-in default).
    let dock = ActivityDock::default();
    assert!(
        !dock.groups().contains(&ActivityGroup::Factory),
        "the unadvertised lane stays out of the traversal cycle"
    );
    // The arrows wrap the remaining groups exactly: a stale Factory
    // selection steps to the row's real ends, never a hidden group.
    assert_eq!(
        dock.step(ActivityGroup::Bash, ActivityDirection::Next),
        ActivityGroup::Subagents,
        "the cycle wraps past the shells group"
    );
    assert_eq!(
        dock.step(ActivityGroup::Subagents, ActivityDirection::Prev),
        ActivityGroup::Bash,
        "the reverse cycle wraps past the subagents group"
    );
}

/// The `/speed` footer row (TS `FooterComponent::render`): one dim row
/// with the readout, truncated with no ellipsis when it overflows.
#[test]
fn speed_footer_is_one_dim_row_truncated_to_width() {
    let theme = Theme::builtin("eukhe", ColorMode::TrueColor);
    let row = render_speed_footer("188 tok/s - avg 200", &theme, 100);
    let text = row
        .iter()
        .map(|span| span.content.as_str())
        .collect::<String>();
    assert_eq!(text, "188 tok/s - avg 200");
    assert_eq!(row.len(), 1);
    let narrow = render_speed_footer("188 tok/s - avg 200", &theme, 10);
    let text = narrow
        .iter()
        .map(|span| span.content.as_str())
        .collect::<String>();
    assert_eq!(text.chars().count(), 10);
    assert!(!text.contains("..."));
}

use super::*;
use crate::theme::{ColorMode, Theme};
use serde_json::json;

fn theme() -> Theme {
    Theme::builtin("eukhe", ColorMode::TrueColor)
}

#[test]
fn token_count_formats() {
    assert_eq!(format_token_count(999), "999");
    assert_eq!(format_token_count(6_123), "6.1k");
    assert_eq!(format_token_count(61_234), "61k");
    assert_eq!(format_token_count(1_234_567), "1.2M");
}

#[test]
fn splash_renders_name_version_model_and_cwd() {
    let state = ChromeState {
        version: "0.0.0".to_string(),
        cwd: "/tmp/project".to_string(),
        model_id: Some("faux-1".to_string()),
        ..Default::default()
    };
    let lines = render_splash(&state, &theme(), 120);
    let text = |line: &Line| line.iter().map(|s| s.content.as_str()).collect::<String>();
    assert_eq!(lines.len(), 5);
    assert_eq!(lines[0], Vec::new());
    assert_eq!(text(&lines[1]).trim_end(), " eukhe v0.0.0");
    assert_eq!(text(&lines[2]).trim_end(), " model faux-1");
    assert_eq!(text(&lines[3]).trim_end(), " cwd /tmp/project");
    assert_eq!(str_width(&text(&lines[1])), 119);
    assert_eq!(lines[4], Vec::new());
}

/// TS `getModelContextLabel`: the effort suffix is the state's
/// `thinkingLevel` behind the model's `reasoning` gate -- a level on a
/// reasoning model renders, everything else keeps the bare id.
#[test]
fn effort_suffix_gates_on_model_reasoning() {
    let reasoning = json!({
        "model": { "id": "faux-1", "provider": "faux", "reasoning": true },
        "thinkingLevel": "high",
    });
    assert_eq!(
        tray_thinking_suffix(&reasoning),
        Some("high".to_string()),
        "a reasoning model's session level renders as the suffix"
    );
    let plain = json!({
        "model": { "id": "faux-1", "provider": "faux", "reasoning": false },
        "thinkingLevel": "high",
    });
    assert_eq!(
        tray_thinking_suffix(&plain),
        None,
        "no reasoning, no suffix"
    );
    assert_eq!(
        tray_thinking_suffix(&json!({ "thinkingLevel": "high" })),
        None,
        "no model block, no suffix"
    );
    let unknown = json!({
        "model": { "id": "faux-1", "provider": "faux", "reasoning": true },
        "thinkingLevel": "default",
    });
    assert_eq!(
        tray_thinking_suffix(&unknown),
        None,
        "a level outside the wire vocabulary keeps the bare id"
    );
    let off = json!({
        "model": { "id": "faux-1", "provider": "faux", "reasoning": true },
        "thinkingLevel": "off",
    });
    assert_eq!(
        tray_thinking_suffix(&off),
        Some("off".to_string()),
        "an explicit off renders `model:off` like the TS tray"
    );
}
