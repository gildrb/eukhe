use serde_json::json;

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

fn summary(id: &str, name: &str, parent: &str) -> Value {
    json!({
        "sessionId": id,
        "activeSessionId": format!("{id}-live"),
        "sessionFile": format!("/sessions/{id}.jsonl"),
        "sessionName": name,
        "runtimeKind": "subagent",
        "rlmChildId": format!("sub-{id}"),
        "parentActiveSessionId": format!("{parent}-live"),
        "parentSessionId": parent,
        "parentSessionPath": format!("/sessions/{parent}.jsonl"),
    })
}

/// The lead session `p1` with two children (`worker-1` generating,
/// `worker-2` done) and a grandchild under `worker-1` that shares the
/// name `worker-2`; the roster lists the grandchild before its parent.
fn roster() -> Vec<Value> {
    let mut busy = summary("c1", "worker-1", "p1");
    busy["isStreaming"] = json!(true);
    busy["model"] = json!("elpis/elpis-fast");
    busy["admission"] = json!("generating");
    busy["note"] = json!("wrote the\nparser");
    let mut done = summary("c2", "worker-2", "p1");
    done["taskState"] = json!("completed");
    vec![
        json!({
            "agentId": "p1",
            "status": "idle",
            "summary": {
                "sessionId": "p1",
                "activeSessionId": "p1-live",
                "sessionFile": "/sessions/p1.jsonl",
                "sessionName": "lead",
                "runtimeKind": "top-level",
            },
        }),
        json!({ "agentId": "g1", "status": "idle", "summary": summary("g1", "worker-2", "c1") }),
        json!({ "agentId": "c1", "status": "running", "summary": busy }),
        json!({ "agentId": "c2", "status": "idle", "summary": done }),
    ]
}

fn identity() -> SessionIdentity {
    SessionIdentity::new(
        Some("p1-live".to_string()),
        Some("p1".to_string()),
        Some("/sessions/p1.jsonl".to_string()),
    )
}

#[test]
fn the_family_lists_in_tree_order_with_connectors() {
    let roster = roster();
    let members = family_members(&roster, &identity());
    assert_eq!(
        roster_lines(&members),
        vec![
            RosterLine {
                tree: TREE_MID.to_string(),
                name: "worker-1".to_string(),
                status: "running".to_string(),
                admission: Some(ModelAdmission::Generating),
                depth: 1,
                model: "elpis-fast".to_string(),
                note: Some("wrote the parser".to_string()),
            },
            RosterLine {
                tree: format!("{TREE_PIPE}{TREE_LAST}"),
                name: "worker-2".to_string(),
                status: "idle".to_string(),
                admission: None,
                depth: 2,
                model: "-".to_string(),
                note: None,
            },
            RosterLine {
                tree: TREE_LAST.to_string(),
                name: "worker-2".to_string(),
                status: "done".to_string(),
                admission: None,
                depth: 1,
                model: "-".to_string(),
                note: None,
            },
        ]
    );
}

#[test]
fn tokens_resolve_by_unique_name_id_or_parent_path() {
    let roster = roster();
    let members = family_members(&roster, &identity());
    assert_eq!(
        [
            resolve_agent(&members, "lead", "worker-1"),
            resolve_agent(&members, "lead", "worker-2"),
            resolve_agent(&members, "lead", "lead/worker-2"),
            resolve_agent(&members, "lead", "worker-1/worker-2"),
            resolve_agent(&members, "lead", "sub-c1"),
            resolve_agent(&members, "lead", "c2-live"),
            resolve_agent(&members, "lead", "lead"),
            resolve_agent(&members, "lead", "nobody"),
        ],
        [
            AgentLookup::Found(&roster[2]),
            AgentLookup::Ambiguous(vec![
                "worker-1/worker-2".to_string(),
                "lead/worker-2".to_string(),
            ]),
            AgentLookup::Found(&roster[3]),
            AgentLookup::Found(&roster[1]),
            AgentLookup::Found(&roster[2]),
            AgentLookup::Found(&roster[3]),
            AgentLookup::Unknown,
            AgentLookup::Unknown,
        ]
    );
}

#[test]
fn mentions_offer_each_agent_by_the_handle_that_resolves_it() {
    let roster = roster();
    let members = family_members(&roster, &identity());
    let item = |handle: &str, description: &str| CompletionItem {
        value: format!("@{handle}"),
        label: handle.to_string(),
        description: Some(description.to_string()),
        argument_hint: None,
        source_tag: None,
        path_row: None,
    };
    assert_eq!(
        mention_items(&members, "lead"),
        vec![
            item("worker-1", "agent, running, generating"),
            item("worker-1/worker-2", "agent, idle"),
            item("lead/worker-2", "agent, done"),
        ]
    );
}

#[test]
fn the_roster_renders_aligned_columns() {
    let roster = roster();
    let row = SwarmRow::Roster(roster_lines(&family_members(&roster, &identity())));
    assert_eq!(
        plain(&render_swarm_row(
            &row,
            Detail::Overview,
            &theme(),
            200,
            true
        )),
        vec![
            String::new(),
            " agents: 3 (1 running)".to_string(),
            " |- worker-1     running (generating)  depth 1  elpis-fast  wrote the parser"
                .to_string(),
            " |  `- worker-2  idle                  depth 2  -".to_string(),
            " `- worker-2     done                  depth 1  -".to_string(),
        ]
    );
}

#[test]
fn a_sent_message_echoes_its_target() {
    let row = SwarmRow::Sent {
        to: "worker-1".to_string(),
        text: "check the tests\nthen report".to_string(),
    };
    assert_eq!(
        plain(&render_swarm_row(
            &row,
            Detail::Overview,
            &theme(),
            80,
            false
        )),
        vec![
            " you -> worker-1: check the tests".to_string(),
            "   then report".to_string(),
        ]
    );
}

#[test]
fn a_relay_shows_its_first_line_until_detail_all() {
    let row = SwarmRow::Relay(AgentRelayEvent {
        from: "scout".to_string(),
        to: "builder".to_string(),
        text: "the api is in core\nsee durable/children".to_string(),
    });
    assert_eq!(
        [
            plain(&render_swarm_row(
                &row,
                Detail::Overview,
                &theme(),
                80,
                false
            )),
            plain(&render_swarm_row(
                &row,
                Detail::Details,
                &theme(),
                30,
                false
            )),
            plain(&render_swarm_row(&row, Detail::All, &theme(), 80, false)),
        ],
        [
            vec![" scout -> builder: the api is in core...".to_string()],
            vec![" scout -> builder: the api ...".to_string()],
            vec![
                " scout -> builder: the api is in core".to_string(),
                "   see durable/children".to_string(),
            ],
        ]
    );
}
