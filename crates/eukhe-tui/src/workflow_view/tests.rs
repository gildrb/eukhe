use eukhe_types::workflow::{
    WorkflowAgent, WorkflowAgentStatus, WorkflowPhase, WorkflowPhaseState, WorkflowRunSnapshot,
    WorkflowRunState, WorkflowSize,
};
use serde_json::json;

use super::*;
use crate::theme::{ColorMode, Theme};

fn kb() -> KeybindingsManager {
    KeybindingsManager::new()
}

fn agent(ordinal: u32, label: &str, phase: &str, status: WorkflowAgentStatus) -> WorkflowAgent {
    WorkflowAgent {
        ordinal,
        label: label.to_owned(),
        phase: Some(phase.to_owned()),
        status,
        child_session_id: None,
        note: None,
    }
}

fn run() -> WorkflowRunSnapshot {
    WorkflowRunSnapshot {
        run_id: "14".to_owned(),
        session_id: "s".to_owned(),
        name: "review".to_owned(),
        description: "Review the repo".to_owned(),
        size: WorkflowSize::Medium,
        state: WorkflowRunState::Running,
        phases: vec![
            WorkflowPhase {
                title: "Scan".to_owned(),
                state: WorkflowPhaseState::Done,
            },
            WorkflowPhase {
                title: "Fix".to_owned(),
                state: WorkflowPhaseState::Active,
            },
        ],
        agents: vec![
            WorkflowAgent {
                note: Some("found 2 bugs".to_owned()),
                ..agent(1, "scan api", "Scan", WorkflowAgentStatus::Done)
            },
            agent(2, "fix api", "Fix", WorkflowAgentStatus::Running),
        ],
        spawned: 2,
        done: 1,
        failed: 0,
        max_agents: 10,
        concurrency: 6,
        logs: vec!["phase: Fix".to_owned()],
    }
}

fn text(view: &WorkflowView) -> Vec<String> {
    let theme = Theme::builtin("eukhe", ColorMode::TrueColor);
    view.render(&theme, 100, &kb())
        .iter()
        .map(|line| line.iter().map(|span| span.content.as_str()).collect())
        .collect()
}

#[test]
fn a_run_renders_its_phases_agents_and_log() {
    let view = WorkflowView::new(vec![run()], 40);
    assert_eq!(
        text(&view),
        vec![
            "  Workflows",
            "",
            "  review  medium | 2/10 agents | 1 running | 1 done | 0 failed | running",
            "  run 14  Review the repo",
            "  ✓ Scan",
            "    › ✓ scan api  found 2 bugs",
            "  ▶ Fix",
            "      ▶ fix api",
            "    log: phase: Fix",
            "",
            "  up/down move - Enter agents view - c cancel run - Esc close",
        ]
    );
}

#[test]
fn the_arrows_walk_the_agents_and_c_then_y_cancels() {
    let mut view = WorkflowView::new(vec![run()], 40);
    assert_eq!(view.handle_key("down", &kb()), WorkflowViewAction::None);
    assert!(text(&view).contains(&"    › ▶ fix api".to_owned()));
    assert_eq!(
        view.handle_key("enter", &kb()),
        WorkflowViewAction::OpenAgents
    );
    assert_eq!(view.handle_key("c", &kb()), WorkflowViewAction::None);
    assert!(text(&view)
        .iter()
        .any(|row| row.contains("Cancel this run")));
    assert_eq!(
        view.handle_key("y", &kb()),
        WorkflowViewAction::Cancel {
            run_id: "14".to_owned()
        }
    );
    assert_eq!(view.handle_key("escape", &kb()), WorkflowViewAction::Close);
}

#[test]
fn the_reply_parses_and_counts_running_runs() {
    let runs = parse_workflow_runs(&json!({ "runs": [serde_json::to_value(run()).unwrap()] }))
        .expect("runs list");
    assert_eq!(runs, vec![run()]);
    assert_eq!(running_runs(&runs), 1);
    assert_eq!(parse_workflow_runs(&json!({})), None);
}
