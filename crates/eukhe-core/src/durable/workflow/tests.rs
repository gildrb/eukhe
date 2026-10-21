//! The admission rule of `agent()` calls: the budget, reattachment, and
//! the resume cache.

use eukhe_types::workflow::{WorkflowAgentStatus, WorkflowLimits, WorkflowSize};
use serde_json::json;

use super::globals::{admit, resume_key, Admission, Resumed};
use super::meta::WorkflowMeta;
use super::run_doc::{AgentRow, RunRecord};

fn run(max_agents: u32, resume_from: Option<&str>) -> RunRecord {
    RunRecord::start(
        WorkflowMeta {
            name: "t".to_owned(),
            description: "d".to_owned(),
            phases: Vec::new(),
        },
        WorkflowSize::Small,
        WorkflowLimits {
            concurrency: 2,
            max_agents,
        },
        0.0,
        resume_from.map(str::to_owned),
        "1".to_owned(),
    )
}

fn row(ordinal: u32, prompt: &str) -> AgentRow {
    AgentRow {
        ordinal,
        label: prompt.to_owned(),
        phase: None,
        status: WorkflowAgentStatus::Queued,
        key: resume_key(prompt, &json!({}), 0),
        child_name: Some(format!("wf1-{ordinal}")),
        retries: Vec::new(),
        child_session_id: None,
        result: None,
        note: None,
        counted: true,
    }
}

#[test]
fn the_budget_refuses_the_agent_past_max_agents() {
    let mut record = run(2, None);
    assert_eq!(
        admit(&mut record, Resumed::Fresh, 1, row(1, "a")),
        Admission::Run(row(1, "a"))
    );
    assert_eq!(
        admit(&mut record, Resumed::Fresh, 2, row(2, "b")),
        Admission::Run(row(2, "b"))
    );
    assert_eq!(
        admit(&mut record, Resumed::Fresh, 3, row(3, "c")),
        Admission::Exhausted(2)
    );
    // A rerun of an admitted call reattaches to its row.
    assert_eq!(
        admit(&mut record, Resumed::Fresh, 2, row(2, "b")),
        Admission::Run(row(2, "b"))
    );
}

#[test]
fn a_resume_takes_finished_agents_from_the_earlier_run_without_counting_them() {
    let mut earlier = run(2, None);
    let mut done = row(1, "a");
    done.status = WorkflowAgentStatus::Done;
    done.result = Some(json!("answer a"));
    earlier.agents.insert(1, done);
    let mut failed = row(2, "b");
    failed.status = WorkflowAgentStatus::Failed;
    earlier.agents.insert(2, failed);

    let mut record = run(1, Some("1"));
    let cached = AgentRow {
        status: WorkflowAgentStatus::Cached,
        child_name: None,
        result: Some(json!("answer a")),
        counted: false,
        ..row(1, "a")
    };
    assert_eq!(
        admit(&mut record, Resumed::From(&earlier), 1, row(1, "a")),
        Admission::Cached(cached)
    );
    assert_eq!(
        admit(&mut record, Resumed::From(&earlier), 2, row(2, "b")),
        Admission::Run(row(2, "b"))
    );
    assert_eq!(record.spawned(), 1);
}

#[test]
fn the_resume_key_tells_occurrences_and_options_apart() {
    let first = resume_key("p", &json!({"label": "x"}), 0);
    assert_ne!(first, resume_key("p", &json!({"label": "x"}), 1));
    assert_ne!(first, resume_key("p", &json!({"label": "y"}), 0));
    assert_eq!(first, resume_key("p", &json!({"label": "x"}), 0));
}
