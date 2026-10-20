//! The bridge between the workflow limits and admission rule
//! ([`effective_limits`], [`admit`]) and their Bend model
//! (`bend/workflow.bend`, whose laws `laws/workflow.bend` and
//! `PROOF.bend` prove): both run the same random scenarios and must
//! print the same transcript. `bend/bridge_workflow.bend` documents the
//! scenario format.

use eukhe_durable::testing::bridge::{compare, Rng, Scenario};
use eukhe_types::workflow::{WorkflowAgentStatus, WorkflowLimits, WorkflowSize};

use super::globals::{admit, Admission};
use super::meta::WorkflowMeta;
use super::run_doc::{AgentRow, RunRecord};
use super::size::effective_limits;

fn record(max_agents: u32) -> RunRecord {
    RunRecord::start(
        WorkflowMeta {
            name: "bridge".to_owned(),
            description: "bridge".to_owned(),
            phases: Vec::new(),
        },
        WorkflowSize::Small,
        WorkflowLimits {
            concurrency: 1,
            max_agents,
        },
        0.0,
        Some("earlier".to_owned()),
    )
}

fn row(ordinal: u32, key: u64, status: WorkflowAgentStatus) -> AgentRow {
    AgentRow {
        ordinal,
        label: format!("agent {ordinal}"),
        phase: None,
        status,
        key: format!("k{key}"),
        child_name: Some(format!("wf1-{ordinal}")),
        child_session_id: None,
        result: None,
        note: None,
        counted: true,
    }
}

#[test]
fn the_rust_admission_equals_the_bend_model() {
    let mut rng = Rng(0x00f1_0e57);
    let mut scenarios = Vec::new();
    for at in 0..60 {
        let mut events = String::new();
        let mut transcript = String::new();
        for _ in 0..rng.range(1, 4) {
            let size_code = rng.below(3);
            let cap = rng.below(15);
            let size = WorkflowSize::ALL[usize::try_from(size_code).unwrap_or(0)];
            let limits = effective_limits(size, u32::try_from(cap).unwrap_or(u32::MAX));
            events.push_str(&format!("l {size_code} {cap}\n"));
            transcript.push_str(&format!("l {} {}\n", limits.concurrency, limits.max_agents));
        }
        let max_agents = rng.below(6);
        events.push_str(&format!("b {max_agents}\n"));
        let mut run = record(u32::try_from(max_agents).unwrap_or(0));
        let mut earlier = record(25);
        for ordinal in 0..rng.range(0, 5) {
            let key = rng.below(8);
            events.push_str(&format!("c {key}\n"));
            let ordinal = u32::try_from(ordinal).unwrap_or(0) + 1;
            earlier
                .agents
                .insert(ordinal, row(ordinal, key, WorkflowAgentStatus::Done));
        }
        for ordinal in 1..=u32::try_from(rng.range(0, 10)).unwrap_or(0) {
            let key = rng.below(8);
            events.push_str(&format!("g {key}\n"));
            let decided = admit(
                &mut run,
                Some(&earlier),
                ordinal,
                row(ordinal, key, WorkflowAgentStatus::Queued),
            );
            transcript.push_str(match decided {
                Admission::Cached(_) => "g cached\n",
                Admission::Run(_) => "g spawn\n",
                Admission::Exhausted(_) => "g refused\n",
                Admission::Ended(_) => "g ended\n",
            });
        }
        scenarios.push(Scenario {
            name: format!("admission-{at}"),
            events,
            transcript,
        });
    }
    compare("bend/bridge_workflow.bend", scenarios);
}
