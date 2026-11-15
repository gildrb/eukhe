//! The admission rule of `agent()` calls (the budget, reattachment, the
//! resume cache) and the agent tree of a workflow: writing batches, their
//! integration, conflicts, and read-only agents.

use eukhe_bend::rules::agent_tree::{Info, Lim, Node, Status};
use eukhe_types::workflow::{WorkflowAgentStatus, WorkflowLimits, WorkflowSize};
use serde_json::json;

use super::batch::{crown, place, plan, Batch, BatchRefusal, LeafPlace, Outcome, Room};
use super::globals::{
    admit, agent_options, resume_key, spawn_kwargs, Access, Admission, AgentOptions, Resumed,
    Spawn, WorkflowOptionError,
};
use super::meta::WorkflowMeta;
use super::run_doc::{AgentRow, RunRecord};
use super::tree::{self, Written};

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
        batch: None,
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

/// The room of a batch under a session at depth 0 with the root's
/// allowance, limits off.
fn room() -> Room {
    Room {
        depth: 1,
        allowance: 15,
        limit: None,
        deadline: None,
    }
}

fn writers(scopes: &[&str]) -> Vec<(u32, Vec<String>)> {
    (1..)
        .zip(scopes)
        .map(|(ordinal, scope)| (ordinal, vec![(*scope).to_owned()]))
        .collect()
}

fn info(status: Status, scope: [bool; 4], patch: Vec<Option<u64>>) -> Info {
    Info {
        status,
        scope: scope.to_vec(),
        limit: Lim::Unlimited,
        spent: 0,
        deadline: Lim::Unlimited,
        patch,
    }
}

fn leaf(unit: usize) -> Box<Node> {
    Box::new(Node::Leaf(info(
        Status::Running,
        std::array::from_fn(|at| at == unit),
        Vec::new(),
    )))
}

fn split(scope: [bool; 4], left: Box<Node>, right: Box<Node>) -> Node {
    Node::Split {
        info: info(Status::Running, scope, Vec::new()),
        own: vec![false; 4],
        left,
        right,
    }
}

/// A patch over four units writing `units`.
fn wrote(units: &[usize]) -> Vec<Option<u64>> {
    (0..4)
        .map(|unit| units.contains(&unit).then_some(1))
        .collect()
}

/// Four writing agents become a depth-2 balanced tree: the root and two
/// integrators over the four leaves in call order; once all four end,
/// the root's integrated patch holds every scope.
#[test]
fn a_batch_of_four_builds_a_balanced_tree_and_integrates_every_scope() {
    let batch = plan(
        room(),
        &[String::new()],
        &[],
        &writers(&["a", "b", "c", "d"]),
    )
    .expect("plan");
    assert_eq!(
        (
            batch
                .leaves
                .iter()
                .map(|leaf| leaf.path.as_str())
                .collect::<Vec<_>>(),
            crown(&batch).expect("crown").tree,
        ),
        (
            vec!["LL", "LR", "RL", "RR"],
            split(
                [true; 4],
                Box::new(split([true, true, false, false], leaf(0), leaf(1))),
                Box::new(split([false, false, true, true], leaf(2), leaf(3))),
            ),
        )
    );
    let ended = [(1, 0), (2, 1), (3, 2), (4, 3)]
        .into_iter()
        .fold(batch, |batch: Batch, (ordinal, unit)| {
            batch.ended(ordinal, Outcome::Finished, wrote(&[unit]))
        });
    assert_eq!(
        (
            ended.settled(),
            crown(&ended).expect("crown").tree.info().clone()
        ),
        (
            true,
            info(Status::Finished, [true; 4], wrote(&[0, 1, 2, 3]))
        ),
    );
}

/// An agent that writes outside its scope gets those paths back as
/// conflicts, and the batch's integration leaves them out.
#[test]
fn a_write_outside_the_scope_returns_as_a_conflict() {
    let state = json!({
        "settled": true,
        "status": "done",
        "answer": "done",
        "scopedHandback": {
            "taken": ["a/x.rs"],
            "outside": ["c/y.rs"],
            "conflicts": [],
            "patch": [1, null, 1, null],
        },
    });
    let written = tree::written(&state);
    assert_eq!(
        written,
        Written {
            patch: wrote(&[0, 2]),
            conflicts: vec!["c/y.rs".to_owned()],
        }
    );
    let batch = plan(
        room(),
        &[String::new()],
        &[],
        &writers(&["a", "b", "c", "d"]),
    )
    .expect("plan")
    .ended(1, Outcome::Finished, written.patch_over(4))
    .ended(2, Outcome::Finished, wrote(&[1]))
    .ended(3, Outcome::Failed, Vec::new())
    .ended(4, Outcome::Finished, wrote(&[3]));
    assert_eq!(
        crown(&batch).expect("crown").tree.info().patch,
        wrote(&[0, 1, 3])
    );
}

/// An agent without a scope is a read-only help leaf: its spawn names no
/// node of a writing tree, so the session's tree gives it no write scope.
/// A scope that names no file is refused.
#[test]
fn an_agent_without_a_scope_is_a_read_only_help_leaf() {
    let options = agent_options(&json!({ "label": "look" })).expect("options");
    assert_eq!(
        (
            options.clone(),
            spawn_kwargs("wf1-1", &options, &Spawn::Help),
            agent_options(&json!({ "scope": [] })),
        ),
        (
            AgentOptions {
                label: Some("look".to_owned()),
                phase: None,
                schema: None,
                model: None,
                thinking: None,
                access: Access::ReadOnly,
            },
            json!({
                "name": "wf1-1",
                "label": "look",
                "phase": null,
                "model": null,
                "thinking": null,
                "report": "silent",
            }),
            Err(WorkflowOptionError::NoScope),
        )
    );
    assert_eq!(
        WorkflowOptionError::NoScope.to_string(),
        "a writing agent needs its files"
    );
}

/// A writing leaf spawns as a node of its batch's crown: role, path,
/// units and its scope over them; its budget is its half of the batch's
/// limit, in the session's budget dimension.
#[test]
fn a_writing_leaf_spawns_with_its_place_in_the_batch() {
    let facts = tree::facts(&json!({
        "writeScope": ["crates"],
        "depth": 0,
        "remaining": 15,
        "free": { "budget": { "tokens": 1000 } },
        "deadlineMs": null,
    }))
    .expect("facts");
    let batch = plan(
        facts.room.clone(),
        &facts.write_scope,
        &[],
        &writers(&["crates/a", "crates/b"]),
    )
    .expect("plan");
    let crowned = crown(&batch).expect("crown");
    let right = place(&batch, &crowned, 2).expect("place");
    let options = AgentOptions {
        label: None,
        phase: None,
        schema: None,
        model: None,
        thinking: None,
        access: Access::Writes(vec!["crates/b".to_owned()]),
    };
    let spawn = Spawn::Leaf {
        batch: tree::lend_key("wf1", 1),
        units: 2,
        kwargs: tree::leaf_kwargs(&batch, &right),
    };
    assert_eq!(
        (
            facts.room.limit.map(|limit| limit.amount),
            right,
            spawn_kwargs("wf1-2", &options, &spawn)
        ),
        (
            Some(900),
            LeafPlace {
                path: "R".to_owned(),
                mask: vec![false, true],
                limit: Lim::Value(450),
                deadline: Lim::Unlimited,
            },
            json!({
                "name": "wf1-2",
                "label": null,
                "phase": null,
                "model": null,
                "thinking": null,
                "report": "silent",
                "node": {
                    "role": "right",
                    "path": "R",
                    "units": ["crates/a", "crates/b"],
                    "scope": [false, true],
                    "allowance": 1,
                },
                "budget": { "tokens": 450 },
            }),
        )
    );
}

/// The refusals of a batch: more agents than the remaining depth holds,
/// shared files, a path outside the session's scope or one a running
/// batch holds, a path that leaves the workspace.
#[test]
fn a_batch_is_refused_with_the_rules_text() {
    let deep = Room { depth: 2, ..room() };
    let running = plan(room(), &[String::new()], &[], &writers(&["src/lib.rs"])).expect("plan");
    let refused = [
        plan(deep, &[String::new()], &[], &writers(&["a", "b", "c"])),
        plan(
            room(),
            &[String::new()],
            &[],
            &writers(&["src", "src/lib.rs"]),
        ),
        plan(room(), &["crates".to_owned()], &[], &writers(&["docs"])),
        plan(room(), &[String::new()], &[&running], &writers(&["src"])),
        plan(room(), &[String::new()], &[], &writers(&["../etc"])),
    ]
    .map(|refused| refused.map_err(|refusal| refusal.to_string()));
    assert_eq!(
        refused,
        [
            Err("3 writing agents started together need 2 levels below their root; 1 remain here (at most 2 writing agents at once)".to_owned()),
            Err("the writing agents started together must name disjoint files".to_owned()),
            Err("docs lies outside this session's scope (crates)".to_owned()),
            Err("src belongs to a running writing batch of this workflow (agents 1)".to_owned()),
            Err("agent(prompt, opts): scope paths are relative paths inside the workspace, not ../etc".to_owned()),
        ]
    );
    assert_eq!(
        BatchRefusal::NoScope.to_string(),
        "a writing agent needs its files"
    );
}

/// One writing agent alone is the batch's root: no integrator.
#[test]
fn a_single_writing_agent_is_the_batch_root() {
    let batch = plan(room(), &[String::new()], &[], &writers(&["a"])).expect("plan");
    let crowned = crown(&batch).expect("crown");
    assert_eq!(
        (
            crowned.tree,
            place(&batch, &crown(&batch).expect("crown"), 1)
        ),
        (
            Node::Leaf(Info {
                status: Status::Running,
                scope: vec![true],
                limit: Lim::Unlimited,
                spent: 0,
                deadline: Lim::Unlimited,
                patch: Vec::new(),
            }),
            Some(LeafPlace {
                path: String::new(),
                mask: vec![true],
                limit: Lim::Unlimited,
                deadline: Lim::Unlimited,
            }),
        )
    );
}
