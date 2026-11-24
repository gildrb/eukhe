//! The admission rule of `agent()` calls (the budget, reattachment, the
//! resume cache) and the agent tree of a workflow: writing batches, their
//! integration, conflicts, and read-only agents.

use eukhe_bend::rules::agent_tree::{Info, Lim, Node, Status};
use eukhe_types::workflow::{WorkflowAgentStatus, WorkflowLimits, WorkflowRunState, WorkflowSize};
use serde_json::json;

use super::batch::{crown, place, plan, wave, Batch, BatchRefusal, LeafPlace, Outcome, Room, Wave};
use super::batch_doc::Batches;
use super::globals::{
    admit, agent_options, resume_key, spawn_kwargs, start_group, Access, Admission, AgentOptions,
    GroupSite, GroupStart, Resumed, Spawn, WorkflowOptionError, Writing,
};
use super::meta::WorkflowMeta;
use super::run_doc::{AgentRow, RunRecord};
use super::run_task::RunReport;
use super::tree::{self, Facts, Written};

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
        path: String::new(),
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
/// units and its scope over them; its tree path runs from the root
/// through its session's node; its budget is its half of the batch's
/// limit, in the session's budget dimension.
#[test]
fn a_writing_leaf_spawns_with_its_place_in_the_batch() {
    let facts = tree::facts(&json!({
        "writeScope": ["crates"],
        "path": "R",
        "depth": 1,
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
                    "path": "RLR",
                    "units": ["crates/a", "crates/b"],
                    "scope": [false, true],
                    "allowance": 1,
                },
                "budget": { "tokens": 450 },
            }),
        )
    );
}

/// The refusals of a writing group: shared files, a path outside the
/// session's scope or one a running batch holds, a path that leaves the
/// workspace.
#[test]
fn a_batch_is_refused_with_the_rules_text() {
    let running = plan(room(), &[String::new()], &[], &writers(&["src/lib.rs"])).expect("plan");
    let refused = [
        wave(
            &room(),
            &[String::new()],
            &[],
            &writers(&["src", "src/lib.rs"]),
        ),
        wave(&room(), &["crates".to_owned()], &[], &writers(&["docs"])),
        wave(&room(), &[String::new()], &[&running], &writers(&["src"])),
        wave(&room(), &[String::new()], &[], &writers(&["../etc"])),
    ]
    .map(|refused| refused.map_err(|refusal| refusal.to_string()));
    assert_eq!(
        refused,
        [
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

/// A writing group wider than the remaining depth holds starts its
/// first wave (the first agents one batch holds) instead of a refusal; a
/// kernel caller's batch, all or none, is still refused.
#[test]
fn a_group_deeper_than_the_room_starts_its_first_wave() {
    let deep = Room { depth: 2, ..room() };
    let first = match wave(&deep, &[String::new()], &[], &writers(&["a", "b", "c"])) {
        Ok(Wave::Batch(batch)) => batch.leaves.iter().map(|leaf| leaf.ordinal).collect(),
        other => panic!("no first wave: {other:?}"),
    };
    assert_eq!(
        (
            first,
            plan(deep, &[String::new()], &[], &writers(&["a", "b", "c"]))
                .map_err(|refusal| refusal.to_string()),
        ),
        (
            vec![1, 2],
            Err("3 writing agents started together need 2 levels below their root; 1 remain here (at most 2 writing agents at once)".to_owned()),
        )
    );
}

/// The run `run_id` "1" of a session at the tree's root with `nodes`
/// nodes free.
fn root_facts(nodes: u64) -> Facts {
    Facts {
        write_scope: vec![String::new()],
        room: Room {
            allowance: nodes,
            ..room()
        },
    }
}

/// Writing agents `ordinals` of prompt `w<ordinal>`, each writing the
/// directory `d<ordinal>`.
fn group(ordinals: std::ops::RangeInclusive<u32>) -> Vec<(AgentRow, Vec<String>)> {
    ordinals
        .map(|ordinal| {
            (
                row(ordinal, &format!("w{ordinal}")),
                vec![format!("d{ordinal}")],
            )
        })
        .collect()
}

fn site<'a>(key: u32, facts: &'a Facts, batches: &'a Batches) -> GroupSite<'a> {
    GroupSite {
        key,
        cache: Resumed::Fresh,
        facts,
        batches,
        writing: Writing::Running,
    }
}

/// The ordinals of `start`'s batch, and its deferred ordinals.
fn started(start: &GroupStart) -> (Vec<u32>, Vec<u32>) {
    match start {
        GroupStart::Wave { batch, deferred } => (
            batch
                .iter()
                .flat_map(|batch| batch.leaves.iter().map(|leaf| leaf.ordinal))
                .collect(),
            deferred.clone(),
        ),
        GroupStart::Refused(reason) => panic!("refused: {reason}"),
    }
}

/// Eight writing agents at the tree's root (four per batch) start in two
/// waves, both at once while the tree has nodes for both; with no node
/// free the rest wait while a writing agent of the run runs, and with
/// none running they are refused and their reserved rows released.
#[test]
fn a_writing_group_past_the_batch_width_starts_in_waves() {
    let record = run(10, None);
    let none = Batches::default();
    let facts = root_facts(14);
    let (record, first) = start_group(&record, &site(1, &facts, &none), group(1..=8));
    assert_eq!(started(&first), (vec![1, 2, 3, 4], vec![5, 6, 7, 8]));
    assert_eq!(
        (
            record.spawned(),
            record
                .agents
                .values()
                .map(|row| (row.ordinal, row.status, row.batch))
                .collect::<Vec<_>>(),
        ),
        (
            8,
            (1..=8)
                .map(|ordinal| (
                    ordinal,
                    WorkflowAgentStatus::Queued,
                    (ordinal < 5).then_some(1)
                ))
                .collect(),
        )
    );
    let GroupStart::Wave {
        batch: Some(wave_one),
        ..
    } = first
    else {
        panic!("no first batch");
    };
    let mut holding = Batches::default();
    holding.batches.insert(tree::lend_key("1", 1), wave_one);
    let left = root_facts(14 - tree::nodes(4));
    let (second_record, second) = start_group(&record, &site(5, &left, &holding), group(5..=8));
    assert_eq!(started(&second), (vec![5, 6, 7, 8], Vec::new()));
    assert_eq!(second_record.spawned(), 8);

    let full = root_facts(0);
    let (waiting, wait) = start_group(&record, &site(5, &full, &holding), group(5..=8));
    assert_eq!(
        (started(&wait), waiting.spawned()),
        ((Vec::new(), vec![5, 6, 7, 8]), 8)
    );
    let idle = GroupSite {
        writing: Writing::Idle,
        ..site(5, &full, &holding)
    };
    let (released, refused) = start_group(&record, &idle, group(5..=8));
    assert_eq!(
        (refused, released.spawned()),
        (
            GroupStart::Refused("the agent tree has no node free for a writing agent".to_owned()),
            4,
        )
    );
}

/// The whole group is checked before its first wave starts: a shared
/// file, a path outside the session or a group past `max_agents` in a
/// later wave refuses the group at once, and no agent of it gets a row.
#[test]
fn a_group_is_refused_whole_before_its_first_wave() {
    let none = Batches::default();
    let facts = root_facts(14);
    let overlapping = {
        let mut agents = group(1..=6);
        agents[5].1 = vec!["d1/inner".to_owned()];
        agents
    };
    let outside = Facts {
        write_scope: (1..=4).map(|ordinal| format!("d{ordinal}")).collect(),
        ..root_facts(14)
    };
    let refusals = [
        start_group(&run(10, None), &site(1, &facts, &none), overlapping),
        start_group(&run(10, None), &site(1, &outside, &none), group(1..=6)),
        start_group(&run(5, None), &site(1, &facts, &none), group(1..=6)),
    ]
    .map(|(record, start)| (record.agents.len(), start));
    assert_eq!(
        refusals,
        [
            (
                0,
                GroupStart::Refused(
                    "the writing agents started together must name disjoint files".to_owned()
                ),
            ),
            (
                0,
                GroupStart::Refused(
                    "d5 lies outside this session's scope (d1, d2, d3, d4)".to_owned()
                ),
            ),
            (
                0,
                GroupStart::Refused(
                    "WorkflowBudgetExhausted: this run may spawn at most 5 agents".to_owned()
                ),
            ),
        ]
    );
}

/// A rerun with `resume` reuses the writing agents of the earlier run
/// that finished, without counting them; its batch holds only the agents
/// the failed run lost.
#[test]
fn a_resumed_group_reuses_the_writers_that_finished() {
    let mut earlier = run(10, None);
    for (ordinal, status) in [
        (1, WorkflowAgentStatus::Done),
        (2, WorkflowAgentStatus::Done),
        (3, WorkflowAgentStatus::Cancelled),
        (4, WorkflowAgentStatus::Cancelled),
    ] {
        let mut finished = row(ordinal, &format!("w{ordinal}"));
        finished.status = status;
        finished.batch = Some(1);
        finished.result = (status == WorkflowAgentStatus::Done)
            .then(|| json!({ "result": "ok", "conflicts": [] }));
        earlier.agents.insert(ordinal, finished);
    }
    let none = Batches::default();
    let facts = root_facts(14);
    let resumed = GroupSite {
        cache: Resumed::From(&earlier),
        ..site(1, &facts, &none)
    };
    let (record, start) = start_group(&run(10, Some("0")), &resumed, group(1..=4));
    assert_eq!(
        (
            started(&start),
            record.spawned(),
            record
                .agents
                .values()
                .map(|row| (row.ordinal, row.status))
                .collect::<Vec<_>>(),
        ),
        (
            (vec![3, 4], Vec::new()),
            2,
            vec![
                (1, WorkflowAgentStatus::Cached),
                (2, WorkflowAgentStatus::Cached),
                (3, WorkflowAgentStatus::Queued),
                (4, WorkflowAgentStatus::Queued),
            ],
        )
    );
}

/// A run's report names why each `null` came back and how to resume the
/// agents that finished, before the script's output.
#[test]
fn the_report_lists_the_problems_and_the_resume() {
    let mut record = run(10, None);
    record.state = WorkflowRunState::Done;
    let mut finished = row(1, "a");
    finished.status = WorkflowAgentStatus::Done;
    record.agents.insert(1, finished);
    record.push_problem("agent 2 (b) failed: the agent ended failed".to_owned());
    record.push_problem(
        "parallel slot 2: WorkflowBudgetExhausted: this run may spawn at most 2 agents".to_owned(),
    );
    record.push_problem("agent 2 (b) failed: the agent ended failed".to_owned());
    assert_eq!(
        RunReport::ended("7", &record, "Output:\n[\"x\",null,null]").body,
        "workflow run 7 (t): done\nProblems (why results are null):\n- agent 2 (b) failed: the agent ended failed\n- parallel slot 2: WorkflowBudgetExhausted: this run may spawn at most 2 agents\nA rerun with resume: \"7\" reuses the 1 agents that finished.\nOutput:\n[\"x\",null,null]"
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
