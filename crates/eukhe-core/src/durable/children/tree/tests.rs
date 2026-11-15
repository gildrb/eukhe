use eukhe_bend::rules::agent_tree::{Crown, Dir, Info, Lim, Node, Refusal, Status};
use eukhe_types::budget::{BudgetAmounts, BudgetDimension, BudgetLimits, BudgetReport};
use eukhe_types::daemon::agent_tree::{TreePlace, TreeRole};

use super::plan::{bounds, child_allowances, child_limits, hold, mask, refine, rest, size};
use super::{root_place, End, Half, Halves, Local, Slot, SplitRequest};

fn units(paths: &[&str]) -> Vec<String> {
    paths.iter().map(|path| (*path).to_owned()).collect()
}

fn leaf(scope: Vec<bool>, patch: Vec<Option<u64>>) -> Node {
    Node::Leaf(Info {
        status: Status::Running,
        scope,
        limit: Lim::Unlimited,
        spent: 0,
        deadline: Lim::Unlimited,
        patch,
    })
}

#[test]
fn a_new_unit_copies_the_enclosing_units_column() {
    let crown = Crown {
        tree: Node::Split {
            info: Info {
                status: Status::Running,
                scope: vec![true, true],
                limit: Lim::Unlimited,
                spent: 0,
                deadline: Lim::Unlimited,
                patch: vec![None, Some(1)],
            },
            own: vec![true, false],
            left: Box::new(leaf(vec![false, true], Vec::new())),
            right: Box::new(leaf(vec![false, false], Vec::new())),
        },
        helps: Vec::new(),
    };
    let (refined, refined_units) = refine(&crown, &units(&["", "src"]), "src/a");
    assert_eq!(
        (refined, refined_units),
        (
            Crown {
                tree: Node::Split {
                    info: Info {
                        status: Status::Running,
                        scope: vec![true, true, true],
                        limit: Lim::Unlimited,
                        spent: 0,
                        deadline: Lim::Unlimited,
                        patch: vec![None, Some(1), None],
                    },
                    own: vec![true, false, false],
                    left: Box::new(leaf(vec![false, true, true], Vec::new())),
                    right: Box::new(leaf(vec![false, false, false], Vec::new())),
                },
                helps: Vec::new(),
            },
            units(&["", "src", "src/a"]),
        )
    );
}

#[test]
fn a_unit_already_there_and_a_path_outside_every_unit() {
    let crown = Crown::root(vec![true], Lim::Unlimited, Lim::Unlimited);
    assert_eq!(
        [
            refine(&crown, &units(&["src"]), "src"),
            refine(&crown, &units(&["src"]), "docs"),
        ],
        [
            (crown.clone(), units(&["src"])),
            (
                Crown::root(vec![true, false], Lim::Unlimited, Lim::Unlimited),
                units(&["src", "docs"]),
            ),
        ]
    );
}

#[test]
fn a_mask_holds_the_units_inside_the_paths() {
    let all = units(&["", "src", "src/a", "src/ab", "docs"]);
    assert_eq!(
        [
            mask(&all, &units(&["src"])),
            mask(&all, &units(&["src/a", "docs"])),
            mask(&all, &units(&[""])),
        ],
        [
            vec![false, true, true, true, false],
            vec![false, false, true, false, true],
            vec![true; 5],
        ]
    );
    assert_eq!(
        rest(
            &[true, true, true],
            &[true, false, false],
            &[false, true, false]
        ),
        vec![false, false, true]
    );
}

#[test]
fn local_bounds_allowances_and_hold() {
    assert_eq!(
        [
            bounds(0, 15, 0, Lim::Unlimited),
            bounds(2, 7, 4, Lim::Value(10)),
            bounds(4, 1, 0, Lim::Unlimited),
        ],
        [
            eukhe_bend::rules::agent_tree::Bounds {
                max_depth: 3,
                max_nodes: 15,
                margin: 0,
            },
            eukhe_bend::rules::agent_tree::Bounds {
                max_depth: 1,
                max_nodes: 3,
                margin: 120_000,
            },
            eukhe_bend::rules::agent_tree::Bounds {
                max_depth: 0,
                max_nodes: 1,
                margin: 0,
            },
        ]
    );
    assert_eq!(
        [
            child_allowances(15, 1),
            child_allowances(15, 2),
            child_allowances(7, 1),
            child_allowances(3, 1),
        ],
        [(7, 7), (7, 6), (3, 3), (1, 1)]
    );
    assert_eq!(
        [
            hold(Lim::Unlimited, 50),
            hold(Lim::Value(1000), 20),
            hold(Lim::Value(1000), 80),
        ],
        [0, 100, 160]
    );
}

#[test]
fn a_childs_carve_takes_the_same_share_of_every_limited_dimension() {
    let report = BudgetReport {
        limits: BudgetLimits {
            cost_micros: Some(2_000_000),
            tokens: Some(100_000),
            time_ms: Some(600_000),
            ..BudgetLimits::default()
        },
        free: BudgetAmounts {
            cost_micros: 1_000_000,
            tokens: 50_000,
            time_ms: 300_000,
            ..BudgetAmounts::default()
        },
        ..BudgetReport::default()
    };
    assert_eq!(
        child_limits(&report, BudgetDimension::Cost, 400_000, Some(200_000)),
        BudgetLimits {
            cost_micros: Some(400_000),
            tokens: Some(20_000),
            time_ms: Some(200_000),
            ..BudgetLimits::default()
        }
    );
}

fn root(limit: Lim) -> Local {
    let place = TreePlace {
        scope: units(&["src", "docs"]),
        ..root_place()
    };
    Local::open(&place, limit, Some(BudgetDimension::Tokens))
}

fn split(left: &[&str], right: &[&str]) -> SplitRequest {
    SplitRequest {
        left: units(left),
        right: units(right),
        own: None,
        hold: None,
    }
}

#[test]
fn a_split_of_the_root_halves_its_allowance_and_budget() {
    let (after, halves) = root(Lim::Value(1000))
        .split(&split(&["src/a"], &["src/b"]), 50)
        .unwrap();
    assert_eq!(
        halves,
        Halves {
            left: Half {
                scope: units(&["src/a"]),
                mask: vec![false, false, true, false],
                allowance: 7,
                limit: Lim::Value(450),
                deadline: Lim::Unlimited,
            },
            right: Half {
                scope: units(&["src/b"]),
                mask: vec![false, false, false, true],
                allowance: 7,
                limit: Lim::Value(450),
                deadline: Lim::Unlimited,
            },
        }
    );
    assert_eq!(
        (after.units.clone(), after.given, size(&after.crown())),
        (units(&["src", "docs", "src/a", "src/b"]), 12, 3)
    );
    // No room left for a help leaf: the allowance went to the children.
    assert_eq!(after.help(10).map(|_| ()), Err(Refusal::TooMany));
}

#[test]
fn a_split_is_refused_with_its_first_failing_check() {
    let local = root(Lim::Value(1000));
    let (split_once, _) = local.split(&split(&["src"], &["docs"]), 0).unwrap();
    let deep = Local::open(
        &TreePlace {
            role: TreeRole::Left,
            scope: units(&["src"]),
            path: "LLL".to_owned(),
            allowance: 3,
            deadline: None,
        },
        Lim::Unlimited,
        None,
    );
    let small = Local::open(
        &TreePlace {
            allowance: 2,
            ..root_place()
        },
        Lim::Unlimited,
        None,
    );
    let refusals = [
        local.split(&split(&["src"], &["src/a"]), 0).map(|_| ()),
        local.split(&split(&["src"], &["elsewhere"]), 0).map(|_| ()),
        split_once.split(&split(&["src"], &["docs"]), 0).map(|_| ()),
        deep.split(&split(&["src/a"], &["src/b"]), 0).map(|_| ()),
        small.split(&split(&["a"], &["b"]), 0).map(|_| ()),
        local.split(&split(&["src"], &["docs"]), 2000).map(|_| ()),
    ];
    assert_eq!(
        refusals,
        [
            Err(Refusal::BadScopes),
            Err(Refusal::BadScopes),
            Err(Refusal::NotLeaf),
            Err(Refusal::TooDeep),
            Err(Refusal::TooMany),
            Err(Refusal::NoBudget),
        ]
    );
    assert_eq!(
        refusals.map(|refusal| refusal.unwrap_err().text()),
        [
            "own, left and right must split the node's scope exactly, each half non-empty",
            "own, left and right must split the node's scope exactly, each half non-empty",
            "the node has already split",
            "the agent tree is at its depth bound",
            "the agent tree is at its node bound",
            "not enough budget left",
        ]
    );
}

#[test]
fn a_settled_child_returns_what_it_left() {
    let local = root(Lim::Value(1000));
    let (after, _) = local.split(&split(&["src"], &["docs"]), 100).unwrap();
    // The default hold is two worst requests (200): both halves hold
    // their limits (400 each), 200 stays free.
    assert_eq!(after.free(), Lim::Value(200));
    let finished = after.settle(
        Slot::side(Dir::Left),
        200,
        &End::Finished(vec![None, None, Some(1), None]),
    );
    // The left child spent 200 of its 400: the other 200 come back.
    assert_eq!(finished.free(), Lim::Value(400));
    // A child the tree already settled stays as it is.
    assert_eq!(
        finished.settle(Slot::side(Dir::Left), 300, &End::Cancelled),
        finished
    );
}

#[test]
fn a_failed_child_runs_again_once() {
    let (after, _) = root(Lim::Unlimited)
        .split(&split(&["src"], &["docs"]), 0)
        .unwrap();
    let failed = after.settle(Slot::side(Dir::Right), 0, &End::Failed(Vec::new()));
    let redone = failed.redo(Dir::Right, 0).unwrap();
    assert_eq!(
        redone
            .crown()
            .tree
            .at(&[Dir::Right])
            .map(|node| node.info().status),
        Some(Status::Running)
    );
    let failed_again = redone.settle(Slot::side(Dir::Right), 0, &End::Failed(Vec::new()));
    assert_eq!(
        failed_again.redo(Dir::Right, 0).map(|_| ()),
        Err(Refusal::NotRedoable)
    );
}

#[test]
fn a_tick_cancels_the_children_past_their_deadline() {
    let place = TreePlace {
        deadline: Some(1_000_000),
        ..root_place()
    };
    let local = Local::open(&place, Lim::Unlimited, None);
    let (mut after, halves) = local.split(&split(&["a"], &["b"]), 0).unwrap();
    after.left = Some(11);
    after.right = Some(12);
    let (on_time, none) = after.tick(500_000);
    let (late, cancelled) = after.tick(999_000);
    assert_eq!(
        (halves.left.deadline, on_time == after, none, cancelled),
        (Lim::Value(880_000), true, Vec::<u64>::new(), vec![11, 12])
    );
    assert_eq!(
        late.crown()
            .tree
            .at(&[Dir::Left])
            .map(|node| node.info().status),
        Some(Status::Cancelled)
    );
}

#[test]
fn nodes_lent_out_count_until_they_come_back() {
    let local = root(Lim::Unlimited);
    let lent = local.lend("run:1", 10).unwrap();
    assert_eq!(
        (
            lent.remaining(),
            lent.lend("run:1", 10).unwrap() == lent,
            lent.lend("run:2", 5).map(|_| ()),
            lent.take_back("run:1").remaining(),
        ),
        (4, true, Err(Refusal::TooMany), 14)
    );
}
