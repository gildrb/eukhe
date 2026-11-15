//! The agent tree (`bend/agent_tree.bend`, entry `bend/ffi_agent_tree.bend`;
//! laws `laws/agent_tree.bend`, spec `spec/agents/agent_tree.bend`, design
//! `docs/internals/agent-tree.md`): every agent is a node that works alone
//! or splits into exactly two children with disjoint scopes. The core
//! decides each event (`step`), integrates a child's patch (`overlay`),
//! names a node's next action (`next`) and what it may still spend
//! (`free`). Rust keeps the tree between calls and maps paths to units.

use crate::wire::{Reader, WireError, Writer, NAT_MAX};
use crate::{call, expect_core, Entry, Error};

/// An amount or a deadline: none, or a value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Lim {
    Unlimited,
    Value(u64),
}

/// A node's life: running, or settled one of three ways.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Status {
    Running,
    Finished,
    Failed,
    Cancelled,
}

impl Status {
    #[must_use]
    pub fn is_running(self) -> bool {
        match self {
            Status::Running => true,
            Status::Finished | Status::Failed | Status::Cancelled => false,
        }
    }
}

/// A step from a split to one of its children.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Dir {
    Left,
    Right,
}

/// A mask over the units: `true` = owned.
pub type Scope = Vec<bool>;

/// Per unit: `Some(v)` = the unit's new version `v`, `None` = untouched.
pub type Patch = Vec<Option<u64>>;

/// What every node carries.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Info {
    pub status: Status,
    pub scope: Scope,
    pub limit: Lim,
    pub spent: u64,
    pub deadline: Lim,
    /// A leaf: its work; a split: its own work and integration fixes.
    pub patch: Patch,
}

/// A node of the tree.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Node {
    Leaf(Info),
    Split {
        info: Info,
        /// The part of the scope the split keeps for itself.
        own: Scope,
        left: Box<Node>,
        right: Box<Node>,
    },
}

impl Node {
    /// The root: a running leaf over `scope`, nothing spent.
    #[must_use]
    pub fn root(scope: Scope, limit: Lim, deadline: Lim) -> Node {
        Node::Leaf(Info {
            status: Status::Running,
            scope,
            limit,
            spent: 0,
            deadline,
            patch: Vec::new(),
        })
    }

    #[must_use]
    pub fn info(&self) -> &Info {
        match self {
            Node::Leaf(info) | Node::Split { info, .. } => info,
        }
    }

    /// The node at `path`, if any.
    #[must_use]
    pub fn at(&self, path: &[Dir]) -> Option<&Node> {
        match (path.split_first(), self) {
            (None, node) => Some(node),
            (Some(_), Node::Leaf(_)) => None,
            (Some((Dir::Left, rest)), Node::Split { left, .. }) => left.at(rest),
            (Some((Dir::Right, rest)), Node::Split { right, .. }) => right.at(rest),
        }
    }
}

/// The configured bounds: depth, node count, and the time a child's
/// deadline keeps before its parent's (for the parent to integrate).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Bounds {
    pub max_depth: u64,
    pub max_nodes: u64,
    pub margin: u64,
}

/// An event, addressed by the path from the root to its node.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Event {
    Split {
        at: Vec<Dir>,
        own: Scope,
        left: Scope,
        right: Scope,
        hold: u64,
    },
    Spend {
        at: Vec<Dir>,
        amount: u64,
    },
    Finish {
        at: Vec<Dir>,
        patch: Patch,
    },
    Fail {
        at: Vec<Dir>,
        patch: Patch,
    },
    Cancel {
        at: Vec<Dir>,
    },
    Redo {
        at: Vec<Dir>,
        side: Dir,
        extra: u64,
    },
    Tick {
        now: u64,
    },
}

/// Why the core refused an event: its first failing check.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Refusal {
    NoNode,
    NotRunning,
    NotLeaf,
    TooDeep,
    TooMany,
    BadScopes,
    NoBudget,
    Unsettled,
    NotRedoable,
}

impl Refusal {
    /// The text a refused tool call shows.
    #[must_use]
    pub fn text(self) -> &'static str {
        match self {
            Refusal::NoNode => "no such node in the agent tree",
            Refusal::NotRunning => "the node has settled",
            Refusal::NotLeaf => "the node has already split",
            Refusal::TooDeep => "the agent tree is at its depth bound",
            Refusal::TooMany => "the agent tree is at its node bound",
            Refusal::BadScopes => {
                "own, left and right must split the node's scope exactly, each half non-empty"
            }
            Refusal::NoBudget => "not enough budget left",
            Refusal::Unsettled => "a child is still running",
            Refusal::NotRedoable => "only a failed or cancelled leaf child can run again",
        }
    }
}

/// What a node sees when it picks its next action.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct View {
    /// A user message waits.
    pub message: bool,
    /// Children's results arrived and not yet integrated.
    pub arrived: u64,
    /// Work is left in the node's own scope.
    pub own_work: bool,
}

/// A node's next action, first that applies.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Action {
    ReadMessage,
    Integrate,
    WorkOwn,
    Wait,
}

/// A read-only help leaf of a node: no write scope; it counts in the node
/// bound, takes its limit from the node's free and is cancelled with the
/// node's subtree.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Help {
    /// The path of the node the leaf helps.
    pub at: Vec<Dir>,
    pub status: Status,
    pub limit: Lim,
    pub spent: u64,
    pub deadline: Lim,
}

/// The tree of writers and every help leaf admitted, in order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Crown {
    pub tree: Node,
    pub helps: Vec<Help>,
}

impl Crown {
    /// The root alone: a running leaf over `scope`, no help leaf.
    #[must_use]
    pub fn root(scope: Scope, limit: Lim, deadline: Lim) -> Crown {
        Crown {
            tree: Node::root(scope, limit, deadline),
            helps: Vec::new(),
        }
    }
}

/// An event of the crown.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CrownEvent {
    /// An event of the tree of writers.
    Tree(Event),
    /// The running node at `at` asks a help leaf with limit `amount`.
    Help { at: Vec<Dir>, amount: u64 },
    /// Help leaf `index` spends `amount`.
    HelpSpend { index: usize, amount: u64 },
    /// Help leaf `index` settles: finished or failed.
    HelpEnd { index: usize, outcome: HelpOutcome },
}

/// How a help leaf settled.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HelpOutcome {
    Finished,
    Failed,
}

/// A child's patch integrated into its parent's.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Overlay {
    /// The parent's patch with the child's writes inside its scope.
    pub patch: Patch,
    /// The units the child wrote outside its scope (never applied).
    pub conflicts: Scope,
}

/// The decision on `event`: the new crown, or the refusal (the crown stays).
///
/// # Errors
///
/// The refusal: why the event cannot happen on this crown.
pub fn step(bounds: Bounds, crown: &Crown, event: &CrownEvent) -> Result<Crown, Refusal> {
    expect_core(Entry::AgentTree, step_call(bounds, crown, event))
}

/// The child's patch `child` integrated into `cur` by the child's `scope`.
#[must_use]
pub fn overlay(cur: &[Option<u64>], child: &[Option<u64>], scope: &[bool]) -> Overlay {
    expect_core(Entry::AgentTree, overlay_call(cur, child, scope))
}

/// The node's next action.
#[must_use]
pub fn next(view: View) -> Action {
    expect_core(Entry::AgentTree, next_call(view))
}

/// What the node at `at` may still spend or give (help leaves' charges
/// counted); `None` when no node is there.
#[must_use]
pub fn free(crown: &Crown, at: &[Dir]) -> Option<Lim> {
    expect_core(Entry::AgentTree, free_call(crown, at))
}

fn step_call(
    bounds: Bounds,
    crown: &Crown,
    event: &CrownEvent,
) -> Result<Result<Crown, Refusal>, Error> {
    let mut request = Writer::new();
    request
        .tag(0)
        .nat(bounds.max_depth)
        .nat(bounds.max_nodes)
        .nat(bounds.margin);
    put_crown(&mut request, crown);
    put_crown_event(&mut request, event);
    let reply = call(Entry::AgentTree, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let decided = match reader.tag_of(2, "an agent tree step")? {
        0 => Ok(get_crown(&mut reader)?),
        _ => Err(get_refusal(&mut reader)?),
    };
    reader.end()?;
    Ok(decided)
}

fn overlay_call(
    cur: &[Option<u64>],
    child: &[Option<u64>],
    scope: &[bool],
) -> Result<Overlay, Error> {
    let mut request = Writer::new();
    request.tag(1);
    put_patch(&mut request, cur);
    put_patch(&mut request, child);
    put_scope(&mut request, scope);
    let reply = call(Entry::AgentTree, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let overlay = Overlay {
        patch: get_patch(&mut reader)?,
        conflicts: get_scope(&mut reader)?,
    };
    reader.end()?;
    Ok(overlay)
}

fn next_call(view: View) -> Result<Action, Error> {
    let mut request = Writer::new();
    request
        .tag(2)
        .bool(view.message)
        .nat(view.arrived.min(NAT_MAX))
        .bool(view.own_work);
    let reply = call(Entry::AgentTree, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let action = match reader.tag_of(4, "an agent tree action")? {
        0 => Action::ReadMessage,
        1 => Action::Integrate,
        2 => Action::WorkOwn,
        _ => Action::Wait,
    };
    reader.end()?;
    Ok(action)
}

fn free_call(crown: &Crown, at: &[Dir]) -> Result<Option<Lim>, Error> {
    let mut request = Writer::new();
    request.tag(3);
    put_crown(&mut request, crown);
    put_path(&mut request, at);
    let reply = call(Entry::AgentTree, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let lim = if reader.maybe()? {
        Some(get_lim(&mut reader)?)
    } else {
        None
    };
    reader.end()?;
    Ok(lim)
}

// Encoders: numbers past the wire's largest Nat saturate (a limit, a
// spend or a time that large is out of reach either way).

fn put_lim(w: &mut Writer, lim: Lim) {
    match lim {
        Lim::Unlimited => w.tag(0),
        Lim::Value(n) => w.tag(1).nat(n.min(NAT_MAX)),
    };
}

fn put_status(w: &mut Writer, status: Status) {
    w.tag(match status {
        Status::Running => 0,
        Status::Finished => 1,
        Status::Failed => 2,
        Status::Cancelled => 3,
    });
}

fn put_dir(w: &mut Writer, dir: Dir) {
    w.tag(match dir {
        Dir::Left => 0,
        Dir::Right => 1,
    });
}

fn put_path(w: &mut Writer, path: &[Dir]) {
    w.count(path.len());
    for dir in path {
        put_dir(w, *dir);
    }
}

fn put_scope(w: &mut Writer, scope: &[bool]) {
    w.count(scope.len());
    for unit in scope {
        w.bool(*unit);
    }
}

fn put_patch(w: &mut Writer, patch: &[Option<u64>]) {
    w.count(patch.len());
    for unit in patch {
        match unit {
            None => {
                w.none();
            }
            Some(v) => {
                w.some().nat((*v).min(NAT_MAX));
            }
        }
    }
}

fn put_info(w: &mut Writer, info: &Info) {
    put_status(w, info.status);
    put_scope(w, &info.scope);
    put_lim(w, info.limit);
    w.nat(info.spent.min(NAT_MAX));
    put_lim(w, info.deadline);
    put_patch(w, &info.patch);
}

fn put_node(w: &mut Writer, node: &Node) {
    match node {
        Node::Leaf(info) => {
            w.tag(0);
            put_info(w, info);
        }
        Node::Split {
            info,
            own,
            left,
            right,
        } => {
            w.tag(1);
            put_info(w, info);
            put_scope(w, own);
            put_node(w, left);
            put_node(w, right);
        }
    }
}

fn put_event(w: &mut Writer, event: &Event) {
    match event {
        Event::Split {
            at,
            own,
            left,
            right,
            hold,
        } => {
            w.tag(0);
            put_path(w, at);
            put_scope(w, own);
            put_scope(w, left);
            put_scope(w, right);
            w.nat((*hold).min(NAT_MAX));
        }
        Event::Spend { at, amount } => {
            w.tag(1);
            put_path(w, at);
            w.nat((*amount).min(NAT_MAX));
        }
        Event::Finish { at, patch } => {
            w.tag(2);
            put_path(w, at);
            put_patch(w, patch);
        }
        Event::Fail { at, patch } => {
            w.tag(3);
            put_path(w, at);
            put_patch(w, patch);
        }
        Event::Cancel { at } => {
            w.tag(4);
            put_path(w, at);
        }
        Event::Redo { at, side, extra } => {
            w.tag(5);
            put_path(w, at);
            put_dir(w, *side);
            w.nat((*extra).min(NAT_MAX));
        }
        Event::Tick { now } => {
            w.tag(6).nat((*now).min(NAT_MAX));
        }
    }
}

fn put_help(w: &mut Writer, help: &Help) {
    put_path(w, &help.at);
    put_status(w, help.status);
    put_lim(w, help.limit);
    w.nat(help.spent.min(NAT_MAX));
    put_lim(w, help.deadline);
}

fn put_crown(w: &mut Writer, crown: &Crown) {
    put_node(w, &crown.tree);
    w.count(crown.helps.len());
    crown.helps.iter().for_each(|help| put_help(w, help));
}

fn put_crown_event(w: &mut Writer, event: &CrownEvent) {
    match event {
        CrownEvent::Tree(event) => {
            w.tag(0);
            put_event(w, event);
        }
        CrownEvent::Help { at, amount } => {
            w.tag(1);
            put_path(w, at);
            w.nat((*amount).min(NAT_MAX));
        }
        CrownEvent::HelpSpend { index, amount } => {
            w.tag(2).count(*index).nat((*amount).min(NAT_MAX));
        }
        CrownEvent::HelpEnd { index, outcome } => {
            w.tag(3).count(*index).bool(match outcome {
                HelpOutcome::Finished => true,
                HelpOutcome::Failed => false,
            });
        }
    }
}

// Decoders

fn get_lim(r: &mut Reader<'_>) -> Result<Lim, WireError> {
    Ok(match r.tag_of(2, "a limit")? {
        0 => Lim::Unlimited,
        _ => Lim::Value(r.nat()?),
    })
}

fn get_status(r: &mut Reader<'_>) -> Result<Status, WireError> {
    Ok(match r.tag_of(4, "a node status")? {
        0 => Status::Running,
        1 => Status::Finished,
        2 => Status::Failed,
        _ => Status::Cancelled,
    })
}

fn get_dir(r: &mut Reader<'_>) -> Result<Dir, WireError> {
    Ok(match r.tag_of(2, "a direction")? {
        0 => Dir::Left,
        _ => Dir::Right,
    })
}

fn get_path(r: &mut Reader<'_>) -> Result<Vec<Dir>, WireError> {
    let n = r.count()?;
    (0..n).map(|_| get_dir(r)).collect()
}

fn get_help(r: &mut Reader<'_>) -> Result<Help, WireError> {
    Ok(Help {
        at: get_path(r)?,
        status: get_status(r)?,
        limit: get_lim(r)?,
        spent: r.nat()?,
        deadline: get_lim(r)?,
    })
}

fn get_crown(r: &mut Reader<'_>) -> Result<Crown, WireError> {
    let tree = get_node(r)?;
    let n = r.count()?;
    let helps = (0..n).map(|_| get_help(r)).collect::<Result<_, _>>()?;
    Ok(Crown { tree, helps })
}

fn get_scope(r: &mut Reader<'_>) -> Result<Scope, WireError> {
    let n = r.count()?;
    (0..n).map(|_| r.bool()).collect()
}

fn get_patch(r: &mut Reader<'_>) -> Result<Patch, WireError> {
    let n = r.count()?;
    (0..n)
        .map(|_| {
            if r.maybe()? {
                r.nat().map(Some)
            } else {
                Ok(None)
            }
        })
        .collect()
}

fn get_info(r: &mut Reader<'_>) -> Result<Info, WireError> {
    Ok(Info {
        status: get_status(r)?,
        scope: get_scope(r)?,
        limit: get_lim(r)?,
        spent: r.nat()?,
        deadline: get_lim(r)?,
        patch: get_patch(r)?,
    })
}

fn get_node(r: &mut Reader<'_>) -> Result<Node, WireError> {
    Ok(match r.tag_of(2, "an agent tree node")? {
        0 => Node::Leaf(get_info(r)?),
        _ => Node::Split {
            info: get_info(r)?,
            own: get_scope(r)?,
            left: Box::new(get_node(r)?),
            right: Box::new(get_node(r)?),
        },
    })
}

fn get_refusal(r: &mut Reader<'_>) -> Result<Refusal, WireError> {
    Ok(match r.tag_of(9, "an agent tree refusal")? {
        0 => Refusal::NoNode,
        1 => Refusal::NotRunning,
        2 => Refusal::NotLeaf,
        3 => Refusal::TooDeep,
        4 => Refusal::TooMany,
        5 => Refusal::BadScopes,
        6 => Refusal::NoBudget,
        7 => Refusal::Unsettled,
        _ => Refusal::NotRedoable,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const BOUNDS: Bounds = Bounds {
        max_depth: 3,
        max_nodes: 15,
        margin: 120_000,
    };

    fn split(at: Vec<Dir>, own: Scope, left: Scope, right: Scope, hold: u64) -> CrownEvent {
        CrownEvent::Tree(Event::Split {
            at,
            own,
            left,
            right,
            hold,
        })
    }

    /// A root over three units splits: own keeps unit 0, the halves of
    /// (100 - 10) go to the children, deadlines keep the margin; the crown
    /// round-trips through the core whole.
    #[test]
    fn a_split_gives_each_child_half_the_room() {
        let root = Crown::root(vec![true; 3], Lim::Value(100), Lim::Value(1_000_000));
        let child = |unit: usize, limit| {
            Box::new(Node::Leaf(Info {
                status: Status::Running,
                scope: (0..3).map(|u| u == unit).collect(),
                limit: Lim::Value(limit),
                spent: 0,
                deadline: Lim::Value(880_000),
                patch: Vec::new(),
            }))
        };
        assert_eq!(
            step(
                BOUNDS,
                &root,
                &split(
                    vec![],
                    vec![true, false, false],
                    vec![false, true, false],
                    vec![false, false, true],
                    10
                )
            ),
            Ok(Crown {
                tree: Node::Split {
                    info: root.tree.info().clone(),
                    own: vec![true, false, false],
                    left: child(1, 45),
                    right: child(2, 45),
                },
                helps: Vec::new(),
            })
        );
    }

    /// The core names the first failing check: overlapping halves, a
    /// split below a split, an event at a missing node, a split past the
    /// budget.
    #[test]
    fn refused_events_name_their_check() {
        let root = Crown::root(vec![true; 2], Lim::Value(5), Lim::Unlimited);
        let halves = split(
            vec![],
            vec![false, false],
            vec![true, false],
            vec![false, true],
            0,
        );
        let crown = step(BOUNDS, &root, &halves).expect("split");
        assert_eq!(
            [
                step(
                    BOUNDS,
                    &root,
                    &split(
                        vec![],
                        vec![false, false],
                        vec![true, true],
                        vec![false, true],
                        0
                    )
                ),
                step(BOUNDS, &crown, &halves),
                step(
                    BOUNDS,
                    &root,
                    &CrownEvent::Tree(Event::Cancel {
                        at: vec![Dir::Left]
                    })
                ),
                step(
                    BOUNDS,
                    &root,
                    &split(
                        vec![],
                        vec![false, false],
                        vec![true, false],
                        vec![false, true],
                        4
                    )
                ),
            ],
            [
                Err(Refusal::BadScopes),
                Err(Refusal::NotLeaf),
                Err(Refusal::NoNode),
                Err(Refusal::NoBudget),
            ]
        );
    }

    /// Unspent limit returns: once the left child settles having spent 3
    /// of its 5, the parent's free counts 3, not 5.
    #[test]
    fn a_settled_child_returns_its_unspent_limit() {
        let root = Crown::root(vec![true; 2], Lim::Value(10), Lim::Unlimited);
        let crown = step(
            BOUNDS,
            &root,
            &split(
                vec![],
                vec![false, false],
                vec![true, false],
                vec![false, true],
                0,
            ),
        )
        .and_then(|c| {
            step(
                BOUNDS,
                &c,
                &CrownEvent::Tree(Event::Spend {
                    at: vec![Dir::Left],
                    amount: 3,
                }),
            )
        })
        .expect("split, spend");
        let settled = step(
            BOUNDS,
            &crown,
            &CrownEvent::Tree(Event::Finish {
                at: vec![Dir::Left],
                patch: vec![Some(7)],
            }),
        )
        .expect("finish");
        assert_eq!(
            [free(&crown, &[]), free(&settled, &[])],
            [Some(Lim::Value(0)), Some(Lim::Value(2))]
        );
    }

    /// Cancel reaches every descendant and every help leaf below it.
    #[test]
    fn cancel_reaches_every_descendant_and_help_leaf() {
        let root = Crown::root(vec![true; 3], Lim::Unlimited, Lim::Unlimited);
        let crown = step(
            BOUNDS,
            &root,
            &split(
                vec![],
                vec![true, false, false],
                vec![false, true, false],
                vec![false, false, true],
                0,
            ),
        )
        .and_then(|c| {
            step(
                BOUNDS,
                &c,
                &CrownEvent::Help {
                    at: vec![Dir::Left],
                    amount: 0,
                },
            )
        })
        .and_then(|c| step(BOUNDS, &c, &CrownEvent::Tree(Event::Cancel { at: vec![] })))
        .expect("split, help, cancel");
        let statuses = [vec![], vec![Dir::Left], vec![Dir::Right]]
            .map(|p| crown.tree.at(&p).map(|n| n.info().status));
        assert_eq!(
            (
                statuses,
                crown.helps.iter().map(|h| h.status).collect::<Vec<_>>()
            ),
            ([Some(Status::Cancelled); 3], vec![Status::Cancelled])
        );
    }

    /// A help leaf takes its limit from the node's free, and its unspent
    /// part returns when it settles.
    #[test]
    fn a_help_leaf_draws_from_free() {
        let root = Crown::root(vec![true], Lim::Value(10), Lim::Unlimited);
        let helped = step(
            BOUNDS,
            &root,
            &CrownEvent::Help {
                at: vec![],
                amount: 4,
            },
        )
        .and_then(|c| {
            step(
                BOUNDS,
                &c,
                &CrownEvent::HelpSpend {
                    index: 0,
                    amount: 1,
                },
            )
        })
        .expect("help, spend");
        let settled = step(
            BOUNDS,
            &helped,
            &CrownEvent::HelpEnd {
                index: 0,
                outcome: HelpOutcome::Finished,
            },
        )
        .expect("end");
        assert_eq!(
            [
                free(&helped, &[]),
                free(&settled, &[]),
                free(&settled, &[Dir::Left])
            ],
            [Some(Lim::Value(6)), Some(Lim::Value(9)), None]
        );
    }

    /// Integration takes the child's writes inside its scope and reports
    /// the ones outside.
    #[test]
    fn overlay_keeps_in_scope_writes_and_reports_the_rest() {
        assert_eq!(
            overlay(
                &[Some(1), None, None],
                &[Some(9), Some(2), Some(3)],
                &[false, true, false]
            ),
            Overlay {
                patch: vec![Some(1), Some(2), None],
                conflicts: vec![true, false, true],
            }
        );
    }

    /// A user message comes first; a node waits only with nothing to do.
    #[test]
    fn next_action_order() {
        let view = |message, arrived, own_work| View {
            message,
            arrived,
            own_work,
        };
        assert_eq!(
            [
                next(view(true, 2, true)),
                next(view(false, 1, true)),
                next(view(false, 0, true)),
                next(view(false, 0, false)),
            ],
            [
                Action::ReadMessage,
                Action::Integrate,
                Action::WorkOwn,
                Action::Wait
            ]
        );
    }
}
