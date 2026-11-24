//! A writing batch of a workflow on the agent tree: the writing `agent()`
//! calls a script starts together form a group, checked whole, that
//! starts in waves ([`wave`]); each wave is one crown, a balanced binary
//! tree over its agents in call order. Its leaves are the agents; its
//! internal nodes are integrators the harness runs (no model): each
//! finishes once both its children settled, its patch the overlay of
//! theirs. One agent alone is the crown's root. The record keeps the
//! plan (units, room, leaves) and the leaves' ends in order; the crown is
//! their replay, every decision the core's (`agent_tree::step`,
//! `overlay`).

use std::path::{Component, Path};

use eukhe_bend::rules::agent_tree::{
    overlay, step, Bounds, Crown, CrownEvent, Dir, Event, Lim, Node, Patch, Refusal, Scope, Status,
};
use serde::{Deserialize, Serialize};

/// The tree's depth bound.
const MAX_DEPTH: u64 = 3;
/// The time a child's deadline keeps before its parent's (ms), under a
/// deadline.
const MARGIN_MS: u64 = 120_000;

/// Where a batch's root sits in the tree and what it may hold.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct Room {
    /// The session's path in the tree (left/right steps from the root);
    /// the batch's root is its left child.
    #[serde(default)]
    pub(crate) path: String,
    /// The root's depth: the session's depth + 1.
    pub(crate) depth: u64,
    /// The nodes the batch may hold, its root included.
    pub(crate) allowance: u64,
    /// The batch's limit; `None`: unlimited.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) limit: Option<Limit>,
    /// The batch's deadline (Unix ms); `None`: unlimited.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) deadline: Option<u64>,
}

/// A limit in the tree's budget dimension: the `budget` key of a spawn
/// (`tokens`, `cost_usd`, ...) and the amount.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Limit {
    pub(crate) key: String,
    pub(crate) amount: u64,
}

/// One writing agent of a batch: its leaf.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct Leaf {
    pub(crate) ordinal: u32,
    /// Left/right steps from the batch's root (`""`: the root).
    pub(crate) path: String,
    /// The files and directories the agent writes.
    pub(crate) scope: Vec<String>,
}

/// How a leaf ended.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub(crate) enum Outcome {
    Finished,
    Failed,
}

/// A leaf's end: how, and its patch over the batch's units.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct End {
    pub(crate) leaf: usize,
    pub(crate) outcome: Outcome,
    pub(crate) patch: Patch,
}

/// A writing batch: its plan and what happened to it since.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct Batch {
    /// The units of the crown's scopes: every path a leaf names, sorted.
    pub(crate) units: Vec<String>,
    pub(crate) room: Room,
    /// The agents, in call order.
    pub(crate) leaves: Vec<Leaf>,
    /// The leaves' ends, in the order they settled.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub(crate) ends: Vec<End>,
    /// The run cancelled the batch.
    #[serde(default)]
    pub(crate) cancelled: bool,
}

/// The refusal of a writing agent that names no file.
pub(crate) const NEEDS_FILES: &str = "a writing agent needs its files";

/// Why a batch is refused.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub(crate) enum BatchRefusal {
    #[error("{}", NEEDS_FILES)]
    NoScope,
    #[error(
        "agent(prompt, opts): scope paths are relative paths inside the workspace, not {path}"
    )]
    BadPath { path: String },
    #[error(
        "{agents} writing agents started together need {needed} levels below their root; {left} remain here (at most {most} writing agents at once)"
    )]
    TooDeep {
        agents: usize,
        needed: u64,
        left: u64,
        most: u64,
    },
    #[error("{path} lies outside this session's scope ({scope})")]
    OutsideSession { path: String, scope: String },
    #[error("{path} belongs to a running writing batch of this workflow (agents {ordinals})")]
    Busy { path: String, ordinals: String },
    #[error("the writing agents started together must name disjoint files")]
    Overlap,
    #[error("the agent tree has no node free for a writing agent")]
    NoRoom,
    #[error("{}", .0.text())]
    Core(Refusal),
}

/// The bounds a batch's crown is decided under.
fn bounds(room: &Room) -> Bounds {
    Bounds {
        max_depth: MAX_DEPTH.saturating_sub(room.depth),
        max_nodes: room.allowance,
        margin: match room.deadline {
            Some(_) => MARGIN_MS,
            None => 0,
        },
    }
}

/// The leaves a balanced tree holds within `levels` below its root.
fn leaves_within(levels: u64) -> u64 {
    1_u64
        .checked_shl(u32::try_from(levels).unwrap_or(u32::MAX))
        .unwrap_or(u64::MAX)
}

/// The most writing agents one batch holds when its root sits at `depth`
/// with `allowance` nodes: the leaves the depth bound allows, with every
/// node (`2n - 1`) within the allowance.
pub(crate) fn width(depth: u64, allowance: u64) -> u64 {
    leaves_within(MAX_DEPTH.saturating_sub(depth)).min(allowance.saturating_add(1) / 2)
}

fn lim(value: Option<u64>) -> Lim {
    match value {
        Some(value) => Lim::Value(value),
        None => Lim::Unlimited,
    }
}

/// `path` as directions from the root.
fn dirs(path: &str) -> Vec<Dir> {
    path.chars()
        .map(|step| if step == 'L' { Dir::Left } else { Dir::Right })
        .collect()
}

fn path_text(dirs: &[Dir]) -> String {
    dirs.iter()
        .map(|dir| match dir {
            Dir::Left => 'L',
            Dir::Right => 'R',
        })
        .collect()
}

/// The paths of `n` leaves of a balanced binary tree, in order: the
/// first ⌈n/2⌉ under the left child, the rest under the right.
fn shape(n: usize) -> Vec<Vec<Dir>> {
    match n {
        0 => Vec::new(),
        1 => vec![Vec::new()],
        _ => {
            let left = n.div_ceil(2);
            let under = |dir: Dir, count: usize| {
                shape(count).into_iter().map(move |mut path| {
                    path.insert(0, dir);
                    path
                })
            };
            under(Dir::Left, left)
                .chain(under(Dir::Right, n - left))
                .collect()
        }
    }
}

/// The levels below the root that `n` leaves of a balanced tree need.
fn levels(n: usize) -> u64 {
    u64::from(usize::BITS - n.saturating_sub(1).leading_zeros())
}

/// `path` normalized: relative, inside the workspace, `""` for all of it.
fn normalized(path: &str) -> Result<String, BatchRefusal> {
    let mut parts = Vec::new();
    for component in Path::new(path.trim()).components() {
        match component {
            Component::Normal(part) => parts.push(part.to_string_lossy().into_owned()),
            Component::CurDir => {}
            Component::ParentDir | Component::RootDir | Component::Prefix(_) => {
                return Err(BatchRefusal::BadPath {
                    path: path.to_owned(),
                })
            }
        }
    }
    Ok(parts.join("/"))
}

/// Whether `inner` is `outer` or lies under it, component-wise.
fn within(inner: &str, outer: &str) -> bool {
    Path::new(inner).starts_with(outer)
}

/// The mask of `scope` over `units`: a unit is owned when it is one of
/// the scope's paths or lies under one.
fn mask(units: &[String], scope: &[String]) -> Scope {
    units
        .iter()
        .map(|unit| scope.iter().any(|path| within(unit, path)))
        .collect()
}

fn any(masks: &[Scope], units: usize) -> Scope {
    (0..units)
        .map(|unit| masks.iter().any(|mask| mask[unit]))
        .collect()
}

/// The split events that build the tree over `masks` (in leaf order)
/// below `at`, parents first.
fn splits(at: &[Dir], masks: &[Scope], units: usize) -> Vec<Event> {
    if masks.len() < 2 {
        return Vec::new();
    }
    let (left, right) = masks.split_at(masks.len().div_ceil(2));
    let own = vec![false; units];
    let below = |dir: Dir, half: &[Scope]| {
        let mut path = at.to_vec();
        path.push(dir);
        splits(&path, half, units)
    };
    let mut events = vec![Event::Split {
        at: at.to_vec(),
        own,
        left: any(left, units),
        right: any(right, units),
        hold: 0,
    }];
    events.extend(below(Dir::Left, left));
    events.extend(below(Dir::Right, right));
    events
}

fn tree(bounds: Bounds, crown: &Crown, event: Event) -> Result<Crown, Refusal> {
    step(bounds, crown, &CrownEvent::Tree(event))
}

/// The scopes the agents of a running batch hold: every path of a leaf
/// that has not ended.
fn held(batch: &Batch) -> impl Iterator<Item = (&str, u32)> {
    batch
        .leaves
        .iter()
        .enumerate()
        .filter(|(index, _)| !batch.cancelled && batch.ends.iter().all(|end| end.leaf != *index))
        .flat_map(|(_, leaf)| {
            leaf.scope
                .iter()
                .map(move |path| (path.as_str(), leaf.ordinal))
        })
}

/// Whether no path of one scope is, contains or lies inside a path of
/// another: the masks of the scopes over their units do not meet.
fn disjoint(scopes: &[Vec<String>]) -> bool {
    scopes.iter().enumerate().all(|(at, scope)| {
        scopes[at + 1..].iter().all(|other| {
            scope.iter().all(|path| {
                other
                    .iter()
                    .all(|outer| !within(path, outer) && !within(outer, path))
            })
        })
    })
}

/// The scopes of the writing group `agents` (ordinal and scope, in call
/// order), normalized, checked together before any of them starts:
/// inside the session's write scope `session` (`""`: everything), clear
/// of the running batches (`running`), and disjoint from each other.
fn checked(
    session: &[String],
    running: &[&Batch],
    agents: &[(u32, Vec<String>)],
) -> Result<Vec<Vec<String>>, BatchRefusal> {
    let mut scopes = Vec::with_capacity(agents.len());
    for (_, scope) in agents {
        if scope.is_empty() {
            return Err(BatchRefusal::NoScope);
        }
        let paths = scope
            .iter()
            .map(|path| normalized(path))
            .collect::<Result<Vec<_>, _>>()?;
        if let Some(path) = paths
            .iter()
            .find(|path| !session.iter().any(|outer| within(path, outer)))
        {
            return Err(BatchRefusal::OutsideSession {
                path: path.clone(),
                scope: session.join(", "),
            });
        }
        scopes.push(paths);
    }
    for path in scopes.iter().flatten() {
        let ordinals: Vec<String> = running
            .iter()
            .copied()
            .flat_map(held)
            .filter(|(other, _)| within(path, other) || within(other, path))
            .map(|(_, ordinal)| ordinal.to_string())
            .collect();
        if !ordinals.is_empty() {
            return Err(BatchRefusal::Busy {
                path: path.clone(),
                ordinals: ordinals.join(", "),
            });
        }
    }
    if !disjoint(&scopes) {
        return Err(BatchRefusal::Overlap);
    }
    Ok(scopes)
}

/// The batch of `agents` with their checked `scopes`, in `room`: the
/// balanced tree's leaves in call order.
fn laid_out(room: Room, agents: &[(u32, Vec<String>)], scopes: &[Vec<String>]) -> Batch {
    let mut units: Vec<String> = scopes.iter().flatten().cloned().collect();
    units.sort();
    units.dedup();
    Batch {
        leaves: agents
            .iter()
            .zip(scopes)
            .zip(shape(agents.len()))
            .map(|(((ordinal, _), scope), path)| Leaf {
                ordinal: *ordinal,
                path: path_text(&path),
                scope: scope.clone(),
            })
            .collect(),
        units,
        room,
        ends: Vec::new(),
        cancelled: false,
    }
}

/// Plan the batch of the writing agents `agents` (ordinal and scope, in
/// call order) in `room`, all or none, inside the session's write scope
/// `session` (`""`: everything), beside the running batches (`running`).
///
/// # Errors
///
/// An agent without files, a path outside the workspace or the session's
/// scope, a path a running batch holds, shared files, more agents than
/// the remaining depth allows, or a split the core refuses.
pub(crate) fn plan(
    room: Room,
    session: &[String],
    running: &[&Batch],
    agents: &[(u32, Vec<String>)],
) -> Result<Batch, BatchRefusal> {
    let scopes = checked(session, running, agents)?;
    let batch = laid_out(room, agents, &scopes);
    admitted(&batch)?;
    Ok(batch)
}

/// The next wave of a writing group.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Wave {
    /// The group's first agents, as one batch; the rest start later.
    Batch(Batch),
    /// The room holds no writing agent until a running batch settles.
    Full,
}

/// The next wave of the writing group `agents` (ordinal and scope, in
/// call order) in `room`: the longest first run of agents one batch holds
/// (the depth bound, the nodes, the budget's splits). The whole group is
/// checked first, so a later wave meets no refusal this one could have
/// named.
///
/// # Errors
///
/// An agent without files, a path outside the workspace or the session's
/// scope, a path a running batch holds, shared files, or a split the core
/// refuses for another reason than room.
pub(crate) fn wave(
    room: &Room,
    session: &[String],
    running: &[&Batch],
    agents: &[(u32, Vec<String>)],
) -> Result<Wave, BatchRefusal> {
    let scopes = checked(session, running, agents)?;
    let most = usize::try_from(width(room.depth, room.allowance))
        .unwrap_or(usize::MAX)
        .min(agents.len());
    for count in (1..=most).rev() {
        let batch = laid_out(room.clone(), &agents[..count], &scopes[..count]);
        match admitted(&batch) {
            Ok(_) => return Ok(Wave::Batch(batch)),
            Err(
                BatchRefusal::TooDeep { .. }
                | BatchRefusal::Core(Refusal::TooMany | Refusal::NoBudget),
            ) => {}
            Err(
                refusal @ (BatchRefusal::NoScope
                | BatchRefusal::BadPath { .. }
                | BatchRefusal::OutsideSession { .. }
                | BatchRefusal::Busy { .. }
                | BatchRefusal::Overlap
                | BatchRefusal::NoRoom
                | BatchRefusal::Core(
                    Refusal::NoNode
                    | Refusal::NotRunning
                    | Refusal::NotLeaf
                    | Refusal::TooDeep
                    | Refusal::BadScopes
                    | Refusal::Unsettled
                    | Refusal::NotRedoable,
                )),
            ) => return Err(refusal),
        }
    }
    Ok(Wave::Full)
}

/// The crown the batch's plan admits: the root over every unit, split
/// down to one leaf per agent.
fn admitted(batch: &Batch) -> Result<Crown, BatchRefusal> {
    let units = batch.units.len();
    let masks: Vec<Scope> = batch
        .leaves
        .iter()
        .map(|leaf| mask(&batch.units, &leaf.scope))
        .collect();
    let root = Crown::root(
        any(&masks, units),
        lim(batch.room.limit.as_ref().map(|limit| limit.amount)),
        lim(batch.room.deadline),
    );
    let bounds = bounds(&batch.room);
    splits(&[], &masks, units)
        .into_iter()
        .try_fold(root, |crown, event| tree(bounds, &crown, event))
        .map_err(|refusal| match refusal {
            Refusal::BadScopes => BatchRefusal::Overlap,
            Refusal::TooDeep => {
                let left = bounds.max_depth;
                BatchRefusal::TooDeep {
                    agents: batch.leaves.len(),
                    needed: levels(batch.leaves.len()),
                    left,
                    most: leaves_within(left),
                }
            }
            Refusal::NoNode
            | Refusal::NotRunning
            | Refusal::NotLeaf
            | Refusal::TooMany
            | Refusal::NoBudget
            | Refusal::Unsettled
            | Refusal::NotRedoable => BatchRefusal::Core(refusal),
        })
}

/// The patch the integrator at `node` finishes with, once it runs and
/// both its children settled: its own patch, then each finished child's
/// overlaid by the child's scope, left then right. A failed child's
/// partial patch stays out. `None`: a leaf, a settled node, or a child
/// still running.
fn integration(node: &Node, units: usize) -> Option<Patch> {
    let Node::Split {
        info, left, right, ..
    } = node
    else {
        return None;
    };
    let children = [left.info(), right.info()];
    if !info.status.is_running() || children.iter().any(|child| child.status.is_running()) {
        return None;
    }
    let start = match info.patch.len() {
        0 => vec![None; units],
        _ => info.patch.clone(),
    };
    Some(
        children
            .into_iter()
            .filter(|child| child.status == Status::Finished && !child.patch.is_empty())
            .fold(start, |patch, child| {
                overlay(&patch, &child.patch, &child.scope).patch
            }),
    )
}

/// Finish every integrator above `leaf` whose children both settled,
/// deepest first.
fn integrate(bounds: Bounds, crown: Crown, leaf: &[Dir], units: usize) -> Result<Crown, Refusal> {
    let mut crown = crown;
    for depth in (0..leaf.len()).rev() {
        let at = &leaf[..depth];
        let Some(patch) = crown.tree.at(at).and_then(|node| integration(node, units)) else {
            break;
        };
        crown = tree(
            bounds,
            &crown,
            Event::Finish {
                at: at.to_vec(),
                patch,
            },
        )?;
    }
    Ok(crown)
}

/// The batch's crown now: the plan, then each leaf's end with the
/// integrations it completes, then the run's cancel.
///
/// # Errors
///
/// The core refuses the plan or an end (a record this code did not
/// write).
pub(crate) fn crown(batch: &Batch) -> Result<Crown, BatchRefusal> {
    let bounds = bounds(&batch.room);
    let units = batch.units.len();
    let mut crown = admitted(batch)?;
    for end in &batch.ends {
        let Some(leaf) = batch.leaves.get(end.leaf) else {
            return Err(BatchRefusal::Core(Refusal::NoNode));
        };
        let at = dirs(&leaf.path);
        let event = match end.outcome {
            Outcome::Finished => Event::Finish {
                at: at.clone(),
                patch: end.patch.clone(),
            },
            Outcome::Failed => Event::Fail {
                at: at.clone(),
                patch: end.patch.clone(),
            },
        };
        crown = tree(bounds, &crown, event)
            .and_then(|crown| integrate(bounds, crown, &at, units))
            .map_err(BatchRefusal::Core)?;
    }
    if batch.cancelled {
        crown =
            tree(bounds, &crown, Event::Cancel { at: Vec::new() }).map_err(BatchRefusal::Core)?;
    }
    Ok(crown)
}

/// What a leaf's spawn carries: its place in the batch's crown.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LeafPlace {
    pub(crate) path: String,
    /// The leaf's scope as a mask over the batch's units.
    pub(crate) mask: Scope,
    pub(crate) limit: Lim,
    pub(crate) deadline: Lim,
}

/// The place of the agent `ordinal` in the batch's crown.
pub(crate) fn place(batch: &Batch, crown: &Crown, ordinal: u32) -> Option<LeafPlace> {
    let leaf = batch.leaves.iter().find(|leaf| leaf.ordinal == ordinal)?;
    let info = crown.tree.at(&dirs(&leaf.path))?.info();
    Some(LeafPlace {
        path: leaf.path.clone(),
        mask: info.scope.clone(),
        limit: info.limit,
        deadline: info.deadline,
    })
}

impl Batch {
    /// The batch with agent `ordinal`'s end recorded; unchanged when that
    /// agent ended already or is not in the batch.
    pub(crate) fn ended(mut self, ordinal: u32, outcome: Outcome, patch: Patch) -> Self {
        let Some(leaf) = self.leaves.iter().position(|leaf| leaf.ordinal == ordinal) else {
            return self;
        };
        if self.ends.iter().all(|end| end.leaf != leaf) {
            self.ends.push(End {
                leaf,
                outcome,
                patch,
            });
        }
        self
    }

    /// Whether every leaf ended or the run cancelled the batch.
    pub(crate) fn settled(&self) -> bool {
        self.cancelled || self.ends.len() == self.leaves.len()
    }
}
