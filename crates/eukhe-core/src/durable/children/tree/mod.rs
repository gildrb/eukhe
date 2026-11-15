//! A session's place in the agent tree and its local crown
//! (`docs/internals/agent-tree.md`; decisions:
//! `eukhe_bend::rules::agent_tree`).
//!
//! Each session keeps a LOCAL crown in its `eukhe.rlm.tree` conversation
//! document: the root is the session itself (its scope), then its two
//! split children and its help leaves; a child's own subtree lives in the
//! child's session. The bounds passed to the core are local
//! ([`plan::bounds`]): the depth left below the session, and its node
//! allowance less what it gave its split children beyond their first
//! node. Every event goes through the core's `step`; Rust maps paths to
//! units ([`plan::refine`], [`plan::mask`]) and keeps the crown between
//! calls.

mod crown;
mod plan;

#[cfg(test)]
mod tests;

use std::collections::BTreeMap;

use eukhe_bend::rules::agent_tree::{
    self, Bounds, Crown, CrownEvent, Dir, Event, HelpOutcome, Lim, Node, Patch, Refusal, Scope,
    Status,
};
use eukhe_chord::context::Context;
use eukhe_chord::json::{from_json, to_json, JsonValue};
use eukhe_durable::documents::{ConversationDoc, DocDefinition};
use eukhe_durable::session::{SessionResult, Tx};
use eukhe_durable::types::{ConversationId, DocumentReader, DocumentReaderExt, LatestFork};
use eukhe_types::budget::BudgetDimension;
use eukhe_types::daemon::agent_tree::{TreePlace, TreeRole};
use serde::{Deserialize, Serialize};

use crate::durable::deps::{SessionRole, SessionShape};
use crown::CrownDoc;
pub(crate) use crown::DirDoc;
pub(crate) use plan::{
    child_limits, dimension, hold, mask, paths, refine_all, spent, unit_path, MAX_NODES,
};

/// The text a spawn of a session outside the agent tree reads.
pub(crate) const OUTSIDE_TREE: &str =
    "this session is outside the agent tree: only a tree node splits or asks a help leaf";

/// The place of the tree's root: the whole workspace, the full allowance.
#[must_use]
pub(crate) fn root_place() -> TreePlace {
    TreePlace {
        role: TreeRole::Root,
        scope: vec![String::new()],
        path: String::new(),
        allowance: MAX_NODES,
        deadline: None,
    }
}

/// The session's place in the tree: the one its spawn named, or the
/// root's for a top-level session of the `single` shape. Main (the
/// `main-worker` shape) is above the tree: its worker is the root.
#[must_use]
pub(crate) fn place_of(role: &SessionRole, shape: SessionShape) -> Option<TreePlace> {
    match (&role.tree, shape) {
        (Some(place), _) => Some(place.clone()),
        (None, SessionShape::Single) if role.is_root() => Some(root_place()),
        (None, SessionShape::Single | SessionShape::Main) => None,
    }
}

/// Where a spawned child sits in its parent's local crown.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", tag = "kind")]
pub(crate) enum Slot {
    /// A split child of this session.
    Side { dir: DirDoc },
    /// Help leaf `index` of this session.
    Help { index: usize },
    /// The tree's root under main (main keeps no crown).
    Root,
    /// A node of a crown its spawner keeps itself (a workflow's batch).
    External,
}

impl Slot {
    /// The split side, for a split child.
    #[must_use]
    pub(crate) fn side(dir: Dir) -> Self {
        Self::Side { dir: dir.into() }
    }
}

/// How a node's run ended, as its parent records it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum End {
    Finished(Patch),
    Failed(Patch),
    Cancelled,
}

/// One half of an admitted split.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Half {
    /// The paths of the units it owns.
    pub(crate) scope: Vec<String>,
    pub(crate) mask: Scope,
    pub(crate) allowance: u64,
    pub(crate) limit: Lim,
    pub(crate) deadline: Lim,
}

/// The two halves of an admitted split.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Halves {
    pub(crate) left: Half,
    pub(crate) right: Half,
}

/// A split as its caller names it, in paths.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SplitRequest {
    pub(crate) left: Vec<String>,
    pub(crate) right: Vec<String>,
    /// `None`: the rest of the session's scope.
    pub(crate) own: Option<Vec<String>>,
    /// `None`: the default hold ([`hold`]).
    pub(crate) hold: Option<u64>,
}

/// What a session's tree facts are, as a spawner outside its crown reads
/// them (a workflow's batch).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Facts {
    /// The paths the session itself writes now.
    pub(crate) write_scope: Vec<String>,
    /// The session's depth below the root.
    pub(crate) depth: u64,
    /// The nodes it may still hold.
    pub(crate) remaining: u64,
    /// What it may still spend or give.
    pub(crate) free: Lim,
    pub(crate) deadline: Lim,
}

/// A session's local crown with what maps it to paths and tasks.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct Local {
    /// Unit paths; index = position in every scope and patch.
    pub(crate) units: Vec<String>,
    crown: CrownDoc,
    /// The session's depth below the tree's root.
    pub(crate) depth: u64,
    /// The nodes the session may hold, itself included.
    pub(crate) allowance: u64,
    /// The nodes given to its split children beyond their first.
    pub(crate) given: u64,
    /// The budget dimension the crown's amounts count; `None`: unlimited.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) dimension: Option<BudgetDimension>,
    /// The tasks of its split children.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) left: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) right: Option<u64>,
    /// The tasks of its help leaves, by index.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub(crate) helps: Vec<u64>,
    /// The sides already run again once.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    redone: Vec<DirDoc>,
    /// Nodes lent to crowns its spawner keeps itself (a workflow's
    /// batches), by key; they count in `given` until returned.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    lent: BTreeMap<String, u64>,
}

/// The `eukhe.rlm.tree` document.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct TreeState {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) local: Option<Local>,
}

pub(crate) static TREE_DOC: ConversationDoc<TreeState> = match ConversationDoc::define(
    DocDefinition {
        kind: "eukhe.rlm.tree",
        version: 1,
        initial: TreeState::default,
        migrate: None,
        checkpoint_when: None,
    },
    // A fork starts outside any split: its children are not the fork's.
    LatestFork::Initial,
) {
    Ok(token) => token,
    Err(_) => panic!("eukhe.rlm.tree has a valid version"),
};

/// The committed local crown of `conversation_id`, if it has one.
///
/// # Errors
///
/// Document read failures.
pub(crate) async fn read_local(
    reader: &(impl DocumentReader + ?Sized),
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<Option<Local>> {
    let value = reader.snapshot(&TREE_DOC, conversation_id, cx).await?;
    Ok(match value {
        None => None,
        Some(value) => from_json::<TreeState>(&JsonValue::Object(value))?.local,
    })
}

/// The local crown inside a commit.
///
/// # Errors
///
/// Document read failures.
pub(crate) async fn tx_local(
    tx: &Tx,
    conversation_id: ConversationId,
) -> SessionResult<Option<Local>> {
    let value = tx.doc(&TREE_DOC, conversation_id).await?.value()?;
    Ok(from_json::<TreeState>(&value)?.local)
}

/// Write the local crown inside a commit.
///
/// # Errors
///
/// Document write failures.
pub(crate) async fn tx_put_local(
    tx: &Tx,
    conversation_id: ConversationId,
    local: &Local,
) -> SessionResult<()> {
    tx.doc(&TREE_DOC, conversation_id)
        .await?
        .set("local", to_json(local)?)?;
    Ok(())
}

fn deadline_lim(deadline: Option<u64>) -> Lim {
    deadline.map_or(Lim::Unlimited, Lim::Value)
}

fn deadline_ms(deadline: Lim) -> Option<u64> {
    match deadline {
        Lim::Unlimited => None,
        Lim::Value(at) => Some(at),
    }
}

/// The node at `slot` in `crown`, for a slot of this session's crown.
fn status_at(crown: &Crown, slot: Slot) -> Option<Status> {
    match slot {
        Slot::Side { dir } => crown.tree.at(&[dir.into()]).map(|node| node.info().status),
        Slot::Help { index } => crown.helps.get(index).map(|help| help.status),
        Slot::Root | Slot::External => None,
    }
}

impl Local {
    /// The crown of a session at `place` before its first split: a running
    /// root over its own scope with `limit`, counted in `dimension`.
    #[must_use]
    pub(crate) fn open(place: &TreePlace, limit: Lim, dimension: Option<BudgetDimension>) -> Self {
        let mut units: Vec<String> = Vec::with_capacity(place.scope.len());
        for path in place.scope.iter().map(|path| unit_path(path)) {
            if !units.contains(&path) {
                units.push(path);
            }
        }
        let crown = Crown::root(vec![true; units.len()], limit, deadline_lim(place.deadline));
        Self {
            units,
            crown: (&crown).into(),
            depth: u64::try_from(place.path.len()).unwrap_or(u64::MAX),
            allowance: place.allowance,
            given: 0,
            dimension,
            left: None,
            right: None,
            helps: Vec::new(),
            redone: Vec::new(),
            lent: BTreeMap::new(),
        }
    }

    /// The local crown.
    #[must_use]
    pub(crate) fn crown(&self) -> Crown {
        (&self.crown).into()
    }

    fn with_crown(&self, crown: &Crown) -> Self {
        Self {
            crown: crown.into(),
            ..self.clone()
        }
    }

    /// The bounds the core decides this crown's events under.
    #[must_use]
    pub(crate) fn bounds(&self) -> Bounds {
        let crown = self.crown();
        plan::bounds(
            self.depth,
            self.allowance,
            self.given,
            crown.tree.info().deadline,
        )
    }

    /// The core's decision on `event`.
    ///
    /// # Errors
    ///
    /// The core's refusal; the crown stays.
    pub(crate) fn step(&self, event: &CrownEvent) -> Result<Self, Refusal> {
        agent_tree::step(self.bounds(), &self.crown(), event).map(|crown| self.with_crown(&crown))
    }

    /// What the session may still spend or give.
    #[must_use]
    pub(crate) fn free(&self) -> Lim {
        agent_tree::free(&self.crown(), &[]).unwrap_or(Lim::Value(0))
    }

    /// The session's facts for a spawner outside its crown.
    #[must_use]
    pub(crate) fn facts(&self) -> Facts {
        let crown = self.crown();
        let own = match &crown.tree {
            Node::Leaf(info) => info.scope.clone(),
            Node::Split { own, .. } => own.clone(),
        };
        Facts {
            write_scope: paths(&self.units, &own),
            depth: self.depth,
            remaining: self
                .allowance
                .saturating_sub(self.given)
                .saturating_sub(plan::size(&crown)),
            free: self.free(),
            deadline: crown.tree.info().deadline,
        }
    }

    /// Admit the split `request`: the named paths become units, the core
    /// decides the split, and each child gets its share of the
    /// allowance. `worst_request`: one worst-case model request in the
    /// crown's dimension (the default hold is two of them, or a tenth of
    /// the room).
    ///
    /// # Errors
    ///
    /// The core's refusal; nothing changes.
    pub(crate) fn split(
        &self,
        request: &SplitRequest,
        worst_request: u64,
    ) -> Result<(Self, Halves), Refusal> {
        let normal =
            |paths: &[String]| paths.iter().map(|path| unit_path(path)).collect::<Vec<_>>();
        let (left, right) = (normal(&request.left), normal(&request.right));
        let own = request.own.as_deref().map(normal);
        let named: Vec<String> = left
            .iter()
            .chain(&right)
            .chain(own.iter().flatten())
            .cloned()
            .collect();
        let (crown, units) = refine_all(&self.crown(), &self.units, &named);
        let (left_mask, right_mask) = (mask(&units, &left), mask(&units, &right));
        let own_mask = match &own {
            Some(own) => mask(&units, own),
            None => plan::rest(&crown.tree.info().scope, &left_mask, &right_mask),
        };
        let hold = request
            .hold
            .unwrap_or_else(|| plan::hold(self.free(), worst_request));
        let size = plan::size(&crown);
        let refined = Self {
            units: units.clone(),
            ..self.with_crown(&crown)
        };
        let split = refined.step(&CrownEvent::Tree(Event::Split {
            at: Vec::new(),
            own: own_mask,
            left: left_mask.clone(),
            right: right_mask.clone(),
            hold,
        }))?;
        let (left_allowance, right_allowance) = plan::child_allowances(self.allowance, size);
        let after = split.crown();
        let half = |dir: Dir, mask: Scope, allowance: u64| {
            let info = after
                .tree
                .at(&[dir])
                .map(Node::info)
                .cloned()
                .unwrap_or_else(|| after.tree.info().clone());
            Half {
                scope: paths(&units, &mask),
                mask,
                allowance,
                limit: info.limit,
                deadline: info.deadline,
            }
        };
        let halves = Halves {
            left: half(Dir::Left, left_mask, left_allowance),
            right: half(Dir::Right, right_mask, right_allowance),
        };
        Ok((
            Self {
                given: split.given + (left_allowance - 1) + (right_allowance - 1),
                ..split
            },
            halves,
        ))
    }

    /// Admit a help leaf with limit `amount`; answers its index.
    ///
    /// # Errors
    ///
    /// The core's refusal; nothing changes.
    pub(crate) fn help(&self, amount: u64) -> Result<(Self, usize), Refusal> {
        let next = self.step(&CrownEvent::Help {
            at: Vec::new(),
            amount,
        })?;
        let index = next.crown().helps.len().saturating_sub(1);
        Ok((next, index))
    }

    /// The default limit of a help leaf: a tenth of what is free.
    #[must_use]
    pub(crate) fn help_amount(&self) -> u64 {
        hold(self.free(), 0)
    }

    /// Record the end of the child at `slot`: what it spent beyond what
    /// the crown already holds (`spent` is its whole spend so far; the
    /// core lets it spend at most its free), then how it ended. An event
    /// the core refuses (a node a tick or a cancel already settled) leaves
    /// the crown as it is.
    #[must_use]
    pub(crate) fn settle(&self, slot: Slot, spent: u64, end: &End) -> Self {
        let crown = self.crown();
        let after =
            |local: &Self, event: CrownEvent| local.step(&event).unwrap_or_else(|_| local.clone());
        match slot {
            Slot::Side { dir } => {
                let at = vec![Dir::from(dir)];
                let amount = crown
                    .tree
                    .at(&at)
                    .map_or(0, |node| spent.saturating_sub(node.info().spent));
                let charge = match agent_tree::free(&crown, &at) {
                    Some(Lim::Value(free)) => amount.min(free),
                    Some(Lim::Unlimited) => amount,
                    None => 0,
                };
                let charged = after(
                    self,
                    CrownEvent::Tree(Event::Spend {
                        at: at.clone(),
                        amount: charge,
                    }),
                );
                let event = match end {
                    End::Finished(patch) => Event::Finish {
                        at,
                        patch: patch.clone(),
                    },
                    End::Failed(patch) => Event::Fail {
                        at,
                        patch: patch.clone(),
                    },
                    End::Cancelled => Event::Cancel { at },
                };
                after(&charged, CrownEvent::Tree(event))
            }
            Slot::Help { index } => {
                let charge = crown.helps.get(index).map_or(0, |help| {
                    let amount = spent.saturating_sub(help.spent);
                    match help.limit {
                        Lim::Value(limit) => amount.min(limit.saturating_sub(help.spent)),
                        Lim::Unlimited => amount,
                    }
                });
                let charged = after(
                    self,
                    CrownEvent::HelpSpend {
                        index,
                        amount: charge,
                    },
                );
                let outcome = match end {
                    End::Finished(_) => HelpOutcome::Finished,
                    End::Failed(_) | End::Cancelled => HelpOutcome::Failed,
                };
                after(&charged, CrownEvent::HelpEnd { index, outcome })
            }
            Slot::Root | Slot::External => self.clone(),
        }
    }

    /// Run the failed split child at `dir` again, once per side, with
    /// `extra` more to spend.
    ///
    /// # Errors
    ///
    /// The side already ran again (`NotRedoable`), or the core's refusal.
    pub(crate) fn redo(&self, dir: Dir, extra: u64) -> Result<Self, Refusal> {
        let side = DirDoc::from(dir);
        if self.redone.contains(&side) {
            return Err(Refusal::NotRedoable);
        }
        let next = self.step(&CrownEvent::Tree(Event::Redo {
            at: Vec::new(),
            side: dir,
            extra,
        }))?;
        let mut redone = next.redone.clone();
        redone.push(side);
        Ok(Self { redone, ..next })
    }

    /// The crown after the clock read `now`, and the tasks of the children
    /// it cancelled (past their deadline, or under a node that is).
    #[must_use]
    pub(crate) fn tick(&self, now: u64) -> (Self, Vec<u64>) {
        let before = self.crown();
        let Ok(next) = self.step(&CrownEvent::Tree(Event::Tick { now })) else {
            return (self.clone(), Vec::new());
        };
        let after = next.crown();
        let cancelled = |slot: Slot| {
            status_at(&before, slot).is_some_and(Status::is_running)
                && status_at(&after, slot) == Some(Status::Cancelled)
        };
        let sides = [(Dir::Left, self.left), (Dir::Right, self.right)]
            .into_iter()
            .filter_map(|(dir, task)| task.filter(|_| cancelled(Slot::side(dir))));
        let helps = self
            .helps
            .iter()
            .enumerate()
            .filter(|(index, _)| cancelled(Slot::Help { index: *index }))
            .map(|(_, task)| *task);
        let tasks = sides.chain(helps).collect();
        (next, tasks)
    }

    /// The nodes the session may still hold.
    #[must_use]
    pub(crate) fn remaining(&self) -> u64 {
        self.allowance
            .saturating_sub(self.given)
            .saturating_sub(plan::size(&self.crown()))
    }

    /// Lend `nodes` under `key` to a crown kept outside this one (once per
    /// key).
    ///
    /// # Errors
    ///
    /// `TooMany` when they exceed what the session may still hold.
    pub(crate) fn lend(&self, key: &str, nodes: u64) -> Result<Self, Refusal> {
        if self.lent.contains_key(key) {
            return Ok(self.clone());
        }
        if nodes > self.remaining() {
            return Err(Refusal::TooMany);
        }
        let mut lent = self.lent.clone();
        lent.insert(key.to_owned(), nodes);
        Ok(Self {
            lent,
            given: self.given + nodes,
            ..self.clone()
        })
    }

    /// The nodes lent under `key` come back (once).
    #[must_use]
    pub(crate) fn take_back(&self, key: &str) -> Self {
        let mut lent = self.lent.clone();
        let nodes = lent.remove(key).unwrap_or(0);
        Self {
            lent,
            given: self.given.saturating_sub(nodes),
            ..self.clone()
        }
    }

    /// The deadline of a child of this crown, as its place names it.
    #[must_use]
    pub(crate) fn deadline_of(deadline: Lim) -> Option<u64> {
        deadline_ms(deadline)
    }
}
