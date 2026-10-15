//! The ownership tree of tasks and conversations (spec §5.5): walks up it
//! decide what reaches one task, a cancelling owner or a scope; walks down
//! the index of live work ([`State::below`]) decide what lies below one node,
//! a task's live ordinary owned work, a scope's tasks, a cascade's reach.
//!
//! A task's parent is its owner task, or its conversation; a conversation's
//! parent is its owner task, if any.

use std::collections::HashMap;
use std::sync::OnceLock;

use indexmap::{IndexMap, IndexSet};

use crate::session::Tx;
use crate::types::{AnyTaskRecord, ConversationId, ConversationOwner, TaskId, TaskState};

use super::state::State;

/// The immutable ownership fields of a task.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct TaskNode {
    pub(super) conversation_id: ConversationId,
    pub(super) owner: Option<TaskId>,
    pub(super) background: bool,
}

impl TaskNode {
    pub(super) fn of(record: &AnyTaskRecord) -> Self {
        Self {
            conversation_id: record.conversation_id,
            owner: record.owner,
            background: record.background,
        }
    }

    /// The node this task hangs from: its owner task, or its conversation.
    pub(super) fn parent(&self) -> Node {
        match self.owner {
            Some(owner) => Node::Task(owner),
            None => Node::Conversation(self.conversation_id),
        }
    }
}

/// The parent of a record in the ownership tree.
pub(super) fn parent_of(record: &AnyTaskRecord) -> Node {
    TaskNode::of(record).parent()
}

/// A node of the ownership tree: a task, or a conversation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) enum Node {
    Task(TaskId),
    Conversation(ConversationId),
}

/// One step of a walk up: an owner task with its node, a conversation, or an
/// owner edge that is not loaded yet.
#[derive(Clone, Copy, Debug)]
pub(super) enum Step {
    Task { id: TaskId, node: TaskNode },
    Conversation(ConversationId),
    Unknown,
}

/// Child nodes by parent node, each list in insertion order.
pub(super) type Links = HashMap<Node, IndexSet<Node>>;

/// Candidate records a commit staged; they override committed records in
/// ownership walks.
pub(super) struct Overlay {
    /// Staged task records in staging order.
    pub(super) tasks: IndexMap<TaskId, AnyTaskRecord>,
    /// Owner edges of staged conversations; `None` when ownerless.
    pub(super) edges: HashMap<ConversationId, Option<TaskId>>,
    /// Where walks down find the staged new tasks, derived at the first walk
    /// with this overlay.
    links: OnceLock<Links>,
}

impl Overlay {
    /// The candidates `tx` has staged so far.
    pub(super) fn of(tx: &Tx) -> Self {
        let tasks = tx
            .staged_tasks()
            .into_iter()
            .map(|record| (record.id, record))
            .collect();
        let edges = tx
            .staged_conversations()
            .into_iter()
            .map(|record| (record.id, owner_task(record.owner.as_ref())))
            .collect();
        Self {
            tasks,
            edges,
            links: OnceLock::new(),
        }
    }
}

/// The owner task of a conversation record, `None` when ownerless.
pub(super) fn owner_task(owner: Option<&ConversationOwner>) -> Option<TaskId> {
    owner.map(|owner| owner.task_id)
}

/// A conversation's owner edge as walks see it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Edge {
    /// Not loaded yet.
    Unloaded,
    /// The owner task, `None` when ownerless.
    Loaded(Option<TaskId>),
}

/// Where ordinary ownership traversal starts: one conversation, or every
/// ownerless conversation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Scope {
    Conversation(ConversationId),
    Roots,
}

/// Whether traversal crosses background owners.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(super) enum Background {
    /// Ordinary traversal: a background owner is a boundary.
    #[default]
    Boundary,
    /// Traversal ignoring the background flag.
    Cross,
}

/// How a walk down goes.
#[derive(Clone, Copy, Default)]
pub(super) struct Walk<'a> {
    /// The commit's candidates, which replace committed records; the walk
    /// also reaches the commit's new tasks.
    pub(super) overlay: Option<&'a Overlay>,
    /// Whether the walk enters background tasks, which it always reaches.
    pub(super) background: Background,
    /// The tasks the walk may enter; `None` enters every task.
    pub(super) enter: Option<&'a dyn Fn(TaskId) -> bool>,
}

/// A task a walk down reached: its node, and its record while live.
pub(super) struct Reached<'a> {
    pub(super) id: TaskId,
    pub(super) node: TaskNode,
    pub(super) live: Option<&'a AnyTaskRecord>,
}

/// Walk up from a start: owner tasks and conversations, ending at an
/// ownerless root or an edge not loaded yet.
pub(super) struct Above<'a> {
    state: &'a State,
    overlay: Option<&'a Overlay>,
    at: Option<Node>,
    /// A conversation step was yielded whose edge is not loaded; yield
    /// `Unknown` next and stop.
    unknown_next: bool,
}

impl Iterator for Above<'_> {
    type Item = Step;

    fn next(&mut self) -> Option<Step> {
        if self.unknown_next {
            self.unknown_next = false;
            self.at = None;
            return Some(Step::Unknown);
        }
        match self.at? {
            Node::Task(id) => {
                let Some(node) = self.state.node(id, self.overlay) else {
                    self.at = None;
                    return Some(Step::Unknown);
                };
                self.at = Some(node.parent());
                Some(Step::Task { id, node })
            }
            Node::Conversation(conversation) => {
                match self.state.edge(conversation, self.overlay) {
                    Edge::Unloaded => self.unknown_next = true,
                    Edge::Loaded(owner) => self.at = owner.map(Node::Task),
                }
                Some(Step::Conversation(conversation))
            }
        }
    }
}

/// The tasks below a start that a walk down reaches: those [`State::below`]
/// lists and, under an overlay, the commit's new tasks, with its candidates in
/// place of committed records. Depth first with an explicit stack, as chains
/// can be deeper than the call stack: a node's children in insertion order,
/// then the subtree of its last child first.
pub(super) struct WalkDown<'a> {
    state: &'a State,
    walk: Walk<'a>,
    links: Option<&'a Links>,
    pending: Vec<Node>,
    /// The children of the node being listed: the index's, then the
    /// overlay's links.
    listed: Option<indexmap::set::Iter<'a, Node>>,
    linked: Option<indexmap::set::Iter<'a, Node>>,
}

impl<'a> Iterator for WalkDown<'a> {
    type Item = Reached<'a>;

    fn next(&mut self) -> Option<Reached<'a>> {
        loop {
            let child = self
                .listed
                .as_mut()
                .and_then(Iterator::next)
                .or_else(|| self.linked.as_mut().and_then(Iterator::next));
            let Some(child) = child else {
                let at = self.pending.pop()?;
                self.listed = self.state.below.get(&at).map(IndexSet::iter);
                self.linked = self
                    .links
                    .and_then(|links| links.get(&at))
                    .map(IndexSet::iter);
                continue;
            };
            let id = match *child {
                Node::Conversation(_) => {
                    self.pending.push(*child);
                    continue;
                }
                Node::Task(id) => id,
            };
            let record = self
                .walk
                .overlay
                .and_then(|overlay| overlay.tasks.get(&id))
                .or_else(|| self.state.live.get(&id));
            let Some(node) = record
                .map(TaskNode::of)
                .or_else(|| self.state.settled.get(&id).copied())
            else {
                continue;
            };
            let enters = (self.walk.background == Background::Cross || !node.background)
                && self.walk.enter.is_none_or(|enter| enter(id));
            if enters {
                self.pending.push(*child);
            }
            return Some(Reached {
                id,
                node,
                live: record.filter(|record| is_live(record)),
            });
        }
    }
}

impl State {
    /// Owner edge of a conversation, with the overlay's staged edges first.
    pub(super) fn edge(&self, id: ConversationId, overlay: Option<&Overlay>) -> Edge {
        if let Some(owner) = overlay.and_then(|overlay| overlay.edges.get(&id)) {
            return Edge::Loaded(*owner);
        }
        self.edges
            .get(&id)
            .map_or(Edge::Unloaded, |owner| Edge::Loaded(*owner))
    }

    pub(super) fn node(&self, id: TaskId, overlay: Option<&Overlay>) -> Option<TaskNode> {
        overlay
            .and_then(|overlay| overlay.tasks.get(&id))
            .or_else(|| self.live.get(&id))
            .map(TaskNode::of)
            .or_else(|| self.settled.get(&id).copied())
    }

    /// The ownership fields of a known task, live or settled.
    pub(super) fn known_node(&self, id: TaskId) -> Option<TaskNode> {
        self.live
            .get(&id)
            .map(TaskNode::of)
            .or_else(|| self.settled.get(&id).copied())
    }

    pub(super) fn above<'a>(&'a self, start: Node, overlay: Option<&'a Overlay>) -> Above<'a> {
        Above {
            state: self,
            overlay,
            at: Some(start),
            unknown_next: false,
        }
    }

    /// Whether the chain above `node` is loaded, without walking: known tasks
    /// outside `unloaded` have a loaded chain.
    pub(super) fn known(&self, node: Node) -> bool {
        match node {
            Node::Task(id) => {
                (self.live.contains_key(&id) || self.settled.contains_key(&id))
                    && !self.unloaded.contains(&id)
            }
            Node::Conversation(id) => match self.edges.get(&id) {
                None => false,
                Some(None) => true,
                Some(Some(owner)) => self.known(Node::Task(*owner)),
            },
        }
    }

    /// A walk down from `start`. Under an overlay, it first derives, once per
    /// overlay, the links it needs for the commit's new tasks: each one under
    /// its parent node, then each node above it that `below` does not list
    /// yet, until one it lists, a live task (always listed), or the chain's
    /// end.
    pub(super) fn walk_down<'a>(&'a self, start: Node, walk: Walk<'a>) -> WalkDown<'a> {
        let links = walk.overlay.map(|overlay| {
            overlay.links.get_or_init(|| {
                let mut links = Links::new();
                for record in overlay.tasks.values() {
                    if self.live.contains_key(&record.id) || self.settled.contains_key(&record.id) {
                        continue;
                    }
                    let mut child = Node::Task(record.id);
                    let mut parent = Some(parent_of(record));
                    while let Some(at) = parent {
                        if !links.entry(at).or_default().insert(child) {
                            break;
                        }
                        let above = match at {
                            Node::Task(id) => {
                                if self.live.contains_key(&id) || overlay.tasks.contains_key(&id) {
                                    break;
                                }
                                self.settled.get(&id).map(TaskNode::parent)
                            }
                            Node::Conversation(id) => match self.edge(id, Some(overlay)) {
                                Edge::Loaded(owner) => owner.map(Node::Task),
                                Edge::Unloaded => None,
                            },
                        };
                        if above.is_some_and(|above| {
                            self.below
                                .get(&above)
                                .is_some_and(|children| children.contains(&at))
                        }) {
                            break;
                        }
                        child = at;
                        parent = above;
                    }
                }
                links
            })
        });
        WalkDown {
            state: self,
            walk,
            links,
            pending: vec![start],
            listed: None,
            linked: None,
        }
    }

    /// Whether `owner` has live ordinary owned work (spec §5.5), as the walk
    /// sees it: a live non-background task below it that a walk down reaches
    /// without entering a background task. Owner chains must be loaded.
    pub(super) fn has_owned_live(&self, owner: TaskId, walk: Walk<'_>) -> bool {
        self.walk_down(Node::Task(owner), walk)
            .any(|reached| reached.live.is_some() && !reached.node.background)
    }

    /// The nearest live task above ended ordinary work `node`, in the
    /// overlay's view: the one that work held, if any. Work at or below a
    /// background task holds nothing above it.
    pub(super) fn nearest_live_above<'a>(
        &'a self,
        node: TaskNode,
        overlay: Option<&'a Overlay>,
    ) -> Option<&'a AnyTaskRecord> {
        let mut current = node;
        while !current.background {
            let owner = match current.owner {
                Some(owner) => owner,
                None => match self.edge(current.conversation_id, overlay) {
                    Edge::Loaded(Some(owner)) => owner,
                    Edge::Loaded(None) | Edge::Unloaded => return None,
                },
            };
            let record = overlay
                .and_then(|overlay| overlay.tasks.get(&owner))
                .or_else(|| self.live.get(&owner));
            if let Some(record) = record.filter(|record| is_live(record)) {
                return Some(record);
            }
            current = match record {
                Some(record) => TaskNode::of(record),
                None => *self.settled.get(&owner)?,
            };
        }
        None
    }

    /// Whether ordinary traversal from `scope` reaches `start`: walking up
    /// reaches the scope's conversation, or an ownerless one for `Roots`,
    /// without crossing a background owner, unless `background` crosses.
    /// `None` while an edge is not loaded.
    pub(super) fn in_scope(
        &self,
        start: Node,
        scope: Scope,
        background: Background,
    ) -> Option<bool> {
        for step in self.above(start, None) {
            match step {
                Step::Unknown => return None,
                Step::Conversation(conversation) => {
                    if scope == Scope::Conversation(conversation) {
                        return Some(true);
                    }
                }
                Step::Task { node, .. } => {
                    if node.background && background == Background::Boundary {
                        return Some(false);
                    }
                }
            }
        }
        Some(scope == Scope::Roots)
    }

    /// Whether a live owner's cancellation intent reaches `start`: walking up
    /// finds an owner with intent before a background owner without it.
    /// Terminal owners never cascade (spec §5.4).
    pub(super) fn below_cancelled(&self, start: Node) -> bool {
        // Nothing cancels, the common case: no walk.
        if self.intent.is_empty() {
            return false;
        }
        for step in self.above(start, None) {
            match step {
                Step::Unknown => return false,
                Step::Conversation(_) => {}
                Step::Task { id, node } => {
                    if self.live.get(&id).is_some_and(cancellation_intent) {
                        return true;
                    }
                    if node.background {
                        return false;
                    }
                }
            }
        }
        false
    }

    /// No live non-background task in the scope; a task whose owner edges are
    /// not loaded yet counts as inside.
    pub(super) fn idle(&self, conversation_id: Option<ConversationId>) -> bool {
        let scope = conversation_id.map_or(Scope::Roots, Scope::Conversation);
        // Tasks whose chain is not loaded are not listed below their scope
        // yet; one counts as inside unless its walk up decides otherwise.
        let outside = |id: &TaskId| {
            self.live.get(id).is_none_or(|record| {
                record.background
                    || self.in_scope(parent_of(record), scope, Background::Boundary) == Some(false)
            })
        };
        if !self.unloaded.iter().all(outside) {
            return false;
        }
        let busy = |start: ConversationId| {
            self.walk_down(Node::Conversation(start), Walk::default())
                .any(|reached| reached.live.is_some() && !reached.node.background)
        };
        match conversation_id {
            Some(id) => !busy(id),
            None => !self.roots.iter().any(|root| busy(*root)),
        }
    }
}

/// Whether a candidate record is still live (not terminal).
pub(super) fn is_live(record: &AnyTaskRecord) -> bool {
    !matches!(record.state, TaskState::Terminal { .. })
}

/// A live owner's durable cancellation intent: its abort mark, or a held
/// outcome other than `completed`.
pub(super) fn cancellation_intent(record: &AnyTaskRecord) -> bool {
    is_live(record) && (record.abort_requested || failed_outcome(record))
}

/// Whether the record holds or ends with an outcome other than `completed`.
pub(super) fn failed_outcome(record: &AnyTaskRecord) -> bool {
    record
        .state
        .outcome()
        .is_some_and(|outcome| outcome.status() != crate::types::TaskOutcomeStatus::Completed)
}
