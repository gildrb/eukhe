//! The ownership tree of tasks and conversations (spec §5.5) and the walks up
//! it that decide cascades, idle scopes, and live ordinary owned work.
//!
//! A task's parent is its owner task, or its conversation; a conversation's
//! parent is its owner task, if any.

use std::collections::HashMap;

use indexmap::IndexMap;

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

    /// Where a walk up from this task continues.
    pub(super) fn parent(&self) -> Up {
        match self.owner {
            Some(owner) => Up::Task(owner),
            None => Up::Conversation(self.conversation_id),
        }
    }
}

/// The parent of a record in the ownership tree.
pub(super) fn parent_of(record: &AnyTaskRecord) -> Up {
    TaskNode::of(record).parent()
}

/// Where a walk up the ownership tree continues: an owner task, or a conversation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Up {
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

/// Candidate records a commit staged; they override committed records in
/// ownership walks.
#[derive(Default)]
pub(super) struct Overlay {
    /// Staged task records in staging order.
    pub(super) tasks: IndexMap<TaskId, AnyTaskRecord>,
    /// Owner edges of staged conversations; `None` when ownerless.
    pub(super) edges: HashMap<ConversationId, Option<TaskId>>,
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
        Self { tasks, edges }
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
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Background {
    /// Ordinary traversal: a background owner is a boundary.
    Boundary,
    /// Traversal ignoring the background flag.
    Cross,
}

/// Walk up from a start: owner tasks and conversations, ending at an
/// ownerless root or an edge not loaded yet.
pub(super) struct Above<'a> {
    state: &'a State,
    overlay: Option<&'a Overlay>,
    at: Option<Up>,
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
            Up::Task(id) => {
                let Some(node) = self.state.node(id, self.overlay) else {
                    self.at = None;
                    return Some(Step::Unknown);
                };
                self.at = Some(node.parent());
                Some(Step::Task { id, node })
            }
            Up::Conversation(conversation) => {
                match self.state.edge(conversation, self.overlay) {
                    Edge::Unloaded => self.unknown_next = true,
                    Edge::Loaded(owner) => self.at = owner.map(Up::Task),
                }
                Some(Step::Conversation(conversation))
            }
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

    pub(super) fn set_edge(&mut self, conversation_id: ConversationId, owner: Option<TaskId>) {
        self.edges.insert(conversation_id, owner);
        if let Some(owner) = owner {
            self.conversation_owners.insert(owner);
        }
    }

    pub(super) fn above<'a>(&'a self, start: Up, overlay: Option<&'a Overlay>) -> Above<'a> {
        Above {
            state: self,
            overlay,
            at: Some(start),
            unknown_next: false,
        }
    }

    /// Whether every owner above `start` is loaded.
    pub(super) fn chain_known(&self, start: Up, overlay: Option<&Overlay>) -> bool {
        !self
            .above(start, overlay)
            .any(|step| matches!(step, Step::Unknown))
    }

    /// Live records, with the overlay's candidates replacing committed ones;
    /// terminal candidates are gone.
    pub(super) fn live_records<'a>(
        &'a self,
        overlay: Option<&'a Overlay>,
    ) -> impl Iterator<Item = &'a AnyTaskRecord> + 'a {
        let committed = self.live.values().filter_map(move |record| {
            let candidate = overlay
                .and_then(|overlay| overlay.tasks.get(&record.id))
                .unwrap_or(record);
            is_live(candidate).then_some(candidate)
        });
        let staged = overlay.into_iter().flat_map(move |overlay| {
            overlay
                .tasks
                .values()
                .filter(move |record| !self.live.contains_key(&record.id) && is_live(record))
        });
        committed.chain(staged)
    }

    /// Every task with live ordinary owned work (spec §5.5), mapped to that
    /// work: each live non-background task counts for every owner task above
    /// it up to and including the first background one. Owner chains must be
    /// loaded.
    pub(super) fn owned_live(&self, overlay: Option<&Overlay>) -> IndexMap<TaskId, Vec<TaskId>> {
        let mut owned: IndexMap<TaskId, Vec<TaskId>> = IndexMap::new();
        for record in self.live_records(overlay) {
            if record.background {
                continue;
            }
            for step in self.above(parent_of(record), overlay) {
                match step {
                    Step::Unknown => break,
                    Step::Conversation(_) => {}
                    Step::Task { id, node } => {
                        owned.entry(id).or_default().push(record.id);
                        if node.background {
                            break;
                        }
                    }
                }
            }
        }
        owned
    }

    /// Whether ordinary traversal from `scope` reaches `start`: walking up
    /// reaches the scope's conversation, or an ownerless one for `Roots`,
    /// without crossing a background owner, unless `background` crosses.
    /// `None` while an edge is not loaded.
    pub(super) fn in_scope(&self, start: Up, scope: Scope, background: Background) -> Option<bool> {
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
    pub(super) fn below_cancelled(&self, start: Up) -> bool {
        self.cancelling_owner(start).is_some()
    }

    /// The nearest live owner above `start` whose cancellation intent reaches
    /// it, if any; see [`Self::below_cancelled`].
    pub(super) fn cancelling_owner(&self, start: Up) -> Option<&AnyTaskRecord> {
        for step in self.above(start, None) {
            match step {
                Step::Unknown => return None,
                Step::Conversation(_) => {}
                Step::Task { id, node } => {
                    if let Some(live) = self.live.get(&id).filter(|live| cancellation_intent(live))
                    {
                        return Some(live);
                    }
                    if node.background {
                        return None;
                    }
                }
            }
        }
        None
    }

    /// No live non-background task in the scope; a task whose owner edges are
    /// not loaded yet counts as inside.
    pub(super) fn idle(&self, conversation_id: Option<ConversationId>) -> bool {
        let scope = conversation_id.map_or(Scope::Roots, Scope::Conversation);
        !self.live.values().any(|record| {
            !record.background
                && self.in_scope(parent_of(record), scope, Background::Boundary) != Some(false)
        })
    }
}

/// Whether a candidate record is still live (not terminal).
fn is_live(record: &AnyTaskRecord) -> bool {
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
