//! Upkeep of the ownership index and the candidate sets: each committed task
//! record updates them, chain loads install known nodes, and a sweep drops
//! the nodes no live work hangs below any more.

use crate::types::{AnyTaskRecord, ConversationId, TaskId, TaskState, TaskStatus};

use super::ownership::{cancellation_intent, parent_of, Node, TaskNode};
use super::state::State;

impl State {
    /// Bring the scheduler's sets in line with a task's committed record;
    /// returns the record it replaces in the live mirror. A task that ended
    /// may free the nearest live task above it: one holding its outcome
    /// finalizes, an abort-marked one runs its abort handler; its waiters may
    /// run.
    pub(super) fn track(&mut self, record: &AnyTaskRecord) -> Option<AnyTaskRecord> {
        let id = record.id;
        if record.state.status() == TaskStatus::Terminal {
            let previous = self.live.shift_remove(&id);
            if let Some(previous) = &previous {
                self.unwait(previous);
            }
            self.intent.shift_remove(&id);
            self.runnable.shift_remove(&id);
            self.finalize_checks.shift_remove(&id);
            let node = TaskNode::of(record);
            self.settled.insert(id, node);
            // The nearest live task above ended ordinary work may be free
            // now: one holding its outcome, or an aborting one. Found before
            // anything is forgotten: the walk up to the task it held passes
            // the ended tasks between them. Its chain is loaded, as every
            // commit that ends a task loads the chains of `unloaded` first.
            let above = self.nearest_live_above(node, None).map(|above| {
                (
                    above.id,
                    above.state.status() == TaskStatus::Completing,
                    above.abort_requested,
                )
            });
            match above {
                Some((above, true, _)) => {
                    self.finalize_checks.insert(above);
                }
                Some((above, false, true)) => {
                    self.runnable.insert(above);
                }
                Some((_, false, false)) | None => {}
            }
            if let Some(waiters) = self.waiters.get(&id) {
                self.runnable.extend(waiters.iter().copied());
            }
            self.relist(Node::Task(id));
            self.drop_if_unneeded(Node::Task(id));
            return previous;
        }
        let previous = self.live.insert(id, record.clone());
        if let Some(previous) = &previous {
            self.unwait(previous);
        } else {
            if !self.known(parent_of(record)) {
                self.unloaded.insert(id);
            }
            self.relist(Node::Task(id));
        }
        if cancellation_intent(record) {
            self.intent.insert(id);
        } else {
            self.intent.shift_remove(&id);
        }
        if record.state.status() == TaskStatus::Completing {
            self.runnable.shift_remove(&id);
            self.finalize_checks.insert(id);
        } else {
            self.runnable.insert(id);
        }
        if let TaskState::Waiting { on, .. } = &record.state {
            for member in on {
                self.waiters.entry(*member).or_default().insert(id);
            }
        }
        previous
    }

    /// Drop a replaced waiting record from `waiters`.
    fn unwait(&mut self, previous: &AnyTaskRecord) {
        let TaskState::Waiting { on, .. } = &previous.state else {
            return;
        };
        for member in on {
            if let Some(waiters) = self.waiters.get_mut(member) {
                waiters.shift_remove(&previous.id);
                if waiters.is_empty() {
                    self.waiters.remove(member);
                }
            }
        }
    }

    /// List `start` under its parent node in `below` while it is a live task
    /// or has nodes listed below it, and unlist it otherwise; then its parent,
    /// as far up as that changes. So `below` holds exactly the tree around
    /// live work; a parent that loses its last listed node is queued for the
    /// sweep. A loop, as ownership chains can be deeper than the call stack.
    pub(super) fn relist(&mut self, start: Node) {
        let mut node = start;
        loop {
            let needed = self.listable(node);
            let parent = match node {
                Node::Conversation(id) => match self.edges.get(&id) {
                    None => return,
                    Some(None) => {
                        if needed {
                            self.roots.insert(id);
                        } else {
                            self.roots.remove(&id);
                        }
                        return;
                    }
                    Some(Some(owner)) => Node::Task(*owner),
                },
                Node::Task(id) => match self.known_node(id) {
                    None => return,
                    Some(known) => known.parent(),
                },
            };
            let listed = self
                .below
                .get(&parent)
                .is_some_and(|children| children.contains(&node));
            if listed == needed {
                return;
            }
            if needed {
                let first = !self.below.contains_key(&parent);
                self.below.entry(parent).or_default().insert(node);
                if !first {
                    return;
                }
            } else {
                if let Some(children) = self.below.get_mut(&parent) {
                    children.shift_remove(&node);
                    if !children.is_empty() {
                        return;
                    }
                    self.below.remove(&parent);
                }
                self.drop_if_unneeded(parent);
            }
            node = parent;
        }
    }

    /// Whether `node` belongs in `below`: a live task, or a node with nodes
    /// listed below it.
    fn listable(&self, node: Node) -> bool {
        matches!(node, Node::Task(id) if self.live.contains_key(&id))
            || self.below.contains_key(&node)
    }

    /// Know a conversation's owner edge; the conversation now hangs from its
    /// owner, or is a root. With nothing below it, it waits for the sweep.
    pub(super) fn set_edge(&mut self, conversation_id: ConversationId, owner: Option<TaskId>) {
        self.edges.insert(conversation_id, owner);
        let node = Node::Conversation(conversation_id);
        self.relist(node);
        self.drop_if_unneeded(node);
    }

    /// Queue an ended task or a conversation for the sweep when nothing is
    /// listed below it.
    pub(super) fn drop_if_unneeded(&mut self, node: Node) {
        if !self.listable(node) {
            self.drop_queue.insert(node);
        }
    }

    /// Drop the queued nodes that are still unneeded: not live, nothing
    /// listed below. Runs once a publication is fully tracked, and as a job
    /// of its own on the line, never inside an operation: work a commit
    /// creates below a chain its own callback loaded keeps that chain. A flat
    /// loop: unlisting already queued every node on the way up that lost its
    /// last listed node.
    pub(super) fn sweep(&mut self) {
        for node in self.drop_queue.drain() {
            if self.below.contains_key(&node) {
                continue;
            }
            match node {
                Node::Conversation(id) => {
                    self.edges.remove(&id);
                    self.roots.remove(&id);
                }
                Node::Task(id) => {
                    if !self.live.contains_key(&id) {
                        self.settled.remove(&id);
                        self.unloaded.shift_remove(&id);
                    }
                }
            }
        }
    }
}
