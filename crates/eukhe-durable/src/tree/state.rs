//! The state tree of a session: the session tree whose nodes are the
//! records of the storage. It is derived from the commit stream: each
//! commit becomes `Do` records of the journal.
//!
//! The tree:
//! - a conversation hangs under the conversation of the task that owns
//!   it, else under the conversation it forks from, else under the root;
//! - an entry, a task and a submission hang under their conversation;
//! - a document hangs under its scope: the root (a session document), its
//!   conversation, or the conversation of its task.
//!
//! The parent of each node is a conversation or the root, and a
//! conversation is never deleted: a stored history that drops the early
//! states of a terminal task still gives every node its parent.
//!
//! Ids go to the keys in the order the tree first sees them, so a parent
//! always has a smaller id than its children. The ids and the cursor hold
//! for one tree only: a tree built again from a stored history can see
//! the records in another order, because the history keeps no early state
//! of a terminal task.
//!
//! A node value is the record as JSON for a conversation, a task and a
//! submission. An entry and a document keep a reference only (an entry
//! is immutable; the storage holds the content of a document at each
//! commit): an entry keeps its kind, conversation, head and task; a
//! document keeps its kind, key, scope, the commit that created it, and
//! the commit that last changed it.

use std::collections::HashMap;
use std::fmt;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::sync::Arc;

use serde::{Deserialize, Serialize};
use serde_json::{json, Value};

use super::{Applied, CoreError, Journal, NodeId, RewindEffect, SessionTree, TreeOp, TreeRecord};
use crate::storage::jsonl::HistoryCommit;
use crate::types::{
    AnyTaskRecord, CommitChange, CommitPublication, ConversationRecord, DocumentCommitChange,
    DocumentRecordScope, EntryRecord, Seq, StorageWrite, SubmissionRecord,
};

/// The kind of a state node: the storage table of its record.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum StateKind {
    /// A conversation.
    Conversation,
    /// A transcript entry.
    Entry,
    /// A durable task.
    Task,
    /// A submission.
    Submission,
    /// A document incarnation.
    Document,
}

impl StateKind {
    /// The name: `conversation`, `entry`, `task`, `submission`, or `document`.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Self::Conversation => "conversation",
            Self::Entry => "entry",
            Self::Task => "task",
            Self::Submission => "submission",
            Self::Document => "document",
        }
    }
}

impl fmt::Display for StateKind {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.name())
    }
}

/// The storage identity of a state node: its kind and its record id.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(tag = "kind", content = "id", rename_all = "snake_case")]
pub enum StateKey {
    /// A conversation id.
    Conversation(String),
    /// An entry id.
    Entry(String),
    /// A task id.
    Task(String),
    /// A submission id.
    Submission(String),
    /// A document incarnation id.
    Document(String),
}

impl StateKey {
    /// The kind of the record.
    #[must_use]
    pub fn kind(&self) -> StateKind {
        match self {
            Self::Conversation(_) => StateKind::Conversation,
            Self::Entry(_) => StateKind::Entry,
            Self::Task(_) => StateKind::Task,
            Self::Submission(_) => StateKind::Submission,
            Self::Document(_) => StateKind::Document,
        }
    }

    /// The record id.
    #[must_use]
    pub fn id(&self) -> &str {
        match self {
            Self::Conversation(id)
            | Self::Entry(id)
            | Self::Task(id)
            | Self::Submission(id)
            | Self::Document(id) => id,
        }
    }
}

impl fmt::Display for StateKey {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{} {}", self.kind(), self.id())
    }
}

/// The value of a state node. Two nodes are equal when their contents are
/// equal; a clone shares the JSON value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StateNode {
    /// The kind of the record.
    pub kind: StateKind,
    /// The record as JSON (see the module documentation).
    pub value: Arc<Value>,
}

/// Equal nodes hash the same: JSON objects are equal whatever the order of
/// their keys, so an object hashes its entries in any order.
impl Hash for StateNode {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.kind.hash(state);
        hash_json(&self.value, state);
    }
}

fn hash_json<H: Hasher>(value: &Value, state: &mut H) {
    match value {
        Value::Null => 0u8.hash(state),
        Value::Bool(b) => (1u8, b).hash(state),
        Value::Number(n) => (2u8, n).hash(state),
        Value::String(s) => (3u8, s).hash(state),
        Value::Array(items) => {
            (4u8, items.len()).hash(state);
            for item in items {
                hash_json(item, state);
            }
        }
        Value::Object(map) => {
            let entries = map.iter().fold(0u64, |sum, (key, item)| {
                let mut entry = DefaultHasher::new();
                key.hash(&mut entry);
                hash_json(item, &mut entry);
                sum.wrapping_add(entry.finish())
            });
            (5u8, map.len(), entries).hash(state);
        }
    }
}

/// A change of a commit that the state tree cannot record.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum StateError {
    /// The parent of the record is not in the tree.
    #[error("commit {seq}: {key} hangs under {parent}, which the state tree does not have")]
    UnknownParent {
        /// The commit.
        seq: Seq,
        /// The record.
        key: StateKey,
        /// Its parent.
        parent: StateKey,
    },
    /// The commit changes or retires a document that is not in the tree.
    #[error("commit {seq}: {key} is not in the state tree")]
    UnknownNode {
        /// The commit.
        seq: Seq,
        /// The record.
        key: StateKey,
    },
}

/// A client cursor that is more than the cursor of the tree.
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
#[error("cursor {cursor} is ahead of the state tree cursor {current}")]
pub struct CursorAhead {
    /// The cursor asked for.
    pub cursor: usize,
    /// The cursor of the tree.
    pub current: usize,
}

/// A question about the tree at a cursor that the tree cannot answer.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum CursorError {
    /// The cursor is more than the cursor of the tree.
    #[error(transparent)]
    Ahead(#[from] CursorAhead),
    /// The tree core answered something the journal cannot read.
    #[error(transparent)]
    Core(#[from] CoreError),
}

/// One planned change of a commit, before the ids are known.
enum Planned {
    Put {
        key: StateKey,
        /// `None`: the root.
        parent: Option<StateKey>,
        node: StateNode,
    },
    Del {
        key: StateKey,
    },
}

/// The state tree of a session: the journal of [`StateNode`] records, the
/// keys of the node ids, and the last commit it recorded.
#[derive(Clone, Debug, Default)]
pub struct StateTree {
    journal: Journal<StateNode>,
    ids: HashMap<StateKey, NodeId>,
    /// `keys[n - 1]` is the key of `NodeId(n)`.
    keys: Vec<StateKey>,
    seq: Option<Seq>,
    /// The conversation of each task the tree knows: the parent of a task
    /// document in a storage write.
    task_conversations: HashMap<String, String>,
}

impl StateTree {
    /// An empty state tree.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Record one published commit. A commit at or before [`Self::seq`]
    /// is already in the tree: it records nothing and returns no result.
    /// Otherwise the result has one item per change that the tree takes:
    /// a change whose parent or node is not in the tree is a
    /// [`StateError`] and does not change the tree.
    pub fn record(&mut self, publication: &CommitPublication) -> Vec<Result<Applied, StateError>> {
        let seq = publication.seq;
        if self.seq.is_some_and(|last| seq <= last) {
            return Vec::new();
        }
        let mut planned = Vec::with_capacity(publication.changes.len());
        for change in &publication.changes {
            planned.push(match change {
                CommitChange::Conversation(record) => conversation_put(record),
                CommitChange::Entry(record) => entry_put(record),
                CommitChange::Task(record) => self.task_put(record),
                CommitChange::Submission(record) => submission_put(record),
                CommitChange::Document(DocumentCommitChange::Document {
                    record,
                    conversation_id,
                    ..
                }) => {
                    let key = StateKey::Document(record.id.to_string());
                    if record.retired_at.is_some() {
                        Planned::Del { key }
                    } else {
                        document_put(
                            key,
                            conversation_id.map(|id| StateKey::Conversation(id.to_string())),
                            &record.kind,
                            record.key.as_deref(),
                            record.scope,
                            record.created_at,
                            seq,
                        )
                    }
                }
                CommitChange::Document(DocumentCommitChange::Copy {
                    record,
                    conversation_id,
                    ..
                }) => document_put(
                    StateKey::Document(record.id.to_string()),
                    Some(StateKey::Conversation(conversation_id.to_string())),
                    &record.kind,
                    record.key.as_deref(),
                    record.scope,
                    record.created_at,
                    seq,
                ),
            });
        }
        self.apply_commit(seq, planned)
    }

    /// The tree of a stored history ([`JsonlStorage::take_history`]), in
    /// sequence order, with the result of each change. It first learns the
    /// conversation of every task in the history: a task document can come
    /// before the first stored state of its task.
    ///
    /// [`JsonlStorage::take_history`]: crate::storage::jsonl::JsonlStorage::take_history
    #[must_use]
    pub fn from_history(history: &[HistoryCommit]) -> (Self, Vec<Result<Applied, StateError>>) {
        let mut tree = Self::new();
        for write in history.iter().flat_map(|commit| &commit.writes) {
            if let StorageWrite::Task { value } = write {
                tree.task_conversations
                    .insert(value.id.to_string(), value.conversation_id.to_string());
            }
        }
        let results = history
            .iter()
            .flat_map(|commit| tree.record_writes(commit.seq, &commit.writes))
            .collect();
        (tree, results)
    }

    /// Record one commit from its storage writes. The same commit makes the
    /// same nodes as [`Self::record`] with its publication; the same rules
    /// apply. A task document hangs under the conversation of its task,
    /// which the tree knows from a task write before it, or from
    /// [`Self::from_history`].
    pub fn record_writes(
        &mut self,
        seq: Seq,
        writes: &[StorageWrite],
    ) -> Vec<Result<Applied, StateError>> {
        if self.seq.is_some_and(|last| seq <= last) {
            return Vec::new();
        }
        let mut planned = Vec::with_capacity(writes.len());
        let mut unknown = Vec::new();
        for write in writes {
            planned.push(match write {
                StorageWrite::Conversation { value } => conversation_put(value),
                StorageWrite::Entry { value } => entry_put(value),
                StorageWrite::Task { value } => self.task_put(value),
                StorageWrite::Submission { value } => submission_put(value),
                StorageWrite::DocumentCreate { record, .. }
                | StorageWrite::DocumentCopy { record, .. } => document_put(
                    StateKey::Document(record.id.to_string()),
                    match record.scope {
                        DocumentRecordScope::Session => None,
                        DocumentRecordScope::Conversation {
                            conversation_id, ..
                        } => Some(StateKey::Conversation(conversation_id.to_string())),
                        // An unknown task stays the parent: the put fails as
                        // an unknown parent.
                        DocumentRecordScope::Task { task_id } => {
                            let task = task_id.to_string();
                            Some(match self.task_conversations.get(&task) {
                                Some(conversation) => StateKey::Conversation(conversation.clone()),
                                None => StateKey::Task(task),
                            })
                        }
                    },
                    &record.kind,
                    record.key.as_deref(),
                    record.scope,
                    seq,
                    seq,
                ),
                StorageWrite::DocumentChange { id, .. } => {
                    // The node as an earlier write of this commit or the
                    // tree has it, changed at `seq`.
                    let key = StateKey::Document(id.to_string());
                    let earlier = planned.iter().rev().find_map(|plan| match plan {
                        Planned::Put {
                            key: planned_key,
                            parent,
                            node,
                        } if *planned_key == key => Some((parent.clone(), node.clone())),
                        Planned::Put { .. } | Planned::Del { .. } => None,
                    });
                    let current = earlier.or_else(|| {
                        let node = self.journal.tree().get(*self.ids.get(&key)?)?;
                        let parent = match node.parent {
                            NodeId::ROOT => None,
                            parent => Some(self.key(parent)?.clone()),
                        };
                        Some((parent, node.value.clone()))
                    });
                    let Some((parent, node)) = current else {
                        unknown.push(StateError::UnknownNode { seq, key });
                        continue;
                    };
                    let mut value = (*node.value).clone();
                    value["changedAt"] = json!(seq);
                    Planned::Put {
                        key,
                        parent,
                        node: StateNode {
                            kind: node.kind,
                            value: Arc::new(value),
                        },
                    }
                }
                StorageWrite::DocumentRetire { id } => Planned::Del {
                    key: StateKey::Document(id.to_string()),
                },
            });
        }
        let mut results = self.apply_commit(seq, planned);
        results.extend(unknown.into_iter().map(Err));
        results
    }

    /// Apply the planned changes of one commit. The changes of a commit
    /// come in no order: a `Put` waits until its parent is in the tree,
    /// and the `Del`s come last (a commit retires a document after its
    /// content).
    fn apply_commit(
        &mut self,
        seq: Seq,
        planned: Vec<Planned>,
    ) -> Vec<Result<Applied, StateError>> {
        let mut results = Vec::with_capacity(planned.len());
        let mut puts = Vec::new();
        let mut dels = Vec::new();
        for plan in planned {
            match plan {
                Planned::Put { key, parent, node } => puts.push((key, parent, node)),
                Planned::Del { key } => dels.push(key),
            }
        }
        loop {
            let before = puts.len();
            let mut waiting = Vec::new();
            for (key, parent, node) in puts {
                let parent_id = match &parent {
                    None => Some(NodeId::ROOT),
                    Some(parent) => self
                        .ids
                        .get(parent)
                        .copied()
                        .filter(|id| self.journal.tree().contains(*id)),
                };
                match parent_id {
                    Some(parent_id) => {
                        // A new key takes the next id.
                        let keys = &mut self.keys;
                        let id = *self.ids.entry(key).or_insert_with_key(|key| {
                            keys.push(key.clone());
                            NodeId(keys.len() as u64)
                        });
                        results.push(Ok(self.journal.push(TreeRecord::Do(TreeOp::Put {
                            id,
                            parent: parent_id,
                            value: node,
                        }))));
                    }
                    None => waiting.push((key, parent, node)),
                }
            }
            puts = waiting;
            if puts.is_empty() || puts.len() == before {
                break;
            }
        }
        for (key, parent, _) in puts {
            if let Some(parent) = parent {
                results.push(Err(StateError::UnknownParent { seq, key, parent }));
            }
        }
        for key in dels {
            match self.ids.get(&key).copied() {
                Some(id) if self.journal.tree().contains(id) => {
                    results.push(Ok(self.journal.push(TreeRecord::Do(TreeOp::Del { id }))));
                }
                Some(_) | None => results.push(Err(StateError::UnknownNode { seq, key })),
            }
        }
        self.seq = Some(seq);
        results
    }

    /// The live tree.
    #[must_use]
    pub fn tree(&self) -> &SessionTree<StateNode> {
        self.journal.tree()
    }

    /// The number of records: the cursor after the last record.
    #[must_use]
    pub fn cursor(&self) -> usize {
        self.journal.records().len()
    }

    /// The last commit the tree recorded.
    #[must_use]
    pub fn seq(&self) -> Option<Seq> {
        self.seq
    }

    /// The storage key of node `id`.
    #[must_use]
    pub fn key(&self, id: NodeId) -> Option<&StateKey> {
        let index = usize::try_from(id.0).ok()?.checked_sub(1)?;
        self.keys.get(index)
    }

    /// The records after the first `cursor`.
    ///
    /// # Errors
    /// The cursor is more than [`Self::cursor`].
    pub fn records_since(&self, cursor: usize) -> Result<&[TreeRecord<StateNode>], CursorAhead> {
        self.journal
            .records()
            .get(cursor..)
            .ok_or_else(|| self.ahead(cursor))
    }

    /// The tree after the first `cursor` records.
    ///
    /// # Errors
    /// The cursor is more than [`Self::cursor`], or the tree core answered
    /// something the journal cannot read.
    pub fn snapshot_at(&self, cursor: usize) -> Result<SessionTree<StateNode>, CursorError> {
        if cursor > self.cursor() {
            return Err(self.ahead(cursor).into());
        }
        Ok(self.journal.snapshot_at(cursor)?)
    }

    /// What a rewind from the live tree to the snapshot at `cursor` does.
    ///
    /// # Errors
    /// The cursor is more than [`Self::cursor`].
    pub fn rewind_plan(&self, cursor: usize) -> Result<Vec<RewindEffect>, CursorError> {
        if cursor > self.cursor() {
            return Err(self.ahead(cursor).into());
        }
        Ok(self.journal.rewind_plan(cursor))
    }

    fn ahead(&self, cursor: usize) -> CursorAhead {
        CursorAhead {
            cursor,
            current: self.cursor(),
        }
    }

    /// The `Put` of a task, which the tree learns the conversation of.
    fn task_put(&mut self, record: &AnyTaskRecord) -> Planned {
        let conversation = record.conversation_id.to_string();
        self.task_conversations
            .insert(record.id.to_string(), conversation.clone());
        Planned::Put {
            key: StateKey::Task(record.id.to_string()),
            parent: Some(StateKey::Conversation(conversation)),
            node: record_node(StateKind::Task, record),
        }
    }
}

fn record_node(kind: StateKind, record: &impl Serialize) -> StateNode {
    StateNode {
        kind,
        // The storage records serialize to JSON; a failure has no record to show.
        value: Arc::new(serde_json::to_value(record).unwrap_or(Value::Null)),
    }
}

fn submission_put(record: &SubmissionRecord) -> Planned {
    Planned::Put {
        key: StateKey::Submission(record.id.to_string()),
        parent: Some(StateKey::Conversation(record.conversation_id.to_string())),
        node: record_node(StateKind::Submission, record),
    }
}

fn conversation_put(record: &ConversationRecord) -> Planned {
    Planned::Put {
        key: StateKey::Conversation(record.id.to_string()),
        parent: record
            .owner
            .map(|owner| owner.conversation_id)
            .or(record.parent.map(|parent| parent.conversation_id))
            .map(|id| StateKey::Conversation(id.to_string())),
        node: record_node(StateKind::Conversation, record),
    }
}

fn entry_put(record: &EntryRecord) -> Planned {
    Planned::Put {
        key: StateKey::Entry(record.id.to_string()),
        parent: Some(StateKey::Conversation(record.conversation_id.to_string())),
        node: StateNode {
            kind: StateKind::Entry,
            value: Arc::new(json!({
                "kind": record.kind,
                "conversationId": record.conversation_id,
                "head": record.head,
                "byTaskId": record.by_task_id,
            })),
        },
    }
}

/// The `Put` of a document under `parent` (`None`: the root).
fn document_put(
    key: StateKey,
    parent: Option<StateKey>,
    kind: &str,
    document_key: Option<&str>,
    scope: DocumentRecordScope,
    created_at: Seq,
    changed_at: Seq,
) -> Planned {
    Planned::Put {
        key,
        parent,
        node: StateNode {
            kind: StateKind::Document,
            value: Arc::new(json!({
                "kind": kind,
                "key": document_key,
                "scope": scope.scope().name(),
                "createdAt": created_at,
                "changedAt": changed_at,
            })),
        },
    }
}

#[cfg(test)]
#[path = "state_tests.rs"]
mod tests;
