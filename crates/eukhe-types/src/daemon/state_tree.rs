//! The session state tree on the wire (Rust-native, advertised by the
//! [`STATE_TREE_CAPABILITY`] server capability): the `get_state_tree`
//! reply (the whole tree, or the records after a client cursor), the
//! `get_state_rewind_plan` reply, and the `state_tree_update` frame.
//!
//! Only a connection that sent `subscribe_state_tree` gets the frame. The
//! subscription starts before the worker reads the tree for the reply, so
//! the frames after the reply cover every record after its cursor. A frame
//! can also hold records the reply already had: a client skips a frame
//! whose `cursor` is not more than its own, and applies the records of
//! the others from its own cursor (`records[mine - from..]`).
//!
//! The worker derives the tree from the commits of the session storage:
//! each node is one stored record (a conversation, an entry, a task, a
//! submission, or a document). A cursor counts the records of the tree.

use serde::{Deserialize, Serialize};
use serde_json::Value;

/// The server capability that advertises `get_state_tree`,
/// `subscribe_state_tree`, `unsubscribe_state_tree`,
/// `get_state_rewind_plan` and the `state_tree_update` frame.
pub const STATE_TREE_CAPABILITY: &str = "state_tree";

/// The storage table of a node.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum StateTreeKind {
    Conversation,
    Entry,
    Task,
    Submission,
    Document,
}

impl StateTreeKind {
    /// The wire name.
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

/// One node of the tree.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct StateTreeNode {
    /// The node id; more than the id of its parent.
    pub id: u64,
    /// The parent id; `0` is the root, which is not a node.
    pub parent: u64,
    pub kind: StateTreeKind,
    /// The id of the stored record.
    pub key: String,
    /// The record as JSON (a reference only for an entry or a document).
    pub value: Value,
}

/// One change of the tree.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "op", rename_all = "snake_case")]
pub enum StateTreeOp {
    /// Set the node: insert it, or replace the node with its id.
    Put(StateTreeNode),
    /// Remove the node (in a `do` record, also every node below it).
    Del { id: u64 },
}

/// One record of the tree.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "record", content = "body", rename_all = "snake_case")]
pub enum StateTreeRecord {
    /// One checked change.
    Do(StateTreeOp),
    /// Exact changes, in order, back to an earlier tree.
    Rewind(Vec<StateTreeOp>),
}

/// The whole tree at one cursor.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct StateTreeSnapshot {
    /// The number of records the tree has.
    pub cursor: u64,
    /// The last commit the tree recorded; `None` before the first.
    #[serde(default)]
    pub seq: Option<u64>,
    /// The nodes, in id order.
    pub nodes: Vec<StateTreeNode>,
}

/// The records after a cursor.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct StateTreeRecords {
    /// The cursor before the first record.
    pub from: u64,
    /// The cursor after the last record.
    pub cursor: u64,
    pub records: Vec<StateTreeRecord>,
}

/// The `get_state_tree` response data: the snapshot without `since`, the
/// records after `since` with it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "mode", rename_all = "snake_case")]
pub enum StateTreeReply {
    Snapshot(StateTreeSnapshot),
    Records(StateTreeRecords),
}

/// A node that a rewind touches.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct StateTreeNodeRef {
    pub id: u64,
    pub kind: StateTreeKind,
    /// The id of the stored record.
    pub key: String,
}

/// What a rewind does to the work of one node.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "effect", rename_all = "snake_case")]
pub enum StateTreeEffect {
    /// The node is new: start its work.
    Start(StateTreeNodeRef),
    /// The node goes: stop its work.
    Stop(StateTreeNodeRef),
    /// The node changes: restore its earlier state.
    Restore(StateTreeNodeRef),
}

/// The `get_state_rewind_plan` response data: the effects of a rewind
/// from the live tree to the tree at `target`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct StateRewindPlanReply {
    /// The cursor of the live tree.
    pub cursor: u64,
    /// The cursor of the target tree.
    pub target: u64,
    /// In order: the stops first, then the starts and restores.
    pub effects: Vec<StateTreeEffect>,
}

#[cfg(test)]
mod tests {
    use super::super::rt;

    #[test]
    fn state_tree_replies_roundtrip() {
        rt::<super::StateTreeReply>(
            r#"{"mode":"snapshot","cursor":2,"seq":5,"nodes":[{"id":1,"parent":0,"kind":"conversation","key":"1","value":{"id":1}}]}"#,
        );
        rt::<super::StateTreeReply>(
            r#"{"mode":"records","from":1,"cursor":3,"records":[{"record":"do","body":{"op":"put","id":2,"parent":1,"kind":"entry","key":"3","value":{"kind":"pi.user"}}},{"record":"do","body":{"op":"del","id":2}}]}"#,
        );
        rt::<super::super::DaemonOutbound>(
            r#"{"type":"state_tree_update","activeSessionId":"s1","update":{"from":3,"cursor":4,"records":[{"record":"do","body":{"op":"del","id":2}}]}}"#,
        );
        rt::<super::StateRewindPlanReply>(
            r#"{"cursor":3,"target":1,"effects":[{"effect":"stop","id":2,"kind":"task","key":"4"},{"effect":"restore","id":1,"kind":"document","key":"6"}]}"#,
        );
    }
}
