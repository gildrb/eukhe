//! The session state tree on the wire: `get_state_tree` and
//! `subscribe_state_tree` answer the whole tree or the records after a
//! client cursor, `get_state_rewind_plan` answers what a rewind to a cursor
//! does, and after each commit that adds records one `state_tree_update`
//! frame carries them to the supervisor. The supervisor sends the frame
//! only to the connections that subscribed (`subscribe_state_tree`); it
//! is not a session event and takes no event sequence.

use std::sync::{Arc, Mutex, Weak};

use eukhe_core::durable::{EukheSession, TreeCursor};
use eukhe_durable::tree::{
    NodeId, RewindEffect, StateKey, StateKind, StateNode, StateTree, TreeOp, TreeRecord,
};
use eukhe_types::daemon::{
    DaemonOutbound, DaemonResponse, StateRewindPlanReply, StateTreeEffect, StateTreeKind,
    StateTreeNode, StateTreeNodeRef, StateTreeOp, StateTreeRecord, StateTreeRecords,
    StateTreeReply, StateTreeSnapshot,
};
use serde_json::Value;
use tokio::sync::watch;

use super::{EventPump, HostedSession, OutboundFrame, SessionCore, Worker};
use crate::protocol::{response_failure, response_success};

impl Worker {
    /// Follow the state tree of `hosted` (the installed session; `None`
    /// for none): the previous forwarder stops, and a new one sends each
    /// new record batch as a `state_tree_update` frame until the next
    /// follow.
    pub(crate) fn follow_state_tree(&self, hosted: Option<&HostedSession>) {
        let task = hosted
            .and_then(|hosted| hosted.session().ok())
            .map(|session| {
                tokio::spawn(forward_state_tree(
                    Arc::downgrade(&session),
                    session.state_tree().cursor(),
                    Arc::clone(&self.core),
                    Arc::clone(&self.events),
                ))
            });
        let previous = std::mem::replace(
            &mut *self
                .state_tree_updates
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner),
            task,
        );
        if let Some(previous) = previous {
            previous.abort();
        }
    }

    /// `get_state_tree { since? }` and `subscribe_state_tree { since? }`
    /// (Rust-native, advertised by the `state_tree` capability): the whole
    /// state tree with its cursor, or the records after the client cursor
    /// `since`. The supervisor keeps the subscription; for the worker both
    /// are the same read.
    pub(crate) async fn handle_get_state_tree(
        &self,
        command: &'static str,
        payload: &Value,
    ) -> DaemonResponse {
        let hosted = match self.hosted(command) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let since = match payload.get("since") {
            None | Some(Value::Null) => None,
            Some(since) => match since.as_u64().and_then(|since| usize::try_from(since).ok()) {
                Some(since) => Some(since),
                None => {
                    return response_failure(
                        None,
                        command,
                        &format!("invalid since: {since}"),
                        None,
                    )
                }
            },
        };
        let session = match hosted.session() {
            Ok(session) => session,
            Err(error) => return response_failure(None, command, &error.to_string(), None),
        };
        let reply = session
            .state_tree()
            .read(|state| match since {
                None => Ok(StateTreeReply::Snapshot(StateTreeSnapshot {
                    cursor: wire_cursor(state.cursor()),
                    seq: state.seq().map(eukhe_durable::types::Seq::get),
                    nodes: state
                        .tree()
                        .iter()
                        .map(|(id, node)| wire_node(state, id, node.parent, &node.value))
                        .collect::<Result<_, _>>()?,
                })),
                Some(since) => records(state, since).map(StateTreeReply::Records),
            })
            .await;
        respond(command, reply)
    }

    /// `get_state_rewind_plan { cursor }` (Rust-native, advertised by the
    /// `state_tree` capability): what a rewind of the state tree to the
    /// tree at `cursor` does to the work of each node.
    pub(crate) async fn handle_get_state_rewind_plan(&self, payload: &Value) -> DaemonResponse {
        const COMMAND: &str = "get_state_rewind_plan";
        let hosted = match self.hosted(COMMAND) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let Some(target) = payload
            .get("cursor")
            .and_then(Value::as_u64)
            .and_then(|cursor| usize::try_from(cursor).ok())
        else {
            return response_failure(None, COMMAND, "cursor must be a number", None);
        };
        let session = match hosted.session() {
            Ok(session) => session,
            Err(error) => return response_failure(None, COMMAND, &error.to_string(), None),
        };
        let reply = session
            .state_tree()
            .read(|state| {
                let effects = state
                    .rewind_plan(target)
                    .map_err(|error| error.to_string())?
                    .into_iter()
                    .map(|effect| {
                        Ok(match effect {
                            RewindEffect::Start(id) => StateTreeEffect::Start(node_ref(state, id)?),
                            RewindEffect::Stop(id) => StateTreeEffect::Stop(node_ref(state, id)?),
                            RewindEffect::Restore(id) => {
                                StateTreeEffect::Restore(node_ref(state, id)?)
                            }
                        })
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                Ok(StateRewindPlanReply {
                    cursor: wire_cursor(state.cursor()),
                    target: wire_cursor(target),
                    effects,
                })
            })
            .await;
        respond(COMMAND, reply)
    }
}

/// The response for a read of the tree: `None` when its build failed.
fn respond<T: serde::Serialize>(command: &str, reply: Option<Result<T, String>>) -> DaemonResponse {
    match reply {
        Some(Ok(reply)) => match serde_json::to_value(reply) {
            Ok(data) => response_success(None, command, Some(data)),
            Err(error) => response_failure(None, command, &error.to_string(), None),
        },
        Some(Err(message)) => response_failure(None, command, &message, None),
        None => response_failure(None, command, "the state tree build failed", None),
    }
}

/// Send each new record batch of the tree as a `state_tree_update` frame.
/// The frames chain from the cursor at the end of the build: each one
/// holds the records from the last frame's cursor to the tree's cursor. A
/// subscriber reads its own start with `subscribe_state_tree`.
#[tracing::instrument(skip_all)]
async fn forward_state_tree(
    session: Weak<EukheSession>,
    mut cursor: watch::Receiver<TreeCursor>,
    core: Arc<Mutex<SessionCore>>,
    events: Arc<EventPump>,
) {
    let mut sent: Option<usize> = None;
    loop {
        let current = *cursor.borrow_and_update();
        match (current, sent) {
            (TreeCursor::Failed, _) => return,
            (TreeCursor::Building, _) => {}
            (TreeCursor::Ready(now), None) => sent = Some(now),
            (TreeCursor::Ready(now), Some(from)) => {
                if now > from {
                    let Some(session) = session.upgrade() else {
                        return;
                    };
                    match session
                        .state_tree()
                        .read(|state| records(state, from))
                        .await
                    {
                        Some(Ok(update)) => {
                            sent = usize::try_from(update.cursor).ok();
                            let active_session_id = core
                                .lock()
                                .unwrap_or_else(std::sync::PoisonError::into_inner)
                                .active_session_id
                                .clone();
                            let outbound = DaemonOutbound::StateTreeUpdate {
                                active_session_id,
                                update,
                                rest: serde_json::Map::default(),
                            };
                            match serde_json::to_vec(&outbound) {
                                Ok(payload) => {
                                    events.send(OutboundFrame::state_tree_update(payload));
                                }
                                Err(error) => {
                                    tracing::warn!(%error, "state tree frame serialization failed");
                                }
                            }
                        }
                        Some(Err(error)) => {
                            tracing::warn!(%error, "state tree updates stopped");
                            return;
                        }
                        None => return,
                    }
                }
            }
        }
        if cursor.changed().await.is_err() {
            return;
        }
    }
}

fn wire_cursor(cursor: usize) -> u64 {
    u64::try_from(cursor).unwrap_or(u64::MAX)
}

fn wire_kind(kind: StateKind) -> StateTreeKind {
    match kind {
        StateKind::Conversation => StateTreeKind::Conversation,
        StateKind::Entry => StateTreeKind::Entry,
        StateKind::Task => StateTreeKind::Task,
        StateKind::Submission => StateTreeKind::Submission,
        StateKind::Document => StateTreeKind::Document,
    }
}

fn key_of(state: &StateTree, id: NodeId) -> Result<&StateKey, String> {
    state
        .key(id)
        .ok_or_else(|| format!("state tree node {} has no key", id.0))
}

fn node_ref(state: &StateTree, id: NodeId) -> Result<StateTreeNodeRef, String> {
    let key = key_of(state, id)?;
    Ok(StateTreeNodeRef {
        id: id.0,
        kind: wire_kind(key.kind()),
        key: key.id().to_owned(),
    })
}

fn wire_node(
    state: &StateTree,
    id: NodeId,
    parent: NodeId,
    node: &StateNode,
) -> Result<StateTreeNode, String> {
    Ok(StateTreeNode {
        id: id.0,
        parent: parent.0,
        kind: wire_kind(node.kind),
        key: key_of(state, id)?.id().to_owned(),
        value: (*node.value).clone(),
    })
}

fn wire_op(state: &StateTree, op: &TreeOp<StateNode>) -> Result<StateTreeOp, String> {
    Ok(match op {
        TreeOp::Put { id, parent, value } => {
            StateTreeOp::Put(wire_node(state, *id, *parent, value)?)
        }
        TreeOp::Del { id } => StateTreeOp::Del { id: id.0 },
    })
}

fn records(state: &StateTree, from: usize) -> Result<StateTreeRecords, String> {
    let records = state
        .records_since(from)
        .map_err(|error| error.to_string())?
        .iter()
        .map(|record| {
            Ok(match record {
                TreeRecord::Do(op) => StateTreeRecord::Do(wire_op(state, op)?),
                TreeRecord::Rewind(ops) => StateTreeRecord::Rewind(
                    ops.iter()
                        .map(|op| wire_op(state, op))
                        .collect::<Result<_, String>>()?,
                ),
            })
        })
        .collect::<Result<_, String>>()?;
    Ok(StateTreeRecords {
        from: wire_cursor(from),
        cursor: wire_cursor(state.cursor()),
        records,
    })
}
