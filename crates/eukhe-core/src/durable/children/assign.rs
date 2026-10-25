//! Re-task an existing child (`assign`): a new `eukhe.rlm.child` task on
//! the child of an earlier spawn. It skips the spawn and starts at the
//! prompt; its own task id names the prompt's idempotency key and its
//! report's request ids (`rlm:{task}:report:{n}`), so a second task's
//! report never collides with the first's, and its watch arms the stall
//! clock for this task only. Between tasks no task watches the child: an
//! idle child is not stalled.

use std::sync::Arc;

use eukhe_chord::json::to_json;
use eukhe_durable::harness::types::{ToolExecutionApi, ToolExecutionApiExt};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::{TaskOptions, TaskOwnership};
use serde_json::{Map, Value};

use super::host::ChildMessageKind;
use super::notice::rlm_child_label;
use super::registry::{resolve, tx_children, tx_put_row, ChildStatus, Resolved};
use super::requests::cx;
use super::task::{ChildTaskInput, ReportMode};
use super::Children;

/// One re-task: the prompt, what it is to the child, and its row details.
pub(crate) struct Assignment {
    pub(crate) prompt: String,
    pub(crate) kind: ChildMessageKind,
    pub(crate) details: Option<Map<String, Value>>,
}

/// The refusal for a child whose task is still running or owes its
/// report.
pub(crate) fn child_busy(name: &str) -> String {
    format!("Agent \"{name}\" is still on its task: wait for its report, or send context or a redirect to the running work")
}

/// Start a new watched task on the live child `target` selects in the
/// calling tool's conversation; answers the new task's id. The child must
/// be settled (no task running, no report owed): a busy child refuses.
/// The row's re-task fields, and main's hand-over of the user messages
/// the task carries (`forward_cursor`), land in the commit that admits
/// the task.
///
/// # Errors
///
/// No or an ambiguous child, a busy child, or a failed commit.
pub(crate) async fn assign(
    children: &Children,
    api: &Arc<dyn ToolExecutionApi>,
    target: String,
    assignment: Assignment,
    forward_cursor: Option<u64>,
) -> SessionResult<u64> {
    let task = children.task.as_definition_ref();
    let conversation_id = api.conversation_id();
    let max_depth = children.services.rlm_max_depth;
    // The task anchors to the parent's in-flight model request, as a
    // spawn does; the tool call id stands in without a recorder.
    let spawned_by_request_id = children
        .services
        .semantic_edges
        .as_ref()
        .and_then(|recorder| recorder.last_turn_request_id())
        .unwrap_or_else(|| api.call_id().to_owned());
    api.commit(
        move |tx| async move {
            let state = tx_children(&tx, conversation_id).await?;
            let mut row = match resolve(
                state.children.values().filter(|row| !row.is_deleted()),
                &target,
            ) {
                Resolved::One(row) => row.clone(),
                Resolved::None => {
                    return Err(SessionError::error(format!(
                        "No direct agent matches \"{target}\" in this session"
                    )))
                }
                Resolved::Ambiguous => {
                    return Err(SessionError::error(format!(
                        "Agent selector \"{target}\" is ambiguous in this session"
                    )))
                }
            };
            if !row.settled || !row.status.is_terminal() {
                return Err(SessionError::error(child_busy(&row.session_name)));
            }
            let label = rlm_child_label(&assignment.prompt);
            let input = ChildTaskInput {
                prompt: assignment.prompt,
                model: None,
                thinking: None,
                spawned_by_request_id: Some(spawned_by_request_id),
                max_depth: Some(max_depth),
                workspace: None,
                owed: None,
                report: ReportMode::Inbox,
                child: Some(row.task_id),
                kind: assignment.kind,
                details: assignment.details,
                worker: row.worker,
            };
            let task_id = tx
                .create_task(
                    task,
                    to_json(&input)?,
                    TaskOptions {
                        ownership: TaskOwnership::Conversation,
                        conversation_id: Some(conversation_id),
                        background: Some(true),
                        abandon_on_restart: None,
                    },
                )
                .await?;
            row.status = ChildStatus::Running;
            row.task = Some(task_id.get());
            row.settled = false;
            row.replied_since_task = false;
            row.reporter = None;
            row.error = None;
            row.failure = None;
            row.answer_preview = None;
            row.answer = None;
            row.label = label;
            tx_put_row(&tx, conversation_id, &row).await?;
            if let Some(cursor) = forward_cursor {
                super::worker::tx_hand_over(&tx, conversation_id, cursor).await?;
            }
            Ok(task_id.get())
        },
        &cx(),
    )
    .await
}
