//! Host-command access to the children registry: the daemon's
//! `get_rlm_children`, `cancel_rlm_child`, and `delete_rlm_subagent`
//! commands read and drive the same `eukhe.rlm.children` rows the `rlm.*`
//! kernel requests do.

use eukhe_chord::context::Context;
use eukhe_durable::harness::Harness;
use eukhe_durable::session::SessionResult;
use eukhe_durable::types::{ConversationId, DocumentReader};

use super::host::RlmSubagentHost;
use super::registry::{read_children, resolve, ChildRow, ChildrenState, Resolved};
use super::requests::{delete_child_row, entry, now_ms, session_error};
use super::wire::RlmSubagentEntry;

/// What `delete_inactive_child` did.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeleteChildOutcome {
    /// The child was torn down; its row is a tombstone.
    Deleted(Box<RlmSubagentEntry>),
    /// The child's task has not settled: nothing was deleted.
    Running,
    /// No live child matches.
    NotFound,
}

/// Delete the settled child `target` selects (the daemon's
/// `delete_rlm_subagent`, TS `deleteInactiveRlmSubagent`): a child whose
/// task is still running is refused, never aborted.
///
/// # Errors
///
/// An ambiguous selector, a document read failure, or a failed teardown
/// (the child stays selectable so the caller can retry).
pub async fn delete_inactive_child(
    harness: &Harness,
    host: &dyn RlmSubagentHost,
    conversation_id: ConversationId,
    target: &str,
    cx: &Context,
) -> anyhow::Result<DeleteChildOutcome> {
    let state = read_children(harness, conversation_id, cx)
        .await
        .map_err(session_error)?;
    match live_row(&state, target)? {
        None => return Ok(DeleteChildOutcome::NotFound),
        Some(row) if !row.settled => return Ok(DeleteChildOutcome::Running),
        Some(_) => {}
    }
    let result = delete_child_row(harness, host, conversation_id, target, cx).await?;
    Ok(DeleteChildOutcome::Deleted(Box::new(result.subagent)))
}

/// One live (not deleted) child as a host command sees it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RlmChildRecord {
    /// The roster row (no live host overlay).
    pub entry: RlmSubagentEntry,
    /// The child's resolved `provider/id` model, once spawned.
    pub model: Option<String>,
    /// The child task ended: its run settled and any owed report was
    /// submitted.
    pub settled: bool,
}

/// The live children of `conversation_id`, in spawn order.
///
/// # Errors
///
/// Document read failures.
pub async fn list_children(
    reader: &(impl DocumentReader + ?Sized),
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<Vec<RlmChildRecord>> {
    let state = read_children(reader, conversation_id, cx).await?;
    let now = now_ms();
    Ok(state
        .children
        .values()
        .filter(|row| !row.is_deleted())
        .map(|row| RlmChildRecord {
            entry: entry(row, None, now),
            model: row.model.clone(),
            settled: row.settled,
        })
        .collect())
}

/// The live child `target` selects: `None` when none matches, `Err` when
/// the selector is ambiguous or the document read fails.
///
/// # Errors
///
pub async fn find_child(
    reader: &(impl DocumentReader + ?Sized),
    conversation_id: ConversationId,
    target: &str,
    cx: &Context,
) -> anyhow::Result<Option<RlmChildRecord>> {
    let state = read_children(reader, conversation_id, cx)
        .await
        .map_err(session_error)?;
    let row = live_row(&state, target)?;
    Ok(row.map(|row| RlmChildRecord {
        entry: entry(row, None, now_ms()),
        model: row.model.clone(),
        settled: row.settled,
    }))
}

/// The live row `target` selects (TS selector errors on ambiguity).
fn live_row<'a>(state: &'a ChildrenState, target: &str) -> anyhow::Result<Option<&'a ChildRow>> {
    match resolve(state.children.values().filter(|row| !row.is_deleted()), target) {
        Resolved::None => Ok(None),
        Resolved::One(row) => Ok(Some(row)),
        Resolved::Ambiguous => {
            anyhow::bail!(
                "RLM subagent selector \"{target}\" is ambiguous in the current parent session"
            )
        }
    }
}

/// Cancel the in-flight run of the child `target` selects: abort its
/// `eukhe.rlm.child` task (the abort cancels the child at the host and marks
/// the row cancelled) and wait for the task to end. Answers the row after
/// the cancel, or `None` when no unsettled child matches (an unknown or
/// already settled child is not an error).
///
/// # Errors
///
/// An ambiguous selector, a document read failure, or a failed abort.
pub async fn cancel_child(
    harness: &Harness,
    conversation_id: ConversationId,
    target: &str,
    cx: &Context,
) -> anyhow::Result<Option<RlmSubagentEntry>> {
    let state = read_children(harness, conversation_id, cx)
        .await
        .map_err(session_error)?;
    let Some(row) = live_row(&state, target)?.cloned() else {
        return Ok(None);
    };
    if row.settled {
        return Ok(None);
    }
    let task_id = row.task_id();
    harness
        .abort_task(task_id, cx)
        .await
        .map_err(session_error)?;
    harness
        .wait_for_task(task_id, cx)
        .await
        .map_err(session_error)?;
    let after = read_children(harness, conversation_id, cx)
        .await
        .map_err(session_error)?;
    let row = after
        .children
        .get(&task_id.to_string())
        .cloned()
        .unwrap_or(row);
    Ok(Some(entry(&row, None, now_ms())))
}
