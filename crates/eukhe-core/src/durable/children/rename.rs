//! `rlm.rename` (TS `createRlmRenameHostHandler` +
//! `renameAgentFamilySession`): rename the calling session or one direct
//! child. The name follows the spawn rules; a child is selected by id only
//! (child handle, routing id, or durable session id), never by name. A child
//! rename reserves the name in the parent's registry (sibling uniqueness,
//! atomically with the row update, like `rlm.spawn`), then asks the host to
//! rename the child session; a failed host rename restores the old name.

use std::sync::Arc;

use anyhow::bail;
use eukhe_durable::session::SessionError;
use eukhe_durable::types::{ConversationId, TaskId};
use serde_json::{json, Value};

use super::host::{RlmRenameRequest, RlmRenameTarget};
use super::registry::{tx_children, tx_update_row, ChildStatus};
use super::requests::{commit, conversation_of, session_error, spawn_name_unavailable};
use super::Children;
use crate::durable::deps::HostCall;
use crate::kernel::rlm_runtime::normalize_requested_rlm_subagent_session_name;
use crate::session_engine::agent_messaging::assert_direct_agent_message_target;

const OPERATION: &str = "rlm.rename";
const NOT_OWN_FAMILY: &str =
    "rlm.rename can only rename the current session or one of its direct children";

/// What the reservation commit found for a child selector.
enum Reservation {
    /// The row now carries the new name; `previous` restores it.
    Reserved {
        task_id: TaskId,
        session_id: String,
        previous: String,
    },
    /// No live child has this id; `by_name` when one has it as its name.
    Unresolved { by_name: bool },
}

/// The validated new name: the spawn normalizer (absent or non-string
/// names read as the TS "must be a string" error) plus the broadcast guard.
fn requested_name(data: &Value) -> anyhow::Result<String> {
    let Some(name) = normalize_requested_rlm_subagent_session_name(
        data.get("name").and_then(Value::as_str),
        OPERATION,
    )?
    else {
        bail!("rlm.rename name must be a string");
    };
    assert_direct_agent_message_target(&name)?;
    Ok(name)
}

/// The optional `session_id` selector, trimmed.
fn requested_session_id(data: &Value) -> anyhow::Result<Option<String>> {
    match data.get("session_id") {
        None | Some(Value::Null) => Ok(None),
        Some(Value::String(raw)) if !raw.trim().is_empty() => Ok(Some(raw.trim().to_owned())),
        Some(_) => bail!("rlm.rename session_id must be a non-empty string"),
    }
}

/// `rlm.rename { name, session_id? }`: answers `{ name }` with the applied
/// name.
pub(super) async fn rename(children: Arc<Children>, call: HostCall) -> anyhow::Result<Value> {
    let name = requested_name(&call.data)?;
    let selector = requested_session_id(&call.data)?
        .filter(|selector| *selector != children.services.parent_session_id);
    match selector {
        None => rename_self(&children, &name, None).await?,
        Some(selector) => {
            rename_child(&children, conversation_of(&call), selector, name.clone()).await?;
        }
    }
    Ok(json!({ "name": name }))
}

async fn rename_self(
    children: &Children,
    name: &str,
    selector: Option<String>,
) -> anyhow::Result<()> {
    children
        .services
        .host
        .rename(RlmRenameRequest {
            name: name.to_owned(),
            target: RlmRenameTarget::Session { selector },
        })
        .await
}

async fn rename_child(
    children: &Children,
    conversation_id: ConversationId,
    selector: String,
    name: String,
) -> anyhow::Result<()> {
    let harness = children.harness.require().map_err(session_error)?;
    let sibling_depth = children.services.rlm_depth + 1;
    let (target, new_name) = (selector.clone(), name.clone());
    let reservation = commit(&harness, conversation_id, move |tx| async move {
        let state = tx_children(&tx, conversation_id).await?;
        let mut live = state.children.values().filter(|row| !row.is_deleted());
        let Some(row) = live.clone().find(|row| row.matches_id(&target)) else {
            return Ok(Reservation::Unresolved {
                by_name: live.any(|row| row.session_name == target),
            });
        };
        // A child being deleted is leaving the family; a spawning child has
        // no session to rename yet (`rlm.spawn` has not returned its handle).
        if row.delete_requested() {
            return Err(SessionError::error(NOT_OWN_FAMILY));
        }
        if row.status == ChildStatus::Spawning {
            return Err(SessionError::error(format!(
                "RLM child \"{target}\" is still starting; rename it after rlm.spawn returns"
            )));
        }
        if live.any(|other| other.task_id != row.task_id && other.session_name == new_name) {
            return Err(SessionError::error(spawn_name_unavailable(
                &new_name,
                sibling_depth,
            )));
        }
        let task_id = row.task_id();
        let session_id = row.session_id.clone();
        let previous = row.session_name.clone();
        tx_update_row(&tx, conversation_id, task_id, |row| {
            row.session_name = new_name;
        })
        .await?;
        Ok(Reservation::Reserved {
            task_id,
            session_id,
            previous,
        })
    })
    .await?;
    let (task_id, session_id, previous) = match reservation {
        Reservation::Reserved {
            task_id,
            session_id,
            previous,
        } => (task_id, session_id, previous),
        Reservation::Unresolved { by_name: true } => bail!(
            "rlm.rename session_id \"{selector}\" must be the full session id or a child handle, not a session name or id suffix"
        ),
        // Not a child: the host renames itself when the selector is its own
        // routing id, else refuses.
        Reservation::Unresolved { by_name: false } => {
            return rename_self(children, &name, Some(selector)).await;
        }
    };
    let renamed = children
        .services
        .host
        .rename(RlmRenameRequest {
            name: name.clone(),
            target: RlmRenameTarget::Child { session_id },
        })
        .await;
    let Err(error) = renamed else {
        return Ok(());
    };
    // The child kept its old name: so does its registry row, unless another
    // rename already replaced the reserved one.
    let restored = commit(&harness, conversation_id, move |tx| async move {
        tx_update_row(&tx, conversation_id, task_id, |row| {
            if row.session_name == name {
                row.session_name = previous;
            }
        })
        .await
        .map(drop)
    })
    .await;
    match restored {
        Ok(()) => Err(error),
        Err(restore_error) => Err(error.context(format!(
            "restoring the child's previous registry name failed: {restore_error:#}"
        ))),
    }
}
