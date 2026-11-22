//! The RPC command surface, the workspace snapshots: `undo_turn` and
//! `get_turn_diff` over the live session (`eukhe_core::undo`), with the
//! daemon wire's reply shapes ([`eukhe_types::undo::UndoReply`],
//! [`eukhe_types::undo::TurnDiffReply`]). An undo is refused while a run
//! is going, as on the daemon wire.

use std::sync::Arc;

use eukhe_core::undo::{turn_diff, undo_turn as undo_session_turn};
use serde_json::Value;

use super::commands::RpcState;
use super::error::RpcCommandError;
use super::protocol::ResponseData;
use super::reads::rpc_context;
use crate::worker::diff_scope;

/// `undo_turn`: restore the workspace to the start of the newest turn not
/// undone.
///
/// # Errors
///
/// A run is going, nothing is left to undo, that turn has no snapshot, or
/// git or file IO failed.
pub(crate) async fn undo_turn(state: &Arc<RpcState>) -> Result<ResponseData, RpcCommandError> {
    let session = state.session.session().await;
    let reply = undo_session_turn(&session, &rpc_context()).await?;
    Ok(ResponseData::Present(serde_json::to_value(reply)?))
}

/// `get_turn_diff { scope }`: what changed in the workspace since the
/// start of the newest turn not undone (`turn`, the default) or of the
/// first turn (`all`).
///
/// # Errors
///
/// A `scope` other than `turn` or `all`, no turn yet, that turn has no
/// snapshot, or git IO failed.
pub(crate) async fn get_turn_diff(
    state: &Arc<RpcState>,
    payload: &Value,
) -> Result<ResponseData, RpcCommandError> {
    let scope =
        diff_scope(payload).map_err(|_| RpcCommandError::missing("get_turn_diff", "scope"))?;
    let session = state.session.session().await;
    let reply = turn_diff(&session, scope).await?;
    Ok(ResponseData::Present(serde_json::to_value(reply)?))
}
