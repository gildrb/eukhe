//! A session's workspace snapshots over the daemon wire: `undo_turn` and
//! `get_turn_diff` as typed requests.

use anyhow::{Context, Result};
use eukhe_types::daemon::DaemonCommand;
use eukhe_types::undo::{DiffScope, TurnDiffReply, UndoReply};
use serde_json::Map;

use super::DaemonClient;

impl DaemonClient {
    /// Restore the workspace of the session `active_session_id` to the
    /// start of its newest turn not undone.
    ///
    /// # Errors
    ///
    /// The request fails, the daemon refuses it
    /// ([`RequestRejected`](super::RequestRejected): nothing to undo, a run
    /// is going), or its answer has another shape.
    pub async fn undo_turn(&self, active_session_id: &str) -> Result<UndoReply> {
        let data = self
            .request_ok(DaemonCommand::UndoTurn {
                id: None,
                active_session_id: active_session_id.to_string(),
                rest: Map::default(),
            })
            .await?;
        serde_json::from_value(data).context("read the undo_turn answer")
    }

    /// The changes in the workspace of the session `active_session_id`
    /// since the start of its newest turn not undone (`Turn`) or of its
    /// first turn (`Run`).
    ///
    /// # Errors
    ///
    /// The request fails, the daemon refuses it
    /// ([`RequestRejected`](super::RequestRejected): no turn ran yet), or
    /// its answer has another shape.
    pub async fn get_turn_diff(
        &self,
        active_session_id: &str,
        scope: DiffScope,
    ) -> Result<TurnDiffReply> {
        let data = self
            .request_ok(DaemonCommand::GetTurnDiff {
                id: None,
                active_session_id: active_session_id.to_string(),
                scope,
                rest: Map::default(),
            })
            .await?;
        serde_json::from_value(data).context("read the get_turn_diff answer")
    }
}
