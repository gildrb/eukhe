//! `undo_turn` and `get_turn_diff`: the session's workspace snapshots
//! (`eukhe_core::undo`). An undo is refused while a run is going.

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_core::undo::{turn_diff, undo_turn, UndoError};
use eukhe_types::daemon::DaemonErrorInfo;
use eukhe_types::undo::DiffScope;
use serde_json::Value;

use super::Worker;
use crate::protocol::{response_failure, response_success, DaemonResponse};

const UNDO: &str = "undo_turn";
const DIFF: &str = "get_turn_diff";

impl Worker {
    /// `undo_turn` (Rust-native): restore the workspace to the start of
    /// the newest turn not undone.
    pub(crate) async fn handle_undo_turn(&self) -> DaemonResponse {
        let hosted = match self.hosted(UNDO) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let session = match hosted.session() {
            Ok(session) => session,
            Err(error) => return response_failure(None, UNDO, &error.to_string(), None),
        };
        answer(UNDO, undo_turn(&session, &BACKGROUND_CONTEXT).await)
    }

    /// `get_turn_diff { scope }` (Rust-native): the workspace's changes
    /// since the start of the newest turn not undone, or of the first.
    pub(crate) async fn handle_get_turn_diff(&self, payload: &Value) -> DaemonResponse {
        let hosted = match self.hosted(DIFF) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let session = match hosted.session() {
            Ok(session) => session,
            Err(error) => return response_failure(None, DIFF, &error.to_string(), None),
        };
        let scope = match diff_scope(payload) {
            Ok(scope) => scope,
            Err(error) => return response_failure(None, DIFF, &format!("scope: {error}"), None),
        };
        answer(DIFF, turn_diff(&session, scope).await)
    }
}

/// The `scope` of a `get_turn_diff` payload: the turn when absent.
///
/// # Errors
///
/// A `scope` that is not `turn` or `all`.
pub(crate) fn diff_scope(payload: &Value) -> Result<DiffScope, serde_json::Error> {
    match payload.get("scope") {
        None | Some(Value::Null) => Ok(DiffScope::default()),
        Some(scope) => serde_json::from_value(scope.clone()),
    }
}

fn answer<T: serde::Serialize>(command: &str, result: Result<T, UndoError>) -> DaemonResponse {
    let info = |error: &UndoError| match error {
        UndoError::NothingToUndo => Some(DaemonErrorInfo::NothingToUndo),
        UndoError::NothingToDiff => Some(DaemonErrorInfo::NothingToDiff),
        UndoError::RunInProgress => Some(DaemonErrorInfo::RunInProgress),
        UndoError::NoSnapshots
        | UndoError::NoTurnSnapshot { .. }
        | UndoError::Unread { .. }
        | UndoError::TooLarge { .. }
        | UndoError::Answer(..)
        | UndoError::Git { .. }
        | UndoError::Session(_)
        | UndoError::Io(_)
        | UndoError::Core(_) => None,
    };
    match result.map(serde_json::to_value) {
        Ok(Ok(data)) => response_success(None, command, Some(data)),
        Ok(Err(error)) => response_failure(None, command, &error.to_string(), None),
        Err(error) => response_failure(None, command, &error.to_string(), info(&error)),
    }
}
