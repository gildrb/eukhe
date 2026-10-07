//! The call's execution environment. Port of `tools/env.ts`.

use std::sync::Arc;

use crate::env::{ExecutionEnv, ExecutionError, FileError};
use crate::harness::types::ToolExecutionApi;
use crate::session::{SessionError, SessionResult};

/// The call's execution environment; a tool without one fails with an
/// ordinary error result.
///
/// # Errors
///
/// No execution environment is configured.
pub(crate) fn require_env(api: &dyn ToolExecutionApi) -> SessionResult<Arc<dyn ExecutionEnv>> {
    api.env()
        .ok_or_else(|| SessionError::error("No execution environment is configured"))
}

/// TS `getOrThrow` of a file operation: the [`FileError`] itself is thrown.
impl From<FileError> for SessionError {
    fn from(error: FileError) -> Self {
        Self::other(error)
    }
}

/// TS `throw result.error` of a command: the [`ExecutionError`] itself is
/// thrown.
impl From<ExecutionError> for SessionError {
    fn from(error: ExecutionError) -> Self {
        Self::other(error)
    }
}

/// TS `new Error("Operation aborted")`, thrown by the file tools when the
/// call's context is aborted between steps.
pub(crate) fn operation_aborted() -> SessionError {
    SessionError::error("Operation aborted")
}
