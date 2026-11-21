//! `/undo` and `/diff`: the per-prompt workspace snapshots of a top-level
//! session.

use serde::{Deserialize, Serialize};

/// What `/diff` compares the workspace with.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum DiffScope {
    /// The start of the newest turn not undone.
    #[default]
    Turn,
    /// The start of the session's first turn (`/diff all`).
    All,
}
