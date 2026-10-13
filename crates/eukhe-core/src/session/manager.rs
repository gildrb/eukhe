//! `SessionManager`: the in-memory session model. Port of the class half of
//! core/session-manager.ts (load, new, append, index) without its file
//! writes: legacy session files are read-only import/export sources.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use eukhe_types::session::{
    AgentMessage, ChildUsageOrigin, EntryBase, FileEntry, GitContext, SessionHeader, SessionState,
    SessionStateStatus,
};

use super::{migrate_to_current_version, parse_session_entries, CURRENT_SESSION_VERSION};

// The inline unit battery moved to the child module at the same tree
// position (session::manager::tests); its use-super glob keeps resolving
// through the facade bindings and re-exports (the session_store stage-1
// precedent).
#[cfg(test)]
mod tests;

// The append concern (the in-memory append family: messages, changes,
// compactions, customs, child-usage attributions, session info/state -
// and the leaf/label mutators) lives in the child module at the same tree
// position (session::manager::append).
mod append;

// The entry index (by-id and label maps rebuilt from the entry chain).
mod index;

// The queries concern (the derived state + accessor arm: the active
// context/history snapshot, the branch scans, the window-backed reads,
// and the getters) moved to the child module at the same tree position
// (session::manager::queries); every member keeps its pub level and the
// facade binding below serves the child super:: paths (active_context:
// SessionContext + build_session_context).
mod queries;
use super::{build_session_context, SessionContext};

// The lifecycle concern (the constructors and the load/new/adopt arm)
// moved to the child module at the same tree position
// (session::manager::lifecycle); every member keeps its pub level, the
// child resolves the facade re-exports/bindings via its use-super glob,
// and the `use super::window;` module binding serves the children's
// super::window:: paths (open_windowed, adopt_window,
// set_append_ownership).
mod lifecycle;
use super::window;

// The id mint (the session id minters and the session file path) moved to
// the child module at the same tree position (session::manager::ids); the
// pub(super) bindings keep the constructors' + the append arm's bare calls
// in scope.
mod ids;
use crate::iso_time::format_iso_now;
pub use ids::get_session_file_path;
use ids::{create_session_id, generate_id};

// The header + rlm-depth concern (the first-line header read and the
// RLM depth resolution) moved to the child module at the same tree
// position (session::manager::header); the re-export keeps the pub API
// path stable (discovery.rs) and the pub(super) bindings keep the
// constructors' bare calls in scope (set_session_file, new_session).
mod header;
pub use header::read_session_header;
use header::{is_valid_rlm_depth, resolve_session_rlm_depth, root_rlm_depth_from_env};

// The git-context concern (the quiet git probes and the header capture)
// moved to the child module at the same tree position
// (session::manager::git); the re-export keeps the pub API path stable
// (manager_ext.rs + the git-context integration tests) and the
// constructors bare calls.
mod git;
pub use git::capture_git_context;

// The load concern (the header-validating legacy-file load) lives in the
// child module at the same tree position (session::manager::load); the
// re-export keeps the pub API path stable.
mod load;
pub use load::load_entries_from_file;

/// Options for creating a new session.
#[derive(Default)]
pub struct NewSessionOptions {
    pub id: Option<String>,
    pub parent_session: Option<String>,
    pub rlm_depth: Option<u64>,
}

/// The in-memory session model over a legacy session file: the loader the
/// legacy export reads through, plus the in-memory entry chain. It never
/// writes the session file; sessions persist through durable storage.
pub struct SessionManager {
    session_id: String,
    session_file: Option<PathBuf>,
    session_dir: PathBuf,
    cwd: PathBuf,
    /// Whether the manager carries a session directory of its own (the
    /// daemon's mirrored engine session): the session-owned artifacts
    /// (local harness state) resolve under it.
    session_dir_backed: bool,
    append_ownership: super::window::AppendOwnership,
    file_entries: Vec<FileEntry>,
    window: Option<super::window::WindowedSessionStore>,
    by_id: HashMap<String, usize>,
    labels_by_id: HashMap<String, String>,
    label_timestamps_by_id: HashMap<String, String>,
    leaf_id: Option<String>,
}
