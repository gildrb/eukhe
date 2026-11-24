//! The on-screen window roster: everything the OS shows now, popup menus,
//! pickers and system panels included (port of omp
//! `crates/natives/src/desktop/roster.rs`).

use serde::{Deserialize, Serialize};

use crate::geometry::GlobalRect;
use crate::types::{Pid, WindowId};

/// Whether the window list (and so window selectors) includes a window.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Listing {
    Listed,
    Unlisted,
}

/// One on-screen window, front to back.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct RosterWindow {
    pub id: WindowId,
    pub pid: Pid,
    pub app: String,
    /// Empty without Screen Recording and for windows that publish none.
    pub title: String,
    pub bounds: GlobalRect,
    /// The window server layer: 0 for ordinary windows, 3 for floating
    /// panels, 101 for popup menus, higher for system panels.
    pub layer: i32,
    /// Opacity; 0 is an invisible overlay.
    pub alpha: f64,
    pub listing: Listing,
}
