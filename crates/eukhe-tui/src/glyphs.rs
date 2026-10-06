//! The glyphs of everything eukhe draws itself. ASCII only (0x20-0x7E):
//! the CLI draws no Unicode symbols, box lines, or emoji. User, model,
//! and file text is not changed.

/// Spinner frames, one per tick.
pub const SPINNER: [&str; 4] = ["|", "/", "-", "\\"];
/// The working indicator frames, one per tick.
pub const WORKING: [&str; 4] = [".", "o", "O", "o"];
/// A horizontal rule cell.
pub const RULE: &str = "-";
/// A vertical bar: quote bars, gutters, column separators.
pub const BAR: &str = "|";
/// A list bullet.
pub const BULLET: &str = "*";
/// A selection pointer.
pub const POINTER: &str = ">";
/// A collapsed group marker.
pub const COLLAPSED: &str = "+";
/// An expanded group marker.
pub const EXPANDED: &str = "-";
/// Truncation marker.
pub const ELLIPSIS: &str = "...";
/// Separator between inline segments (status line, hints).
pub const SEP: &str = " - ";
/// A dash used as punctuation in prose chrome.
pub const DASH: &str = "--";
/// Status marks.
pub const OK: &str = "ok";
pub const FAIL: &str = "x";
/// A filled and an empty state dot (running / idle).
pub const DOT_ON: &str = "*";
pub const DOT_OFF: &str = "o";
/// A masked secret character.
pub const MASK: &str = "*";
/// Tree connectors: a middle child, the last child, a continuing parent.
pub const TREE_MID: &str = "|- ";
pub const TREE_LAST: &str = "`- ";
pub const TREE_PIPE: &str = "|  ";
pub const TREE_SPACE: &str = "   ";
/// Table borders.
pub const TABLE_CROSS: &str = "+";
pub const TABLE_H: &str = "-";
pub const TABLE_V: &str = "|";
/// Key names in hints.
pub const KEY_UP: &str = "up";
pub const KEY_DOWN: &str = "down";
pub const KEY_LEFT: &str = "left";
pub const KEY_RIGHT: &str = "right";
/// Direction marks inside data (token counts, more-rows indicators).
pub const UP: &str = "^";
pub const DOWN: &str = "v";
pub const LEFT: &str = "<";
pub const RIGHT: &str = ">";
/// The heartbeat badge mark.
pub const HEARTBEAT: &str = "@";
/// A half-on state dot (idle, paused, pending).
pub const DOT_HALF: &str = "~";
/// The agent message mark.
pub const MAIL: &str = "&";
/// The branch gutter hanging a row off the header above it.
pub const BRANCH: &str = "`- ";
/// A header mark for notices (compaction, refinement, chat view).
pub const NOTICE: &str = "*";
/// Effort meter cells: filled and empty.
pub const METER_ON: &str = "#";
pub const METER_OFF: &str = ".";
/// The last-fired edge marker in factory diagrams.
pub const FIRED: &str = ">>";
/// A transition edge arrow.
pub const ARROW: &str = "->";
/// A warning mark.
pub const WARN: &str = "!";
