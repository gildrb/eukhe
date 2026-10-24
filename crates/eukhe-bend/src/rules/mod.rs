//! The rules that run as their compiled Bend models: one module per area
//! (`pub mod <area>;`, one per line), each encoding its input with the wire
//! format, calling its entry and decoding the reply.

pub mod approvals;
pub mod color;
pub mod cvar;
pub mod cvar_layers;
pub mod frames;
pub mod fsmode;
pub mod quirks;
pub mod retry;
pub mod runners;
pub mod semver;
pub mod shell;
pub mod theme;
pub mod tool_surface;
pub mod tui_color;
