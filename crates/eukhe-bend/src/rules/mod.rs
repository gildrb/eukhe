//! The rules that run as their compiled Bend models: one module per area
//! (`pub mod <area>;`, one per line), each encoding its input with the wire
//! format, calling its entry and decoding the reply.

pub mod approvals;
pub mod cvar;
pub mod fsmode;
pub mod retry;
pub mod runners;
pub mod semver;
pub mod shell;
