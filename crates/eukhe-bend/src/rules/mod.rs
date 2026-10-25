//! The rules that run as their compiled Bend models: one module per area
//! (`pub mod <area>;`, one per line), each encoding its input with the wire
//! format, calling its entry and decoding the reply.

pub mod cron;
pub mod cvar;
pub mod fsmode;
pub mod lease;
pub mod retry;
pub mod semver;
pub mod wait;
