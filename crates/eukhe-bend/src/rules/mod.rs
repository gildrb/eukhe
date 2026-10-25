//! The rules that run as their compiled Bend models: one module per area
//! (`pub mod <area>;`, one per line), each encoding its input with the wire
//! format, calling its entry and decoding the reply.

pub mod approvals;
pub mod bound;
pub mod codemode_id;
pub mod compactor;
pub mod cvar;
pub mod frames;
pub mod fsmode;
pub mod infer_force;
pub mod infer_guard;
pub mod infer_threshold;
pub mod model_facts;
pub mod retry;
pub mod runners;
pub mod semver;
pub mod shell;
pub mod tokens;
pub mod tool_surface;
