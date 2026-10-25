//! The rules that run as their compiled Bend models: one module per area
//! (`pub mod <area>;`, one per line), each encoding its input with the wire
//! format, calling its entry and decoding the reply.

pub mod approvals;
pub mod bound;
pub mod codemode_id;
pub mod compactor;
pub mod cvar;
pub mod doc_plan;
pub mod frames;
pub mod fsmode;
pub mod infer_force;
pub mod infer_guard;
pub mod infer_threshold;
pub mod model_facts;
pub mod node_error;
pub mod repeat;
pub mod retry;
pub mod retry_note;
pub mod runners;
pub mod scan;
pub mod semver;
pub mod shell;
pub mod submission;
pub mod throttle;
pub mod tokens;
pub mod tool_surface;
