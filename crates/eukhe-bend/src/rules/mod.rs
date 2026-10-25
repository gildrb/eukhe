//! The rules that run as their compiled Bend models: one module per area
//! (`pub mod <area>;`, one per line), each encoding its input with the wire
//! format, calling its entry and decoding the reply.

pub mod approvals;
pub mod bound;
pub mod cache_marks;
pub mod codemode_id;
pub mod color;
pub mod compactor;
pub mod config;
pub mod cron;
pub mod cvar;
pub mod cvar_layers;
pub mod doc_plan;
pub mod error_body;
pub mod frames;
pub mod fsmode;
pub mod glob;
pub mod goal_text;
pub mod infer_force;
pub mod infer_guard;
pub mod infer_threshold;
pub mod lease;
pub mod mcp_url;
pub mod model_facts;
pub mod optchat;
pub mod overflow;
pub mod package_source;
pub mod quirks;
pub mod redirect_input;
pub mod refine_plan;
pub mod retry;
pub mod retry_note;
pub mod runners;
pub mod scan;
pub mod semver;
pub mod shell;
pub mod slash;
pub mod slash_args;
pub mod stream_failure;
pub mod submission;
pub mod theme;
pub mod tokens;
pub mod tool_call;
pub mod tool_surface;
pub mod tui_color;
pub mod wait;
