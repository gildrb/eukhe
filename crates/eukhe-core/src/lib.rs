// The Tier-C/D ruling (fleet-uniform, 2026-09-28): stack-resident futures
// by design on hot paths (boxing the 27 flagged fns is allocation-churn
// with zero correctness gain); the fn-length threshold is a style gate,
// not correctness (the session-engine fns are intentionally linear); 64-bit
// targets - the narrowing sits at OS/protocol boundaries where the values
// are bounded (pid syscalls, epoch/elapsed milliseconds, calendar math,
// guarded parses), and checked conversions would add panic paths where
// silent wrap was deliberate (the per-site triage found NO genuinely
// suspect family in this crate - the lane dossier records the read).
#![allow(
    clippy::large_futures,
    clippy::too_many_lines,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::cast_precision_loss
)]
// Test-only: the exact-float `assert_eq!`s assert parsed fixture values
// (the byte-identity contract - values written as JSON literals); an
// epsilon compare would weaken the assertions, not fix a lint.
#![cfg_attr(test, allow(clippy::float_cmp))]

//! Session engine: tools, skills, prompts, compaction, refinement, kernel/RLM
//! manager, subagents, session manager, settings.

pub mod admission;
pub mod agent_messaging;
// RLM kernel subsystem: persistent IPython kernel lifecycle.
pub mod agent_log;
pub mod auth;
pub mod autonomous;
pub mod child_workspace;
pub mod cron;
pub mod durable;
pub mod export_html;
pub mod goals;
pub mod image_dimensions;
pub mod kernel;
pub mod mcp;
pub mod memory;
pub mod models;
pub mod packages;
pub mod platform;
pub mod prompts;
pub mod read_path;
pub mod refinement;
pub mod resources;
pub mod session;
pub mod settings;
pub mod skills;
pub mod slash_command_args;
pub mod tiny;
pub mod workspace_snapshot;
pub use kernel::ReplKernelManager;
