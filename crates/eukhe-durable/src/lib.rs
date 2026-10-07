//! Rust port of `@earendil-works/pi-durable` v1.0.4, a durable agent harness.
//! Conversations, model turns, tool calls, and application state are
//! committed to storage before anything is shown. If the process dies
//! mid-turn, reopening the storage picks the work up where it stopped.

pub mod documents;
pub mod entries;
pub mod env;
pub mod errors;
pub mod harness;
pub mod ids;
pub mod session;
pub mod storage;
pub mod tasks;
pub mod testing;
pub mod tools;
#[cfg_attr(
    not(test),
    expect(dead_code, reason = "used by the tools and harness, ported separately")
)]
mod truncate;
pub mod types;
