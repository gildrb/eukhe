//! Rust port of `@earendil-works/pi-durable` 1.0.4, with parts of 1.1 and 1.2
//! ported (1.2 compaction, scheduler, inbox, input-entry, and document-cache
//! changes, and the 1.2 `codemode` tool), a durable agent harness.
//! Conversations, model turns, tool calls, and application state are
//! committed to storage before anything is shown. If the process dies
//! mid-turn, reopening the storage picks the work up where it stopped.

pub mod codemode;
pub mod documents;
pub mod entries;
pub mod env;
pub mod errors;
pub mod harness;
pub mod ids;
pub mod search;
pub mod session;
pub mod storage;
pub mod tasks;
#[cfg(feature = "testing")]
pub mod testing;
pub mod tree;
pub mod types;

/// The default line bound of a tool result.
pub const DEFAULT_MAX_LINES: u64 = 2000;
/// The default byte bound of a tool result (50KB).
pub const DEFAULT_MAX_BYTES: u64 = 50 * 1024;
