//! Storage backends implementing [`Storage`](crate::types::Storage): the
//! in-memory reference store, SQLite, and JSONL files.

mod common;
pub mod jsonl;
mod memory;
pub mod sqlite;

pub use memory::{MemoryStorage, PreparedMemoryCommit};
