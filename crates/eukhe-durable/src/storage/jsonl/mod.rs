//! JSONL storage backend. Port of `storage/jsonl/index.ts` and
//! `storage/jsonl/node.ts`.

#[cfg(test)]
mod bridge;
mod native;
mod storage;

pub use native::open_native_jsonl_storage;
pub use storage::{
    CommitHistory, HistoryCommit, JsonlCommitCancelledError, JsonlCorruptionError, JsonlFileError,
    JsonlStorage, JsonlStorageOptions, JsonlStoragePoisonedError,
};
