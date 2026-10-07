//! JSONL storage backend. Port of `storage/jsonl/index.ts` and
//! `storage/jsonl/node.ts`.

mod native;
mod storage;

pub use native::open_native_jsonl_storage;
pub use storage::{
    JsonlCorruptionError, JsonlFileError, JsonlStorage, JsonlStorageOptions,
    JsonlStoragePoisonedError,
};
