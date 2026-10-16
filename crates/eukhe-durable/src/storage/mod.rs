//! Storage backends implementing [`Storage`](crate::types::Storage): the
//! in-memory reference store and JSONL files.

mod common;
pub mod jsonl;
mod memory;
mod scan;

pub use memory::{MemoryStorage, PreparedMemoryCommit};

/// Durable storage for the crate's tests: a JSONL directory that survives a
/// simulated restart.
#[cfg(test)]
pub(crate) mod test_support {
    use std::path::{Path, PathBuf};
    use std::sync::Arc;

    use eukhe_chord::context::BACKGROUND_CONTEXT;

    use super::jsonl::{open_native_jsonl_storage, JsonlStorageOptions};
    use crate::types::Storage;

    /// A fresh directory (removed when the guard drops) and the storage
    /// directory inside it.
    pub(crate) fn store_path() -> (tempfile::TempDir, PathBuf) {
        let directory = tempfile::tempdir().expect("create a temp dir");
        let path = directory.path().join("session");
        (directory, path)
    }

    /// Open, or reopen after a close, the JSONL storage at `path`.
    pub(crate) async fn jsonl(path: &Path) -> Arc<dyn Storage> {
        let path = path.to_str().expect("a UTF-8 temp path");
        Arc::new(
            open_native_jsonl_storage(path, &BACKGROUND_CONTEXT, JsonlStorageOptions::default())
                .await
                .expect("open the JSONL storage"),
        )
    }
}
