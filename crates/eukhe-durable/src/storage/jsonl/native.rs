//! Port of `storage/jsonl/node.ts`.

use std::sync::Arc;

use eukhe_chord::context::Context;

use super::storage::{JsonlStorage, JsonlStorageOptions};
use crate::env::{CreationModes, NativeExecutionEnv, NativeExecutionEnvOptions};
use crate::errors::StorageError;

/// Open or create a JSONL storage directory using the local native
/// filesystem, resolving relative paths against the process's current
/// directory (TS `openNodeJsonlStorage`). A storage is eukhe's own state:
/// the directories and files it creates are owner only
/// ([`CreationModes::Private`]).
///
/// # Errors
/// Fails when the current directory cannot be read, or as
/// [`JsonlStorage::open`] does.
pub async fn open_native_jsonl_storage(
    directory: &str,
    cx: &Context,
    options: JsonlStorageOptions,
) -> Result<JsonlStorage, StorageError> {
    let cwd = std::env::current_dir().map_err(StorageError::failed)?;
    let env = NativeExecutionEnv::new(NativeExecutionEnvOptions {
        cwd: cwd.to_string_lossy().into_owned(),
        creation: CreationModes::Private,
        ..NativeExecutionEnvOptions::default()
    });
    JsonlStorage::open(directory, Arc::new(env), cx, options).await
}
