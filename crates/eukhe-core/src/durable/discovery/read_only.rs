//! A read-only view of a durable JSONL storage that another process may be
//! writing: `JsonlStorage::open` replays the committed records into memory
//! and then repairs the files (truncating unconfirmed sidecar tails and torn
//! lines, rewriting reclaimed sidecars, removing `.reclaim` leftovers). A
//! reader beside a live owner must not repair, so this filesystem skips the
//! repairs and refuses writes; the replayed records are unaffected.

use std::sync::Arc;

use eukhe_chord::context::Context;
use eukhe_durable::env::{
    BinaryReader, CreateDirOptions, DirReader, FileError, FileErrorCode, FileInfo, FileSystem,
    FileWatcher, NativeExecutionEnv, NativeExecutionEnvOptions, OnWatchChange,
    OpenBinaryReaderOptions, ReadTextLinesOptions, RemoveOptions, TempFileOptions, TextLineReader,
    WatchTarget,
};
use eukhe_durable::errors::StorageError;
use eukhe_durable::storage::jsonl::{JsonlStorage, JsonlStorageOptions};
use futures::future::BoxFuture;
use futures::FutureExt;

/// Open the storage in `directory` (which must exist) without writing to it.
///
/// # Errors
///
/// The files cannot be read or hold corrupt committed data.
pub(super) async fn open_read_only(
    directory: &str,
    cx: &Context,
) -> Result<JsonlStorage, StorageError> {
    let fs = ReadOnlyFs {
        native: NativeExecutionEnv::new(NativeExecutionEnvOptions {
            cwd: directory.to_owned(),
            ..NativeExecutionEnvOptions::default()
        }),
    };
    JsonlStorage::open(
        directory,
        Arc::new(fs),
        cx,
        JsonlStorageOptions { fsync: false },
    )
    .await
}

/// The native filesystem with repairs skipped and writes refused.
struct ReadOnlyFs {
    native: NativeExecutionEnv,
}

fn refused<'a, T: Send + 'a>(path: &str) -> BoxFuture<'a, Result<T, FileError>> {
    let error = FileError::new(
        FileErrorCode::NotSupported,
        "read-only session view",
        Some(path.to_owned()),
    );
    futures::future::ready(Err(error)).boxed()
}

fn skipped<'a>() -> BoxFuture<'a, Result<(), FileError>> {
    futures::future::ready(Ok(())).boxed()
}

impl FileSystem for ReadOnlyFs {
    fn id(&self) -> &str {
        self.native.id()
    }

    fn cwd(&self) -> &str {
        self.native.cwd()
    }

    fn absolute_path<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<String, FileError>> {
        self.native.absolute_path(path, cx)
    }

    fn join_path<'a>(
        &'a self,
        parts: &'a [&'a str],
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<String, FileError>> {
        self.native.join_path(parts, cx)
    }

    fn read_text_file<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<String, FileError>> {
        self.native.read_text_file(path, cx)
    }

    fn open_text_line_reader<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Box<dyn TextLineReader>, FileError>> {
        self.native.open_text_line_reader(path, cx)
    }

    fn read_text_lines<'a>(
        &'a self,
        path: &'a str,
        options: ReadTextLinesOptions,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Vec<String>, FileError>> {
        self.native.read_text_lines(path, options, cx)
    }

    fn read_binary_file<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Vec<u8>, FileError>> {
        self.native.read_binary_file(path, cx)
    }

    fn open_binary_reader<'a>(
        &'a self,
        path: &'a str,
        options: OpenBinaryReaderOptions,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Box<dyn BinaryReader>, FileError>> {
        self.native.open_binary_reader(path, options, cx)
    }

    fn write_file<'a>(
        &'a self,
        path: &'a str,
        _content: &'a [u8],
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>> {
        refused(path)
    }

    fn append_file<'a>(
        &'a self,
        path: &'a str,
        _content: &'a [u8],
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>> {
        refused(path)
    }

    /// Recovery's tail repair; the replay already ignores the tail.
    fn truncate_file<'a>(
        &'a self,
        _path: &'a str,
        _size: f64,
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>> {
        skipped()
    }

    fn flush_file<'a>(
        &'a self,
        _path: &'a str,
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>> {
        skipped()
    }

    fn rename_file<'a>(
        &'a self,
        source_path: &'a str,
        _destination_path: &'a str,
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>> {
        refused(source_path)
    }

    fn file_info<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<FileInfo, FileError>> {
        self.native.file_info(path, cx)
    }

    fn list_dir<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Vec<FileInfo>, FileError>> {
        self.native.list_dir(path, cx)
    }

    fn open_dir_reader<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Box<dyn DirReader>, FileError>> {
        self.native.open_dir_reader(path, cx)
    }

    fn watch<'a>(
        &'a self,
        targets: &'a [WatchTarget],
        on_change: OnWatchChange,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Box<dyn FileWatcher>, FileError>> {
        self.native.watch(targets, on_change, cx)
    }

    fn canonical_path<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<String, FileError>> {
        self.native.canonical_path(path, cx)
    }

    fn exists<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<bool, FileError>> {
        self.native.exists(path, cx)
    }

    /// The storage opens an existing directory: accept it, never create one.
    fn create_dir<'a>(
        &'a self,
        path: &'a str,
        _options: CreateDirOptions,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>> {
        async move {
            if self.native.exists(path, cx).await? {
                Ok(())
            } else {
                Err(FileError::new(
                    FileErrorCode::NotFound,
                    "read-only session view of a missing directory",
                    Some(path.to_owned()),
                ))
            }
        }
        .boxed()
    }

    /// Recovery's removal of `.reclaim` leftovers.
    fn remove<'a>(
        &'a self,
        _path: &'a str,
        _options: RemoveOptions,
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>> {
        skipped()
    }

    fn create_temp_dir<'a>(
        &'a self,
        prefix: Option<&'a str>,
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<String, FileError>> {
        refused(prefix.unwrap_or("tmp-"))
    }

    fn create_temp_file<'a>(
        &'a self,
        _options: TempFileOptions,
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<String, FileError>> {
        refused(self.native.cwd())
    }

    fn cleanup<'a>(&'a self, cx: &'a Context) -> BoxFuture<'a, ()> {
        self.native.cleanup(cx)
    }
}
