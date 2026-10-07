//! The readers `NativeExecutionEnv` opens: `NodeTextLineReader`,
//! `NodeBinaryReader`, and `NodeDirReader` of `env/node.ts`.

use std::fs::{File, ReadDir};
use std::io;
use std::os::unix::fs::FileExt;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::Context;
use futures::future::BoxFuture;

use super::super::decode::StreamDecoder;
use super::super::line_scan::{is_safe_integer, LineScanner};
use super::super::node_error::{fd_error, fs_error};
use super::super::{
    BinaryReader, DirPage, DirReader, FileError, FileErrorCode, FileInfo, LineRange, LineScan,
    TextLine, TextLineReader,
};
use super::{abort_result, blocking, file_info_from_metadata, paths};

/// Bytes the text line reader and the line scan read at a time.
const READ_CHUNK: usize = 64 * 1024;
/// Largest single read of a `BinaryReader`, so a huge `length` allocates only
/// as much as the file yields.
const BINARY_READ_CHUNK: u64 = 1024 * 1024;

fn closed_result<T>(what: &str, path: &str) -> Result<T, FileError> {
    Err(FileError::new(
        FileErrorCode::Invalid,
        format!("{what} is closed"),
        Some(path.to_owned()),
    ))
}

/// Up to `length` bytes of `file` at `offset`, on the blocking pool.
async fn read_at(file: Arc<File>, offset: u64, length: usize) -> io::Result<Vec<u8>> {
    blocking(move || {
        let mut buffer = vec![0; length];
        let read = loop {
            match file.read_at(&mut buffer, offset) {
                Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
                result => break result?,
            }
        };
        buffer.truncate(read);
        Ok(buffer)
    })
    .await
}

struct TextLineState {
    file: Option<Arc<File>>,
    decoder: StreamDecoder,
    byte_offset: u64,
    buffered: String,
    ended: bool,
}

/// Strict LF reader; it reports whether its final line was newline-terminated.
pub(super) struct NativeTextLineReader {
    path: String,
    state: tokio::sync::Mutex<TextLineState>,
}

impl NativeTextLineReader {
    pub(super) fn new(file: File, path: String) -> Self {
        Self {
            path,
            state: tokio::sync::Mutex::new(TextLineState {
                file: Some(Arc::new(file)),
                decoder: StreamDecoder::new(),
                byte_offset: 0,
                buffered: String::new(),
                ended: false,
            }),
        }
    }

    async fn read_line_inner(&self, cx: &Context) -> Result<Option<TextLine>, FileError> {
        abort_result(cx, Some(&self.path))?;
        let mut state = self.state.lock().await;
        let Some(file) = state.file.clone() else {
            return closed_result("Text line reader", &self.path);
        };
        loop {
            if let Some(newline) = state.buffered.find('\n') {
                let text = state.buffered[..newline].to_owned();
                state.buffered.drain(..=newline);
                return Ok(Some(TextLine {
                    text,
                    terminated: true,
                }));
            }
            if state.ended {
                if state.buffered.is_empty() {
                    return Ok(None);
                }
                let text = std::mem::take(&mut state.buffered);
                return Ok(Some(TextLine {
                    text,
                    terminated: false,
                }));
            }
            // Explicit positions allow an aborted read to be retried without
            // skipping bytes.
            let chunk = read_at(Arc::clone(&file), state.byte_offset, READ_CHUNK)
                .await
                .map_err(|error| fd_error(error, "read", Some(&self.path)))?;
            abort_result(cx, Some(&self.path))?;
            state.byte_offset += chunk.len() as u64;
            if chunk.is_empty() {
                let text = state.decoder.finish();
                state.buffered.push_str(&text);
                state.ended = true;
            } else {
                let text = state.decoder.decode(&chunk);
                state.buffered.push_str(&text);
            }
        }
    }
}

impl TextLineReader for NativeTextLineReader {
    fn read_line<'a>(
        &'a self,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<TextLine>, FileError>> {
        Box::pin(self.read_line_inner(cx))
    }

    fn close<'a>(&'a self, _cx: &'a Context) -> BoxFuture<'a, ()> {
        Box::pin(async move {
            let mut state = self.state.lock().await;
            // Dropping the last handle closes the file; closing is best-effort.
            state.file = None;
            state.buffered.clear();
        })
    }
}

/// Positional reads from one opened regular file.
pub(super) struct NativeBinaryReader {
    path: String,
    file: Mutex<Option<Arc<File>>>,
}

impl NativeBinaryReader {
    pub(super) fn new(file: File, path: String) -> Self {
        Self {
            path,
            file: Mutex::new(Some(Arc::new(file))),
        }
    }

    fn open_file(&self) -> Option<Arc<File>> {
        self.file
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone()
    }

    async fn info_inner(&self, cx: &Context) -> Result<FileInfo, FileError> {
        abort_result(cx, Some(&self.path))?;
        let Some(file) = self.open_file() else {
            return closed_result("Binary reader", &self.path);
        };
        let metadata = blocking(move || file.metadata())
            .await
            .map_err(|error| fd_error(error, "fstat", Some(&self.path)))?;
        file_info_from_metadata(&self.path, &metadata)
    }

    #[allow(
        clippy::cast_possible_truncation,
        clippy::cast_sign_loss,
        reason = "offset and length are checked to be non-negative safe integers first"
    )]
    async fn read_inner(
        &self,
        offset: f64,
        length: f64,
        cx: &Context,
    ) -> Result<Vec<u8>, FileError> {
        abort_result(cx, Some(&self.path))?;
        let Some(file) = self.open_file() else {
            return closed_result("Binary reader", &self.path);
        };
        if !is_safe_integer(offset) || offset < 0.0 || !is_safe_integer(length) || length < 0.0 {
            return Err(FileError::new(
                FileErrorCode::Invalid,
                "Offset and length must be non-negative safe integers",
                Some(self.path.clone()),
            ));
        }
        let (offset, length) = (offset as u64, length as u64);
        let mut bytes = Vec::new();
        let mut total = 0;
        while total < length {
            let size = (length - total).min(BINARY_READ_CHUNK) as usize;
            let chunk = read_at(Arc::clone(&file), offset + total, size)
                .await
                .map_err(|error| fd_error(error, "read", Some(&self.path)))?;
            abort_result(cx, Some(&self.path))?;
            if chunk.is_empty() {
                break;
            }
            total += chunk.len() as u64;
            if bytes.is_empty() {
                bytes = chunk;
            } else {
                bytes.extend_from_slice(&chunk);
            }
        }
        Ok(bytes)
    }

    async fn scan_lines_inner(
        &self,
        range: LineRange,
        cx: &Context,
    ) -> Result<LineScan, FileError> {
        abort_result(cx, Some(&self.path))?;
        let Some(file) = self.open_file() else {
            return closed_result("Binary reader", &self.path);
        };
        let Ok(mut scanner) = LineScanner::new(range.start_line, range.end_line) else {
            return Err(FileError::new(
                FileErrorCode::Invalid,
                "Invalid line range",
                Some(self.path.clone()),
            ));
        };
        let mut position = 0;
        loop {
            let chunk = read_at(Arc::clone(&file), position, READ_CHUNK)
                .await
                .map_err(|error| fd_error(error, "read", Some(&self.path)))?;
            abort_result(cx, Some(&self.path))?;
            if chunk.is_empty() {
                return Ok(scanner.finish());
            }
            scanner.push(&chunk);
            position += chunk.len() as u64;
        }
    }
}

impl BinaryReader for NativeBinaryReader {
    fn info<'a>(&'a self, cx: &'a Context) -> BoxFuture<'a, Result<FileInfo, FileError>> {
        Box::pin(self.info_inner(cx))
    }

    fn read<'a>(
        &'a self,
        offset: f64,
        length: f64,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Vec<u8>, FileError>> {
        Box::pin(self.read_inner(offset, length, cx))
    }

    fn scan_lines<'a>(
        &'a self,
        range: LineRange,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<LineScan, FileError>> {
        Box::pin(self.scan_lines_inner(range, cx))
    }

    fn close<'a>(&'a self, _cx: &'a Context) -> BoxFuture<'a, ()> {
        Box::pin(async move {
            // Dropping the last handle closes the file; closing is best-effort.
            self.file
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .take();
        })
    }
}

struct DirState {
    entries: Option<ReadDir>,
    done: bool,
}

/// Pages of one directory's entries, in the order the file system returns
/// them.
pub(super) struct NativeDirReader {
    path: String,
    state: tokio::sync::Mutex<DirState>,
}

impl NativeDirReader {
    pub(super) fn new(entries: ReadDir, path: String) -> Self {
        Self {
            path,
            state: tokio::sync::Mutex::new(DirState {
                entries: Some(entries),
                done: false,
            }),
        }
    }

    #[allow(
        clippy::cast_possible_truncation,
        clippy::cast_sign_loss,
        reason = "max_entries is checked to be a positive safe integer first"
    )]
    async fn next_inner(&self, max_entries: f64, cx: &Context) -> Result<DirPage, FileError> {
        abort_result(cx, Some(&self.path))?;
        let mut state = self.state.lock().await;
        if state.entries.is_none() {
            return closed_result("Directory reader", &self.path);
        }
        if !is_safe_integer(max_entries) || max_entries <= 0.0 {
            return Err(FileError::new(
                FileErrorCode::Invalid,
                "maxEntries must be a positive safe integer",
                Some(self.path.clone()),
            ));
        }
        let max_entries = max_entries as u64;
        let mut entries = Vec::new();
        while !state.done && (entries.len() as u64) < max_entries {
            let Some(mut iterator) = state.entries.take() else {
                return closed_result("Directory reader", &self.path);
            };
            let (iterator, entry) = blocking(move || {
                let entry = iterator.next();
                Ok((iterator, entry))
            })
            .await
            .map_err(|error| fd_error(error, "readdir", Some(&self.path)))?;
            state.entries = Some(iterator);
            let entry = match entry {
                None => {
                    state.done = true;
                    break;
                }
                Some(Err(error)) => return Err(fd_error(error, "readdir", Some(&self.path))),
                Some(Ok(entry)) => entry,
            };
            abort_result(cx, Some(&self.path))?;
            let name = entry.file_name().to_string_lossy().into_owned();
            let entry_path = paths::resolve(&[&self.path, &name]);
            let lstat_path = entry_path.clone();
            let metadata = match blocking(move || std::fs::symlink_metadata(lstat_path)).await {
                Ok(metadata) => metadata,
                // Removed between enumeration and lstat: not part of the listing
                // any more.
                Err(error) if error.kind() == io::ErrorKind::NotFound => continue,
                Err(error) => return Err(fs_error(error, "lstat", &entry_path)),
            };
            if let Ok(info) = file_info_from_metadata(&entry_path, &metadata) {
                entries.push(info);
            }
        }
        Ok(DirPage {
            entries,
            done: state.done,
        })
    }
}

impl DirReader for NativeDirReader {
    fn next<'a>(
        &'a self,
        max_entries: f64,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<DirPage, FileError>> {
        Box::pin(self.next_inner(max_entries, cx))
    }

    fn close<'a>(&'a self, _cx: &'a Context) -> BoxFuture<'a, ()> {
        Box::pin(async move {
            let mut state = self.state.lock().await;
            state.entries = None;
        })
    }
}
