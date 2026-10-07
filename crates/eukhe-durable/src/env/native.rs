//! The local execution environment: the host's file system and shell. Port
//! of `env/node.ts` (`NodeExecutionEnv`) for Linux and macOS.
//!
//! The Windows branches of `node.ts` (Git Bash discovery, `taskkill`) are not
//! ported: the port targets Linux and macOS only.

mod exec;
mod paths;
mod readers;
#[cfg(test)]
mod tests;

use std::collections::{BTreeMap, HashSet};
use std::fs::Metadata;
use std::future::Future;
use std::io;
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
use std::sync::{Arc, Mutex};

use eukhe_chord::context::Context;
use futures::future::BoxFuture;
use nix::fcntl::OFlag;

use super::native_watch::{NativeFileWatcher, NativeWatchOptions};
use super::node_error::{fd_error, fs_error, fs_error_dest, uv_code};
use super::{
    BinaryReader, CreateDirOptions, DirReader, ExecCommand, ExecutionError, FileError,
    FileErrorCode, FileInfo, FileKind, FileSystem, FileWatcher, OnWatchChange,
    OpenBinaryReaderOptions, ReadTextLinesOptions, RemoveOptions, Shell, ShellExecOptions,
    ShellExecResult, TempFileOptions, TextLineReader, WatchTarget,
};
use readers::{NativeBinaryReader, NativeDirReader, NativeTextLineReader};

pub(crate) use paths::resolve_path;

/// Options of [`NativeExecutionEnv::new`].
#[derive(Clone, Debug, Default)]
pub struct NativeExecutionEnvOptions {
    /// Directory relative paths and commands resolve against.
    pub cwd: String,
    /// The shell for string commands; default `/bin/bash`, else `bash` on
    /// `PATH`, else `sh`.
    pub shell_path: Option<String>,
    /// Variables commands get on top of the process environment.
    pub shell_env: Option<BTreeMap<String, String>>,
    pub watch: NativeWatchOptions,
}

/// The process's own file system and shell: the TS `NodeExecutionEnv`.
pub struct NativeExecutionEnv {
    cwd: String,
    shell_path: Option<String>,
    shell_env: Option<BTreeMap<String, String>>,
    watch_options: NativeWatchOptions,
    /// Process groups of the commands still running.
    active_child_pids: Arc<Mutex<HashSet<u32>>>,
    #[cfg(test)]
    spill_hook: Option<exec::SpillHook>,
}

impl NativeExecutionEnv {
    /// Every local environment sees the same files.
    pub const ID: &'static str = "node:local";

    #[must_use]
    pub fn new(options: NativeExecutionEnvOptions) -> Self {
        Self {
            cwd: options.cwd,
            shell_path: options.shell_path,
            shell_env: options.shell_env,
            watch_options: options.watch,
            active_child_pids: Arc::new(Mutex::new(HashSet::new())),
            #[cfg(test)]
            spill_hook: None,
        }
    }

    fn resolve(&self, path: &str) -> String {
        resolve_path(&self.cwd, path)
    }
}

/// `abortResult`: an `aborted` failure when the context is cancelled.
pub(super) fn abort_result(cx: &Context, path: Option<&str>) -> Result<(), FileError> {
    if cx.aborted() {
        return Err(FileError::new(
            FileErrorCode::Aborted,
            "aborted",
            path.map(str::to_owned),
        ));
    }
    Ok(())
}

/// The error Node's `fs` operations reject with when their signal aborts.
fn abort_error(path: &str) -> FileError {
    FileError::new(
        FileErrorCode::Aborted,
        "The operation was aborted",
        Some(path.to_owned()),
    )
}

/// Run blocking file system work on tokio's blocking pool.
pub(super) async fn blocking<T, F>(work: F) -> io::Result<T>
where
    F: FnOnce() -> io::Result<T> + Send + 'static,
    T: Send + 'static,
{
    match tokio::task::spawn_blocking(work).await {
        Ok(result) => result,
        Err(error) => Err(io::Error::other(error)),
    }
}

/// Await `work` unless the context aborts first, like Node's `fs` calls that
/// take a `signal`.
async fn with_signal<T>(
    work: impl Future<Output = io::Result<T>>,
    cx: &Context,
    path: &str,
) -> Result<io::Result<T>, FileError> {
    match cx.abort_signal() {
        None => Ok(work.await),
        Some(signal) => tokio::select! {
            result = work => Ok(result),
            _ = signal.cancelled() => Err(abort_error(path)),
        },
    }
}

/// Node's `stats.mtimeMs`.
#[allow(
    clippy::cast_precision_loss,
    reason = "Node computes mtimeMs as a double the same way"
)]
fn mtime_ms(metadata: &Metadata) -> f64 {
    metadata.mtime() as f64 * 1000.0 + metadata.mtime_nsec() as f64 / 1_000_000.0
}

/// `fileInfoFromStats`.
pub(super) fn file_info_from_metadata(
    path: &str,
    metadata: &Metadata,
) -> Result<FileInfo, FileError> {
    let file_type = metadata.file_type();
    let kind = if file_type.is_file() {
        FileKind::File
    } else if file_type.is_dir() {
        FileKind::Directory
    } else if file_type.is_symlink() {
        FileKind::Symlink
    } else {
        return Err(FileError::new(
            FileErrorCode::Invalid,
            "Unsupported file type",
            Some(path.to_owned()),
        ));
    };
    Ok(FileInfo {
        name: paths::basename(path).to_owned(),
        path: path.to_owned(),
        kind,
        size: metadata.size(),
        mtime_ms: mtime_ms(metadata),
    })
}

/// Lossless enough path string of an OS path, as Node decodes file names.
fn path_string(path: &std::path::Path) -> String {
    path.to_string_lossy().into_owned()
}

fn symlink_refused(path: &str, cause: io::Error) -> FileError {
    FileError::new(
        FileErrorCode::Invalid,
        "Refusing to follow a symbolic link",
        Some(path.to_owned()),
    )
    .with_cause(Arc::new(cause))
}

/// `mkdir(path, { recursive })`.
async fn make_dir(path: &str, recursive: bool) -> Result<(), FileError> {
    let target = path.to_owned();
    blocking(move || {
        if recursive {
            std::fs::create_dir_all(&target)
        } else {
            std::fs::create_dir(&target)
        }
    })
    .await
    .map_err(|error| fs_error(error, "mkdir", path))
}

/// Six random characters of `mkdtemp`'s template.
fn random_suffix() -> String {
    const ALPHABET: &[u8] = b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789";
    uuid::Uuid::new_v4().as_bytes()[..6]
        .iter()
        .map(|byte| char::from(ALPHABET[usize::from(*byte) % ALPHABET.len()]))
        .collect()
}

/// `fs.mkdtemp(prefix)`.
async fn make_temp_dir(prefix: &str) -> Result<String, FileError> {
    loop {
        let path = format!("{prefix}{}", random_suffix());
        let target = path.clone();
        match blocking(move || std::fs::create_dir(&target)).await {
            Ok(()) => return Ok(path),
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {}
            Err(error) => return Err(fs_error(error, "mkdtemp", &path)),
        }
    }
}

impl NativeExecutionEnv {
    async fn watch_inner(
        &self,
        targets: &[WatchTarget],
        on_change: OnWatchChange,
        cx: &Context,
    ) -> Result<Box<dyn FileWatcher>, FileError> {
        abort_result(cx, None)?;
        let cwd = self.cwd.clone();
        let resolve = move |path: &str| resolve_path(&cwd, path);
        let watcher =
            NativeFileWatcher::open(targets, &resolve, on_change, &self.watch_options).await?;
        if let Err(error) = abort_result(cx, None) {
            watcher.close(cx).await;
            return Err(error);
        }
        Ok(Box::new(watcher))
    }

    async fn open_text_line_reader_inner(
        &self,
        path: &str,
        cx: &Context,
    ) -> Result<Box<dyn TextLineReader>, FileError> {
        let resolved = self.resolve(path);
        abort_result(cx, Some(&resolved))?;
        let target = resolved.clone();
        let file = blocking(move || std::fs::File::open(target))
            .await
            .map_err(|error| fs_error(error, "open", &resolved))?;
        abort_result(cx, Some(&resolved))?;
        Ok(Box::new(NativeTextLineReader::new(file, resolved)))
    }

    async fn read_text_file_inner(&self, path: &str, cx: &Context) -> Result<String, FileError> {
        let bytes = self.read_binary_file_inner(path, cx).await?;
        Ok(super::decode::Utf8Decoder::new().decode_all(&bytes))
    }

    async fn read_text_lines_inner(
        &self,
        path: &str,
        options: ReadTextLinesOptions,
        cx: &Context,
    ) -> Result<Vec<String>, FileError> {
        if options.max_lines.is_some_and(|max_lines| max_lines <= 0.0) {
            return Ok(Vec::new());
        }
        let reader = self.open_text_line_reader_inner(path, cx).await?;
        let mut lines = Vec::new();
        let result = loop {
            #[allow(
                clippy::cast_precision_loss,
                reason = "a line count is far below 2^53, where the conversion is exact"
            )]
            let read = lines.len() as f64;
            if options.max_lines.is_some_and(|max_lines| read >= max_lines) {
                break Ok(());
            }
            match reader.read_line(cx).await {
                Err(error) => break Err(error),
                Ok(None) => break Ok(()),
                Ok(Some(line)) => lines.push(line.text),
            }
        };
        reader.close(cx).await;
        result.map(|()| lines)
    }

    async fn read_binary_file_inner(&self, path: &str, cx: &Context) -> Result<Vec<u8>, FileError> {
        let resolved = self.resolve(path);
        abort_result(cx, Some(&resolved))?;
        let target = resolved.clone();
        let read = blocking(move || {
            use std::io::Read;
            let mut file = std::fs::File::open(&target)
                .map_err(|error| io::Error::new(error.kind(), SyscallError("open", error)))?;
            let mut bytes = Vec::new();
            file.read_to_end(&mut bytes)
                .map_err(|error| io::Error::new(error.kind(), SyscallError("read", error)))?;
            Ok(bytes)
        });
        with_signal(read, cx, &resolved)
            .await?
            .map_err(|error| syscall_error(error, &resolved))
    }

    async fn open_binary_reader_inner(
        &self,
        path: &str,
        options: OpenBinaryReaderOptions,
        cx: &Context,
    ) -> Result<Box<dyn BinaryReader>, FileError> {
        let resolved = self.resolve(path);
        abort_result(cx, Some(&resolved))?;
        let no_follow = options.no_follow;
        let target = resolved.clone();
        let opened = tokio::task::spawn_blocking(move || {
            // Nonblocking, so opening a FIFO does not wait for a writer.
            let mut flags = OFlag::O_NONBLOCK;
            if no_follow {
                flags |= OFlag::O_NOFOLLOW;
            }
            let file = std::fs::OpenOptions::new()
                .read(true)
                .custom_flags(flags.bits())
                .open(&target)
                .map_err(|error| ("open", error))?;
            let metadata = file.metadata().map_err(|error| ("fstat", error))?;
            Ok::<_, (&'static str, io::Error)>((file, metadata))
        });
        let (file, metadata) = match opened.await {
            Ok(Ok(opened)) => opened,
            Ok(Err((syscall, error))) => {
                // O_NOFOLLOW reports a final-component symlink as ELOOP (EMLINK
                // on some BSDs).
                if no_follow && matches!(uv_code(&error), "ELOOP" | "EMLINK") {
                    return Err(symlink_refused(&resolved, error));
                }
                return Err(if syscall == "open" {
                    fs_error(error, syscall, &resolved)
                } else {
                    fd_error(error, syscall, Some(&resolved))
                });
            }
            Err(join_error) => {
                return Err(fd_error(
                    io::Error::other(join_error),
                    "open",
                    Some(&resolved),
                ));
            }
        };
        if !metadata.is_file() {
            drop(file);
            return Err(if metadata.is_dir() {
                FileError::new(
                    FileErrorCode::IsDirectory,
                    "EISDIR: illegal operation on a directory, read",
                    Some(resolved),
                )
            } else {
                FileError::new(FileErrorCode::Invalid, "Not a regular file", Some(resolved))
            });
        }
        abort_result(cx, Some(&resolved))?;
        Ok(Box::new(NativeBinaryReader::new(file, resolved)))
    }

    async fn write_file_inner(
        &self,
        path: &str,
        content: &[u8],
        cx: &Context,
    ) -> Result<(), FileError> {
        let resolved = self.resolve(path);
        abort_result(cx, Some(&resolved))?;
        make_dir(&paths::resolve(&[&resolved, ".."]), true).await?;
        abort_result(cx, Some(&resolved))?;
        let target = resolved.clone();
        let content = content.to_vec();
        let write = blocking(move || {
            use std::io::Write;
            let mut file = std::fs::File::create(&target)
                .map_err(|error| io::Error::new(error.kind(), SyscallError("open", error)))?;
            file.write_all(&content)
                .map_err(|error| io::Error::new(error.kind(), SyscallError("write", error)))
        });
        with_signal(write, cx, &resolved)
            .await?
            .map_err(|error| syscall_error(error, &resolved))
    }

    async fn append_file_inner(
        &self,
        path: &str,
        content: &[u8],
        cx: &Context,
    ) -> Result<(), FileError> {
        let resolved = self.resolve(path);
        abort_result(cx, Some(&resolved))?;
        make_dir(&paths::resolve(&[&resolved, ".."]), true).await?;
        abort_result(cx, Some(&resolved))?;
        let target = resolved.clone();
        let content = content.to_vec();
        blocking(move || {
            use std::io::Write;
            let mut file = std::fs::OpenOptions::new()
                .append(true)
                .create(true)
                .open(&target)
                .map_err(|error| io::Error::new(error.kind(), SyscallError("open", error)))?;
            file.write_all(&content)
                .map_err(|error| io::Error::new(error.kind(), SyscallError("write", error)))
        })
        .await
        .map_err(|error| syscall_error(error, &resolved))?;
        abort_result(cx, Some(&resolved))
    }

    #[allow(
        clippy::cast_possible_truncation,
        clippy::cast_sign_loss,
        reason = "size is checked to be a non-negative safe integer first"
    )]
    async fn truncate_file_inner(
        &self,
        path: &str,
        size: f64,
        cx: &Context,
    ) -> Result<(), FileError> {
        let resolved = self.resolve(path);
        abort_result(cx, Some(&resolved))?;
        if !super::line_scan::is_safe_integer(size) || size < 0.0 {
            return Err(FileError::new(
                FileErrorCode::Invalid,
                "File size must be a non-negative safe integer",
                Some(resolved),
            ));
        }
        let size = size as u64;
        let target = resolved.clone();
        blocking(move || {
            let file = std::fs::OpenOptions::new()
                .read(true)
                .write(true)
                .open(&target)
                .map_err(|error| io::Error::new(error.kind(), SyscallError("open", error)))?;
            file.set_len(size)
                .map_err(|error| io::Error::new(error.kind(), SyscallError("ftruncate", error)))
        })
        .await
        .map_err(|error| syscall_error(error, &resolved))?;
        abort_result(cx, Some(&resolved))
    }

    async fn flush_file_inner(&self, path: &str, cx: &Context) -> Result<(), FileError> {
        let resolved = self.resolve(path);
        abort_result(cx, Some(&resolved))?;
        let target = resolved.clone();
        let flushed = blocking(move || {
            let file = std::fs::OpenOptions::new()
                .read(true)
                .write(true)
                .open(&target)
                .map_err(|error| io::Error::new(error.kind(), SyscallError("open", error)))?;
            let metadata = file
                .metadata()
                .map_err(|error| io::Error::new(error.kind(), SyscallError("fstat", error)))?;
            // POSIX refuses to open a directory for writing; check explicitly
            // like the TS does for Windows.
            if metadata.is_dir() {
                return Ok(false);
            }
            file.sync_all()
                .map_err(|error| io::Error::new(error.kind(), SyscallError("fsync", error)))?;
            Ok(true)
        })
        .await
        .map_err(|error| syscall_error(error, &resolved))?;
        if !flushed {
            return Err(FileError::new(
                FileErrorCode::IsDirectory,
                "Is a directory",
                Some(resolved),
            ));
        }
        abort_result(cx, Some(&resolved))
    }

    async fn rename_file_inner(
        &self,
        source_path: &str,
        destination_path: &str,
        cx: &Context,
    ) -> Result<(), FileError> {
        let source = self.resolve(source_path);
        let destination = self.resolve(destination_path);
        abort_result(cx, Some(&destination))?;
        let (from, to) = (source.clone(), destination.clone());
        blocking(move || std::fs::rename(from, to))
            .await
            .map_err(|error| fs_error_dest(error, "rename", &source, &destination))
    }

    async fn file_info_inner(&self, path: &str, cx: &Context) -> Result<FileInfo, FileError> {
        let resolved = self.resolve(path);
        abort_result(cx, Some(&resolved))?;
        let target = resolved.clone();
        let metadata = blocking(move || std::fs::symlink_metadata(target))
            .await
            .map_err(|error| fs_error(error, "lstat", &resolved))?;
        file_info_from_metadata(&resolved, &metadata)
    }

    async fn list_dir_inner(&self, path: &str, cx: &Context) -> Result<Vec<FileInfo>, FileError> {
        let resolved = self.resolve(path);
        abort_result(cx, Some(&resolved))?;
        let target = resolved.clone();
        let mut names = blocking(move || {
            std::fs::read_dir(target)?
                .map(|entry| entry.map(|entry| entry.file_name().to_string_lossy().into_owned()))
                .collect::<io::Result<Vec<_>>>()
        })
        .await
        .map_err(|error| fs_error(error, "scandir", &resolved))?;
        // libuv's scandir sorts entries with strcmp.
        names.sort_unstable_by(|a, b| a.as_bytes().cmp(b.as_bytes()));
        let mut infos = Vec::with_capacity(names.len());
        for name in names {
            abort_result(cx, Some(&resolved))?;
            let entry_path = paths::resolve(&[&resolved, &name]);
            let target = entry_path.clone();
            let metadata = blocking(move || std::fs::symlink_metadata(target))
                .await
                .map_err(|error| fs_error(error, "lstat", &entry_path))?;
            if let Ok(info) = file_info_from_metadata(&entry_path, &metadata) {
                infos.push(info);
            }
        }
        Ok(infos)
    }

    async fn open_dir_reader_inner(
        &self,
        path: &str,
        cx: &Context,
    ) -> Result<Box<dyn DirReader>, FileError> {
        let resolved = self.resolve(path);
        abort_result(cx, Some(&resolved))?;
        let target = resolved.clone();
        let entries = blocking(move || std::fs::read_dir(target))
            .await
            .map_err(|error| fs_error(error, "opendir", &resolved))?;
        abort_result(cx, Some(&resolved))?;
        Ok(Box::new(NativeDirReader::new(entries, resolved)))
    }

    async fn canonical_path_inner(&self, path: &str, cx: &Context) -> Result<String, FileError> {
        let resolved = self.resolve(path);
        abort_result(cx, Some(&resolved))?;
        let target = resolved.clone();
        blocking(move || std::fs::canonicalize(target))
            .await
            .map(|path| path_string(&path))
            .map_err(|error| fs_error(error, "realpath", &resolved))
    }

    async fn exists_inner(&self, path: &str, cx: &Context) -> Result<bool, FileError> {
        match self.file_info_inner(path, cx).await {
            Ok(_) => Ok(true),
            Err(error) if error.code == FileErrorCode::NotFound => Ok(false),
            Err(error) => Err(error),
        }
    }

    async fn create_dir_inner(
        &self,
        path: &str,
        options: CreateDirOptions,
        cx: &Context,
    ) -> Result<(), FileError> {
        let resolved = self.resolve(path);
        abort_result(cx, Some(&resolved))?;
        make_dir(&resolved, options.recursive).await
    }

    async fn remove_inner(
        &self,
        path: &str,
        options: RemoveOptions,
        cx: &Context,
    ) -> Result<(), FileError> {
        let resolved = self.resolve(path);
        abort_result(cx, Some(&resolved))?;
        let target = resolved.clone();
        let metadata = match blocking(move || std::fs::symlink_metadata(target)).await {
            Ok(metadata) => metadata,
            Err(error) if options.force && error.kind() == io::ErrorKind::NotFound => return Ok(()),
            Err(error) => return Err(fs_error(error, "lstat", &resolved)),
        };
        if metadata.is_dir() && !options.recursive {
            // Node's ERR_FS_EISDIR is not one of the codes `toFileError` maps.
            return Err(FileError::new(
                FileErrorCode::Unknown,
                format!("Path is a directory: rm returned EISDIR (is a directory) {resolved}"),
                Some(resolved),
            ));
        }
        let target = resolved.clone();
        let is_dir = metadata.is_dir();
        blocking(move || {
            if is_dir {
                std::fs::remove_dir_all(&target)
                    .map_err(|error| io::Error::new(error.kind(), SyscallError("rm", error)))
            } else {
                std::fs::remove_file(&target)
                    .map_err(|error| io::Error::new(error.kind(), SyscallError("unlink", error)))
            }
        })
        .await
        .or_else(|error| {
            if options.force && error.kind() == io::ErrorKind::NotFound {
                Ok(())
            } else {
                Err(syscall_error(error, &resolved))
            }
        })
    }

    async fn create_temp_dir_inner(
        &self,
        prefix: Option<&str>,
        cx: &Context,
    ) -> Result<String, FileError> {
        create_temp_dir(prefix, cx).await
    }

    async fn create_temp_file_inner(
        &self,
        options: TempFileOptions,
        cx: &Context,
    ) -> Result<String, FileError> {
        create_temp_file(&options, cx).await
    }

    fn kill_active_children(&self) {
        let pids: Vec<u32> = {
            let mut active = self
                .active_child_pids
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            active.drain().collect()
        };
        for pid in pids {
            exec::kill_process_tree(pid);
        }
    }
}

/// `createTempDir` of `NodeExecutionEnv`.
async fn create_temp_dir(prefix: Option<&str>, cx: &Context) -> Result<String, FileError> {
    abort_result(cx, None)?;
    let prefix = prefix.unwrap_or("tmp-");
    make_temp_dir(&paths::join(&[&paths::tmp_dir(), prefix])).await
}

/// `createTempFile` of `NodeExecutionEnv`.
pub(super) async fn create_temp_file(
    options: &TempFileOptions,
    cx: &Context,
) -> Result<String, FileError> {
    let dir = create_temp_dir(Some("tmp-"), cx).await?;
    let name = format!(
        "{}{}{}",
        options.prefix.as_deref().unwrap_or(""),
        uuid::Uuid::new_v4(),
        options.suffix.as_deref().unwrap_or("")
    );
    let file_path = paths::join(&[&dir, &name]);
    let target = file_path.clone();
    blocking(move || std::fs::write(target, b""))
        .await
        .map_err(|error| fs_error(error, "open", &file_path))?;
    Ok(file_path)
}

/// An I/O error tagged with the system call Node would name in its message.
#[derive(Debug, thiserror::Error)]
#[error("{1}")]
struct SyscallError(&'static str, #[source] io::Error);

/// The `FileError` of an error from a multi-step blocking operation:
/// `fs_error` with the syscall it was tagged with, `open` otherwise.
fn syscall_error(error: io::Error, path: &str) -> FileError {
    let kind = error.kind();
    match error.into_inner() {
        Some(inner) => match inner.downcast::<SyscallError>() {
            Ok(tagged) => {
                let SyscallError(syscall, source) = *tagged;
                fs_error(source, syscall, path)
            }
            Err(other) => fs_error(io::Error::new(kind, other), "open", path),
        },
        None => fs_error(io::Error::from(kind), "open", path),
    }
}

impl FileSystem for NativeExecutionEnv {
    fn id(&self) -> &str {
        Self::ID
    }

    fn cwd(&self) -> &str {
        &self.cwd
    }

    fn absolute_path<'a>(
        &'a self,
        path: &'a str,
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<String, FileError>> {
        Box::pin(async move { Ok(self.resolve(path)) })
    }

    fn join_path<'a>(
        &'a self,
        parts: &'a [&'a str],
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<String, FileError>> {
        Box::pin(async move { Ok(paths::join(parts)) })
    }

    fn read_text_file<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<String, FileError>> {
        Box::pin(self.read_text_file_inner(path, cx))
    }

    fn open_text_line_reader<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Box<dyn TextLineReader>, FileError>> {
        Box::pin(self.open_text_line_reader_inner(path, cx))
    }

    fn read_text_lines<'a>(
        &'a self,
        path: &'a str,
        options: ReadTextLinesOptions,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Vec<String>, FileError>> {
        Box::pin(self.read_text_lines_inner(path, options, cx))
    }

    fn read_binary_file<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Vec<u8>, FileError>> {
        Box::pin(self.read_binary_file_inner(path, cx))
    }

    fn open_binary_reader<'a>(
        &'a self,
        path: &'a str,
        options: OpenBinaryReaderOptions,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Box<dyn BinaryReader>, FileError>> {
        Box::pin(self.open_binary_reader_inner(path, options, cx))
    }

    fn write_file<'a>(
        &'a self,
        path: &'a str,
        content: &'a [u8],
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>> {
        Box::pin(self.write_file_inner(path, content, cx))
    }

    fn append_file<'a>(
        &'a self,
        path: &'a str,
        content: &'a [u8],
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>> {
        Box::pin(self.append_file_inner(path, content, cx))
    }

    fn truncate_file<'a>(
        &'a self,
        path: &'a str,
        size: f64,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>> {
        Box::pin(self.truncate_file_inner(path, size, cx))
    }

    fn flush_file<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>> {
        Box::pin(self.flush_file_inner(path, cx))
    }

    fn rename_file<'a>(
        &'a self,
        source_path: &'a str,
        destination_path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>> {
        Box::pin(self.rename_file_inner(source_path, destination_path, cx))
    }

    fn file_info<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<FileInfo, FileError>> {
        Box::pin(self.file_info_inner(path, cx))
    }

    fn list_dir<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Vec<FileInfo>, FileError>> {
        Box::pin(self.list_dir_inner(path, cx))
    }

    fn open_dir_reader<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Box<dyn DirReader>, FileError>> {
        Box::pin(self.open_dir_reader_inner(path, cx))
    }

    fn watch<'a>(
        &'a self,
        targets: &'a [WatchTarget],
        on_change: OnWatchChange,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Box<dyn FileWatcher>, FileError>> {
        Box::pin(self.watch_inner(targets, on_change, cx))
    }

    fn canonical_path<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<String, FileError>> {
        Box::pin(self.canonical_path_inner(path, cx))
    }

    fn exists<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<bool, FileError>> {
        Box::pin(self.exists_inner(path, cx))
    }

    fn create_dir<'a>(
        &'a self,
        path: &'a str,
        options: CreateDirOptions,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>> {
        Box::pin(self.create_dir_inner(path, options, cx))
    }

    fn remove<'a>(
        &'a self,
        path: &'a str,
        options: RemoveOptions,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>> {
        Box::pin(self.remove_inner(path, options, cx))
    }

    fn create_temp_dir<'a>(
        &'a self,
        prefix: Option<&'a str>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<String, FileError>> {
        Box::pin(self.create_temp_dir_inner(prefix, cx))
    }

    fn create_temp_file<'a>(
        &'a self,
        options: TempFileOptions,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<String, FileError>> {
        Box::pin(self.create_temp_file_inner(options, cx))
    }

    fn cleanup<'a>(&'a self, _cx: &'a Context) -> BoxFuture<'a, ()> {
        Box::pin(async move { self.kill_active_children() })
    }
}

impl Shell for NativeExecutionEnv {
    fn exec<'a>(
        &'a self,
        command: &'a ExecCommand,
        options: &'a ShellExecOptions,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<ShellExecResult, ExecutionError>> {
        Box::pin(exec::exec(self, command, options, cx))
    }

    fn cleanup<'a>(&'a self, _cx: &'a Context) -> BoxFuture<'a, ()> {
        Box::pin(async move { self.kill_active_children() })
    }
}
