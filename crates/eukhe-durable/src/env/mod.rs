//! Execution environments: the file system and shell an agent's tools act
//! on. Port of `env/index.ts`.
//!
//! Fallible operations return [`Result`]: expected failures are values, never
//! panics. The TS helpers `ok`, `err`, `getOrThrow`, `getOrUndefined`, and
//! `toError` are the std [`Result`] API (`Ok`, `Err`, `?`, `.ok()`).

mod decode;
mod line_scan;
mod native;
mod native_watch;
mod node_error;

use std::collections::BTreeMap;
use std::error::Error;
use std::fmt;
use std::sync::Arc;

use eukhe_chord::context::Context;
use futures::future::BoxFuture;

pub use decode::{range_decoder, starts_with_bom, StreamDecoder, Utf8Decoder};
pub use line_scan::{InvalidLineRange, LineScanner};
pub use native::{NativeExecutionEnv, NativeExecutionEnvOptions};
pub use native_watch::NativeWatchOptions;

/// The cause attached to a [`FileError`] or [`ExecutionError`]: the JS
/// `Error.cause`.
pub type ErrorCause = Arc<dyn Error + Send + Sync + 'static>;

/// What a path names.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FileKind {
    File,
    Directory,
    Symlink,
}

impl FileKind {
    /// The TS string: `"file"`, `"directory"`, or `"symlink"`.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::File => "file",
            Self::Directory => "directory",
            Self::Symlink => "symlink",
        }
    }
}

/// Why a file operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FileErrorCode {
    Aborted,
    NotFound,
    PermissionDenied,
    NotDirectory,
    IsDirectory,
    Invalid,
    NotSupported,
    Unknown,
}

impl FileErrorCode {
    /// The TS string, e.g. `"not_found"`.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Aborted => "aborted",
            Self::NotFound => "not_found",
            Self::PermissionDenied => "permission_denied",
            Self::NotDirectory => "not_directory",
            Self::IsDirectory => "is_directory",
            Self::Invalid => "invalid",
            Self::NotSupported => "not_supported",
            Self::Unknown => "unknown",
        }
    }
}

impl fmt::Display for FileErrorCode {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.as_str())
    }
}

/// A failed file operation: the TS `FileError` (`name` `"FileError"`).
#[derive(Clone, Debug, thiserror::Error)]
#[error("{message}")]
pub struct FileError {
    pub code: FileErrorCode,
    pub message: String,
    pub path: Option<String>,
    #[source]
    pub cause: Option<ErrorCause>,
}

impl FileError {
    /// The JS `error.name`.
    pub const NAME: &'static str = "FileError";

    /// A failure without a cause.
    #[must_use]
    pub fn new(code: FileErrorCode, message: impl Into<String>, path: Option<String>) -> Self {
        Self {
            code,
            message: message.into(),
            path,
            cause: None,
        }
    }

    /// The same failure caused by `cause`.
    #[must_use]
    pub fn with_cause(mut self, cause: ErrorCause) -> Self {
        self.cause = Some(cause);
        self
    }
}

/// Why running a command failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ExecutionErrorCode {
    Aborted,
    Timeout,
    ShellUnavailable,
    SpawnError,
    CallbackError,
    Unknown,
}

impl ExecutionErrorCode {
    /// The TS string, e.g. `"spawn_error"`.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Aborted => "aborted",
            Self::Timeout => "timeout",
            Self::ShellUnavailable => "shell_unavailable",
            Self::SpawnError => "spawn_error",
            Self::CallbackError => "callback_error",
            Self::Unknown => "unknown",
        }
    }
}

impl fmt::Display for ExecutionErrorCode {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.as_str())
    }
}

/// A command that could not run to completion: the TS `ExecutionError`
/// (`name` `"ExecutionError"`).
#[derive(Clone, Debug, thiserror::Error)]
#[error("{message}")]
pub struct ExecutionError {
    pub code: ExecutionErrorCode,
    pub message: String,
    /// Spill file of a command that timed out or was aborted after its output
    /// crossed the spill thresholds.
    pub spill_path: Option<String>,
    #[source]
    pub cause: Option<ErrorCause>,
}

impl ExecutionError {
    /// The JS `error.name`.
    pub const NAME: &'static str = "ExecutionError";

    /// A failure without a cause.
    #[must_use]
    pub fn new(code: ExecutionErrorCode, message: impl Into<String>) -> Self {
        Self {
            code,
            message: message.into(),
            spill_path: None,
            cause: None,
        }
    }

    /// The same failure caused by `cause`.
    #[must_use]
    pub fn with_cause(mut self, cause: ErrorCause) -> Self {
        self.cause = Some(cause);
        self
    }
}

/// Metadata of one path, not following a final symbolic link unless the
/// operation says so.
#[derive(Clone, Debug, PartialEq)]
pub struct FileInfo {
    pub name: String,
    pub path: String,
    pub kind: FileKind,
    pub size: u64,
    pub mtime_ms: f64,
}

/// One line of a text file, without its newline.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TextLine {
    pub text: String,
    /// Whether a newline ended the line.
    pub terminated: bool,
}

/// Reads one text file line by line.
///
/// Implementations split on LF only (a CR stays in the text), decode as UTF-8
/// like decoding the whole file, and return `Ok(None)` at the end. An aborted
/// read consumes nothing, so the next read returns the same line. After
/// `close`, reads fail with `invalid`; `close` is idempotent.
pub trait TextLineReader: Send + Sync {
    fn read_line<'a>(
        &'a self,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<TextLine>, FileError>>;
    fn close<'a>(&'a self, cx: &'a Context) -> BoxFuture<'a, ()>;
}

/// The lines `BinaryReader::scan_lines` selects: `[start_line, end_line)`,
/// 0-based; `end_line` absent: to the end.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct LineRange {
    pub start_line: f64,
    pub end_line: Option<f64>,
}

/// Positional reads from one opened regular file; all calls see the same file
/// even if its path is renamed.
///
/// Numbers are JS numbers: an offset, length, or line that is not a
/// non-negative safe integer fails with `invalid`. After `close`, every call
/// fails with `invalid`; `close` is idempotent.
pub trait BinaryReader: Send + Sync {
    /// Metadata of the opened file, not of whatever its path names now.
    fn info<'a>(&'a self, cx: &'a Context) -> BoxFuture<'a, Result<FileInfo, FileError>>;
    /// Up to `length` bytes at `offset`; fewer only at end of file.
    fn read<'a>(
        &'a self,
        offset: f64,
        length: f64,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Vec<u8>, FileError>>;
    /// One pass over the file that locates lines `[start_line, end_line)`,
    /// 0-based, where line `k` starts after the `k`-th newline byte. Decoded
    /// sizes are those of the text decoding the whole file would produce for
    /// that range, so a byte-order mark at the start of the file is not
    /// counted.
    fn scan_lines<'a>(
        &'a self,
        range: LineRange,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<LineScan, FileError>>;
    fn close<'a>(&'a self, cx: &'a Context) -> BoxFuture<'a, ()>;
}

/// Entries below a watched directory that are neither watched nor reported.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct WatchExclude {
    /// Names starting with `.`.
    pub hidden: bool,
    /// These names.
    pub names: Vec<String>,
}

/// A file or directory to watch. It may be missing; creating it is a change.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct WatchTarget {
    pub path: String,
    /// Watch everything below a directory, not only its entries. Symbolic
    /// links below it are not followed.
    pub recursive: bool,
    pub exclude: WatchExclude,
}

/// What changed.
#[derive(Clone, Debug)]
pub enum WatchChange {
    /// Something at or below each path may have changed (a directory path
    /// covers its whole subtree). Calls may be spurious; a change is never
    /// missed while the watcher is healthy.
    Paths(Vec<String>),
    /// Coverage was uncertain for a while (lost events, reconnect); rescan
    /// everything that is watched.
    Overflow,
    /// The watcher stopped, for example because the watched tree grew past
    /// the environment's limit; no calls follow.
    Error(FileError),
}

/// Receives the changes a [`FileWatcher`] reports.
pub type OnWatchChange = Arc<dyn Fn(WatchChange) + Send + Sync>;

/// How a [`FileWatcher`] learns about changes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum WatchMode {
    /// Changes are reported within about two seconds.
    Native,
    /// The environment compares snapshots, because the file system does not
    /// report changes reliably (network and FUSE file systems); a change undone
    /// between two snapshots can be missed.
    Polling,
}

impl WatchMode {
    /// The TS string: `"native"` or `"polling"`.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Native => "native",
            Self::Polling => "polling",
        }
    }
}

/// A running watch started by [`FileSystem::watch`].
///
/// Implementations report through the callback given to `watch` until
/// `close` resolves; no callback starts after that. `close` is idempotent.
pub trait FileWatcher: Send + Sync {
    /// The current mode; a native watcher that runs out of watches switches to
    /// polling.
    fn mode(&self) -> WatchMode;
    /// Stop watching; no `on_change` call starts after this resolves.
    fn close<'a>(&'a self, cx: &'a Context) -> BoxFuture<'a, ()>;
}

/// Where lines of a file are, as `BinaryReader::scan_lines` found them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LineScan {
    /// Newline bytes in the whole file; it has `newlines + 1` lines.
    pub newlines: u64,
    /// Byte range of the selected lines: from the start of the first to the
    /// end of the last, without the newline that ends it. A selection past
    /// the last line is empty at the end of the file.
    pub start: u64,
    pub end: u64,
    /// Where the first selected line ends: its newline, or the end of the
    /// file.
    pub first_line_end: u64,
    /// Where the last selected line starts.
    pub last_line_start: u64,
    /// UTF-8 byte length of the decoded selection.
    pub selected_bytes: u64,
    /// UTF-8 byte length of the decoded first selected line.
    pub first_line_bytes: u64,
}

/// One page of a [`DirReader`].
#[derive(Clone, Debug, PartialEq)]
pub struct DirPage {
    pub entries: Vec<FileInfo>,
    pub done: bool,
}

/// Pages of one directory's entries.
///
/// `next` returns up to `max_entries` entries in the order the file system
/// returns them, continuing where the previous call stopped. `done` marks the
/// end; it may come with the last entries or with an empty page. An entry that
/// disappears before its metadata is read is skipped, as are entries of
/// unsupported kinds. After a failed or aborted call, close the reader.
/// `max_entries` must be a positive safe integer (else `invalid`); after
/// `close`, `next` fails with `invalid`; `close` is idempotent.
pub trait DirReader: Send + Sync {
    fn next<'a>(
        &'a self,
        max_entries: f64,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<DirPage, FileError>>;
    fn close<'a>(&'a self, cx: &'a Context) -> BoxFuture<'a, ()>;
}

/// Options of [`FileSystem::read_text_lines`].
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct ReadTextLinesOptions {
    /// Stop after this many lines; zero or less reads none.
    pub max_lines: Option<f64>,
}

/// Options of [`FileSystem::open_binary_reader`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct OpenBinaryReaderOptions {
    /// Fail with `invalid` instead of following a symbolic link as the final
    /// path component; earlier components are still resolved.
    pub no_follow: bool,
}

/// Options of [`FileSystem::create_dir`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CreateDirOptions {
    /// Create missing parents and accept an existing directory; default true.
    pub recursive: bool,
}

impl Default for CreateDirOptions {
    fn default() -> Self {
        Self { recursive: true }
    }
}

/// Options of [`FileSystem::remove`]; both default to false.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RemoveOptions {
    pub recursive: bool,
    /// Succeed when the path does not exist.
    pub force: bool,
}

/// Options of [`FileSystem::create_temp_file`].
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TempFileOptions {
    pub prefix: Option<String>,
    pub suffix: Option<String>,
}

/// Portable filesystem capability. Operations return failures rather than
/// panicking.
///
/// Implementations resolve relative paths against `cwd`, check the context's
/// abort signal before doing anything (failing with `aborted` and no side
/// effects), and report expected failures as [`FileError`] values with the
/// failing path.
pub trait FileSystem: Send + Sync {
    /// The file namespace: equal ids see the same files at the same paths,
    /// whatever their `cwd`. Every local native environment shares one id;
    /// each container or remote host has its own.
    fn id(&self) -> &str;
    fn cwd(&self) -> &str;
    fn absolute_path<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<String, FileError>>;
    fn join_path<'a>(
        &'a self,
        parts: &'a [&'a str],
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<String, FileError>>;
    fn read_text_file<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<String, FileError>>;
    fn open_text_line_reader<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Box<dyn TextLineReader>, FileError>>;
    fn read_text_lines<'a>(
        &'a self,
        path: &'a str,
        options: ReadTextLinesOptions,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Vec<String>, FileError>>;
    fn read_binary_file<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Vec<u8>, FileError>>;
    /// Open a regular file for bounded positional reads. A directory fails
    /// with `is_directory`, other non-regular files with `invalid`.
    fn open_binary_reader<'a>(
        &'a self,
        path: &'a str,
        options: OpenBinaryReaderOptions,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Box<dyn BinaryReader>, FileError>>;
    /// Write `content`, creating missing parent directories.
    fn write_file<'a>(
        &'a self,
        path: &'a str,
        content: &'a [u8],
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>>;
    /// Append `content`, creating the file and missing parent directories.
    fn append_file<'a>(
        &'a self,
        path: &'a str,
        content: &'a [u8],
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>>;
    /// Truncate or extend a file to exactly `size` bytes; `size` must be a
    /// non-negative safe integer.
    fn truncate_file<'a>(
        &'a self,
        path: &'a str,
        size: f64,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>>;
    /// Flush file contents and metadata needed to retrieve them from an open
    /// file handle.
    fn flush_file<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>>;
    fn rename_file<'a>(
        &'a self,
        source_path: &'a str,
        destination_path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>>;
    fn file_info<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<FileInfo, FileError>>;
    fn list_dir<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Vec<FileInfo>, FileError>>;
    fn open_dir_reader<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Box<dyn DirReader>, FileError>>;
    /// Report changes to files and directories, for hosts that load resources
    /// from the environment. When the returned watcher exists, coverage is
    /// established: a host that watches before it loads cannot miss a change
    /// made during the load. See [`WatchChange`] for what is reported and
    /// [`WatchMode`] for how reliably.
    fn watch<'a>(
        &'a self,
        targets: &'a [WatchTarget],
        on_change: OnWatchChange,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Box<dyn FileWatcher>, FileError>>;
    fn canonical_path<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<String, FileError>>;
    fn exists<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<bool, FileError>>;
    fn create_dir<'a>(
        &'a self,
        path: &'a str,
        options: CreateDirOptions,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>>;
    fn remove<'a>(
        &'a self,
        path: &'a str,
        options: RemoveOptions,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>>;
    /// A new directory in the temporary directory; `prefix` defaults to
    /// `"tmp-"`.
    fn create_temp_dir<'a>(
        &'a self,
        prefix: Option<&'a str>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<String, FileError>>;
    /// A new empty file in a new temporary directory.
    fn create_temp_file<'a>(
        &'a self,
        options: TempFileOptions,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<String, FileError>>;
    /// Release what the environment holds; best-effort.
    fn cleanup<'a>(&'a self, cx: &'a Context) -> BoxFuture<'a, ()>;
}

/// Spill the complete output to a temporary file once it exceeds either
/// threshold.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ShellSpillOptions {
    pub after_bytes: u64,
    /// Complete or partial lines.
    pub after_lines: u64,
}

/// A command that ran to completion.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShellExecResult {
    pub exit_code: i32,
    /// Temporary file holding the complete raw output, when the spill
    /// thresholds were exceeded.
    pub spill_path: Option<String>,
}

/// The stream a chunk of output came from.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum OutputStream {
    Stdout,
    Stderr,
}

impl OutputStream {
    /// The TS string: `"stdout"` or `"stderr"`.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Stdout => "stdout",
            Self::Stderr => "stderr",
        }
    }
}

/// The tail of the combined output a caller keeps, and how often it samples
/// it. An environment that transfers output over a slow link uses it to omit
/// what the caller would drop anyway and to send no faster than the caller
/// commits.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct ShellOutputWindow {
    /// UTF-8 bytes of decoded text kept at the end of the output.
    pub max_bytes: u64,
    /// Lines kept at the end of the output.
    pub max_lines: u64,
    /// Minimum pause between the caller's samples of the output.
    pub min_interval_ms: f64,
    /// Each sample also pauses the caller in proportion to its size at this
    /// rate.
    pub bytes_per_second: f64,
}

/// Output an environment omitted, measured on the decoded text `on_output`
/// would have received: every U+FFFD counts as three bytes, and no sanitizing
/// is applied.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ShellOutputSkip {
    /// UTF-8 byte length of the omitted text.
    pub bytes: u64,
    /// Newlines (U+000A) in the omitted text.
    pub newlines: u64,
    /// Whether the omitted text ends with a newline.
    pub ends_with_newline: bool,
}

/// What accompanies one chunk of output.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ShellOutputInfo {
    pub stream: OutputStream,
    /// Output omitted immediately before this chunk, only with `window`. The
    /// chunk then holds all output after the omission up to its end, and that
    /// is more than the window by at least one byte or one line: more than
    /// `window.max_bytes` bytes or more than `window.max_lines` newlines. So
    /// the omitted text can never be in the kept tail. The omission and such a
    /// chunk may span both streams in arrival order; `stream` then names the
    /// chunk's last stream. Callers that need the streams apart do not pass
    /// `window`.
    pub skipped: Option<ShellOutputSkip>,
}

/// The error an output callback fails with: the JS exception it throws.
pub type OutputCallbackError = Box<dyn Error + Send + Sync + 'static>;

/// Receives every decoded chunk of output; an `Err` stops the command with
/// `callback_error`.
pub type OnShellOutput =
    Arc<dyn Fn(&str, &Context, &ShellOutputInfo) -> Result<(), OutputCallbackError> + Send + Sync>;

/// What to run: the TS `string | readonly string[]`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExecCommand {
    /// Runs through the environment's shell.
    Shell(String),
    /// Runs `argv[0]` directly with the rest as its arguments, without a
    /// shell, so they reach the program unparsed.
    Argv(Vec<String>),
}

/// Options of [`Shell::exec`].
#[derive(Clone, Default)]
pub struct ShellExecOptions {
    pub cwd: Option<String>,
    pub env: Option<BTreeMap<String, String>>,
    /// Start from the environment's variables; default true.
    pub inherit_env: Option<bool>,
    /// Seconds; must be finite, positive, and at most 2147483.647.
    pub timeout: Option<f64>,
    /// Every decoded chunk of stdout and stderr as it arrives, in arrival
    /// order, with the stream it came from: raw, unbounded, and unthrottled.
    /// Each stream is decoded separately, so a character split across chunks
    /// survives.
    pub on_output: Option<OnShellOutput>,
    pub spill: Option<ShellSpillOptions>,
    /// The caller keeps only this tail of the output, so the environment may
    /// omit output outside it and report the omission as `info.skipped`.
    /// Without it, every chunk is delivered.
    pub window: Option<ShellOutputWindow>,
}

impl fmt::Debug for ShellExecOptions {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ShellExecOptions")
            .field("cwd", &self.cwd)
            .field("env", &self.env)
            .field("inherit_env", &self.inherit_env)
            .field("timeout", &self.timeout)
            .field("on_output", &self.on_output.as_ref().map(|_| "Fn"))
            .field("spill", &self.spill)
            .field("window", &self.window)
            .finish()
    }
}

/// Runs commands.
///
/// Aborting the context or a timeout kills only the command's processes; the
/// result then fails with `aborted` or `timeout`. A command that ran reports
/// its exit code, also when non-zero.
pub trait Shell: Send + Sync {
    /// Run a command. A [`ExecCommand::Shell`] string runs through the
    /// environment's shell; an [`ExecCommand::Argv`] array runs `argv[0]`
    /// directly.
    fn exec<'a>(
        &'a self,
        command: &'a ExecCommand,
        options: &'a ShellExecOptions,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<ShellExecResult, ExecutionError>>;
    /// Kill every command this environment still runs; for its owner's
    /// shutdown, never for one request.
    fn cleanup<'a>(&'a self, cx: &'a Context) -> BoxFuture<'a, ()>;
}

/// A file system and a shell over the same files. Implemented for every type
/// that is both.
pub trait ExecutionEnv: FileSystem + Shell {}

impl<T: FileSystem + Shell> ExecutionEnv for T {}
