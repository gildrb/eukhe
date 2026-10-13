//! The documents functions behind both entry points: [`perform`] runs one
//! decoded call on the session's documents, [`Done::diagnose`] hands the
//! files it wrote to the session's language servers, and the `fs.*` kernel
//! host requests (`fs.read`, `fs.write`, `fs.edit`, `fs.grep`, `fs.glob`)
//! repair the kernel's arguments by the function's contract, perform it,
//! and reply `done` with the typed result and the repair warnings, or
//! `rejected` with a reason and the model-facing message. Every reply
//! carries the function revision (`read@1`, `edit@hl.1`).

use std::path::{Path, PathBuf};
use std::sync::Arc;

use anyhow::Context as _;
use eukhe_docs::{
    Documents, EditError, FileChange, GlobError, GlobOutput, GrepError, GrepOutput,
    HashlineOutcome, Notice, ReadContent, ReadError, ReadView, WriteDisposition, WriteError,
    WriteOutcome,
};
use eukhe_durable::types::ConversationId;
use eukhe_types::pi_ai::JsonObject;
use futures::FutureExt;
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};
use serde_json::Value;

use super::contract::{EditArgs, Function, GlobArgs, GrepArgs, ReadArgs, WriteArgs};
use super::DocumentsHost;
use crate::durable::lsp::{SessionLsp, WriteDiagnostics};
use crate::durable::{HostCall, HostRequestRegistry};

/// Every request carries the kernel's working directory, so relative paths
/// resolve the way the model's `os.chdir` expects, and the arguments as the
/// kernel received them.
#[derive(Deserialize)]
struct KernelCall {
    cwd: PathBuf,
    args: JsonObject,
}

/// Why a call changed nothing; the message names the fix.
#[derive(Debug, Serialize)]
pub(super) struct Rejection {
    pub(super) version: &'static str,
    pub(super) reason: &'static str,
    pub(super) message: String,
}

impl Rejection {
    fn new(function: Function, reason: &'static str, error: &impl ToString) -> Self {
        Self {
            version: function.version(),
            reason,
            message: error.to_string(),
        }
    }
}

#[derive(Serialize)]
#[serde(tag = "outcome", rename_all = "snake_case")]
enum Reply {
    Done {
        #[serde(flatten)]
        done: Box<Done>,
        warnings: Vec<String>,
    },
    Rejected(Rejection),
}

/// A performed call's typed result.
#[derive(Serialize)]
#[serde(untagged)]
pub(super) enum Done {
    Read(ReadReply),
    Write(WriteReply),
    Edit(EditReply),
    Grep(GrepReply),
    Glob(GlobReply),
}

impl Done {
    /// The model-facing text.
    pub(super) fn rendered(&self) -> &str {
        match self {
            Self::Read(reply) => &reply.rendered,
            Self::Write(reply) => &reply.rendered,
            Self::Edit(reply) => &reply.rendered,
            Self::Grep(reply) => &reply.rendered,
            Self::Glob(reply) => &reply.rendered,
        }
    }

    /// Hand every file this call wrote to the language servers (their
    /// inline window runs for all files at once) and add what they said to
    /// the result and its text. Late diagnostics go to `conversation` (the
    /// root conversation when `None`).
    pub(super) async fn diagnose(
        &mut self,
        lsp: &Arc<SessionLsp>,
        conversation: Option<ConversationId>,
    ) {
        match self {
            Self::Write(reply) => {
                let diagnostics = lsp.committed_write(&reply.absolute, conversation).await;
                append(&mut reply.rendered, diagnostics.render(&reply.path));
                reply.diagnostics = Some(diagnostics);
            }
            Self::Edit(reply) => {
                let synced = futures::future::join_all(reply.files.iter().map(|file| async {
                    match &file.committed {
                        Some(path) => Some(lsp.committed_write(path, conversation).await),
                        None => None,
                    }
                }))
                .await;
                for (file, diagnostics) in reply.files.iter_mut().zip(synced) {
                    if let Some(diagnostics) = &diagnostics {
                        append(&mut reply.rendered, diagnostics.render(&file.path));
                    }
                    file.diagnostics = diagnostics;
                }
            }
            Self::Read(_) | Self::Grep(_) | Self::Glob(_) => {}
        }
    }
}

fn append(rendered: &mut String, text: Option<String>) {
    if let Some(text) = text {
        rendered.push('\n');
        rendered.push_str(&text);
    }
}

#[derive(Serialize)]
pub(super) struct ReadReply {
    version: &'static str,
    path: String,
    absolute: PathBuf,
    rendered: String,
    diags: Vec<String>,
    #[serde(flatten)]
    content: ReadReplyContent,
}

#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
enum ReadReplyContent {
    File {
        tag: Option<String>,
        text: String,
        total_lines: usize,
        /// Inclusive `[start, end]` spans of shown lines.
        shown: Vec<[usize; 2]>,
    },
    Directory {
        entries: Vec<DirEntryReply>,
    },
}

#[derive(Serialize)]
struct DirEntryReply {
    /// Slash-separated, relative to the listed directory (depth 2).
    path: String,
    is_dir: bool,
    size: Option<u64>,
    modified_ms: Option<u64>,
}

#[derive(Serialize)]
pub(super) struct WriteReply {
    version: &'static str,
    path: String,
    absolute: PathBuf,
    created: bool,
    bytes: usize,
    tag: Option<String>,
    made_executable: bool,
    rendered: String,
    /// What the language servers said; set by [`Done::diagnose`].
    #[serde(flatten)]
    diagnostics: Option<WriteDiagnostics>,
}

#[derive(Serialize)]
pub(super) struct EditReply {
    version: &'static str,
    rendered: String,
    files: Vec<EditFileReply>,
}

#[derive(Serialize)]
struct EditFileReply {
    path: String,
    absolute: PathBuf,
    change: &'static str,
    destination: Option<PathBuf>,
    diff: String,
    first_changed_line: Option<u32>,
    warnings: Vec<String>,
    tag: Option<String>,
    /// The file the edit left on disk (the destination of a move); `None`
    /// when it deleted the file or changed nothing.
    #[serde(skip)]
    committed: Option<PathBuf>,
    /// What the language servers said about `committed`; set by
    /// [`Done::diagnose`].
    #[serde(flatten)]
    diagnostics: Option<WriteDiagnostics>,
}

#[derive(Serialize)]
pub(super) struct GrepReply {
    version: &'static str,
    rendered: String,
    files: Vec<GrepFileReply>,
    total_files: u64,
    more_files: bool,
}

#[derive(Serialize)]
struct GrepFileReply {
    path: String,
    absolute: PathBuf,
    tag: Option<String>,
    /// `[line, text]` of each matching line.
    matches: Vec<(u32, String)>,
}

#[derive(Serialize)]
pub(super) struct GlobReply {
    version: &'static str,
    rendered: String,
    paths: Vec<String>,
    truncated: bool,
}

fn notice_lines(notices: &[Notice]) -> Vec<String> {
    notices.iter().map(ToString::to_string).collect()
}

fn read_reply(view: ReadView) -> ReadReply {
    let content = match view.content {
        ReadContent::File(file) => ReadReplyContent::File {
            tag: file.tag,
            text: file.text,
            total_lines: file.total_lines,
            shown: file
                .shown
                .iter()
                .map(|span| [span.start_line, span.end_line])
                .collect(),
        },
        ReadContent::Directory(entries) => ReadReplyContent::Directory {
            entries: entries
                .into_iter()
                .map(|entry| DirEntryReply {
                    path: entry.relative_path,
                    is_dir: entry.is_dir,
                    size: entry.size,
                    modified_ms: entry.modified_ms,
                })
                .collect(),
        },
    };
    ReadReply {
        version: Function::Read.version(),
        diags: notice_lines(&view.diags),
        path: view.path,
        absolute: view.absolute,
        rendered: view.rendered,
        content,
    }
}

fn read_rejection(error: &ReadError) -> &'static str {
    match error {
        ReadError::NotFound(_) => "not_found",
        ReadError::Selector(_) => "selector",
        ReadError::Binary { .. } => "binary",
        ReadError::Io { .. } => "io",
    }
}

fn write_reply(outcome: WriteOutcome) -> WriteReply {
    WriteReply {
        version: Function::Write.version(),
        path: outcome.path,
        absolute: outcome.absolute,
        created: match outcome.disposition {
            WriteDisposition::Created => true,
            WriteDisposition::Overwrote => false,
        },
        bytes: outcome.bytes,
        tag: outcome.tag,
        made_executable: outcome.made_executable,
        rendered: outcome.rendered,
        diagnostics: None,
    }
}

fn write_rejection(error: &WriteError) -> &'static str {
    match error {
        WriteError::IsDirectory { .. } => "is_directory",
        WriteError::Changed { .. } => "changed",
        WriteError::Io { .. } => "io",
    }
}

fn edit_reply(outcome: HashlineOutcome) -> EditReply {
    EditReply {
        version: Function::Edit.version(),
        rendered: outcome.text,
        files: outcome
            .files
            .into_iter()
            .map(|file| {
                let (change, destination, committed) = match file.change {
                    FileChange::Updated => ("updated", None, Some(file.absolute.clone())),
                    FileChange::Moved { destination } => {
                        ("moved", Some(destination.clone()), Some(destination))
                    }
                    FileChange::Deleted => ("deleted", None, None),
                    FileChange::Unchanged => ("unchanged", None, None),
                };
                EditFileReply {
                    path: file.display,
                    absolute: file.absolute,
                    change,
                    destination,
                    diff: file.diff,
                    first_changed_line: file.first_changed_line,
                    warnings: file.warnings,
                    tag: file.tag,
                    committed,
                    diagnostics: None,
                }
            })
            .collect(),
    }
}

/// The rejection reason of an edit: what the model must fix.
fn edit_rejection(error: &EditError) -> &'static str {
    match error {
        EditError::Parse { .. } => "parse",
        EditError::Apply(_) => "apply",
        EditError::Match(_) => "anchor",
        EditError::Io { .. } => "io",
    }
}

fn grep_reply(output: GrepOutput) -> GrepReply {
    GrepReply {
        version: Function::Grep.version(),
        rendered: output.render(),
        total_files: output.total_files,
        more_files: output.file_limit_reached,
        files: output
            .files
            .into_iter()
            .map(|file| GrepFileReply {
                path: file.path,
                absolute: file.absolute,
                tag: file.tag,
                matches: file
                    .matches
                    .into_iter()
                    .map(|hit| (hit.line_number, hit.line))
                    .collect(),
            })
            .collect(),
    }
}

fn grep_rejection(error: &GrepError) -> &'static str {
    match error {
        GrepError::EmptyPattern | GrepError::InvalidRegex { .. } => "pattern",
        GrepError::InvalidSelector { .. } => "selector",
        GrepError::TimedOut => "timeout",
        GrepError::AllPathsMissing { .. } => "not_found",
        GrepError::Workspace { .. } => "io",
    }
}

fn glob_reply(output: GlobOutput) -> GlobReply {
    GlobReply {
        version: Function::Glob.version(),
        rendered: output.render(),
        truncated: output.truncated,
        paths: output.matches.into_iter().map(|hit| hit.path).collect(),
    }
}

fn glob_rejection(error: &GlobError) -> &'static str {
    match error {
        GlobError::EmptyPath | GlobError::RootSearch | GlobError::UnsupportedScheme { .. } => {
            "path"
        }
        GlobError::PathNotFound { .. } => "not_found",
        GlobError::PathNotDirectory { .. } => "not_directory",
        GlobError::InvalidPattern { .. } => "pattern",
        GlobError::Workspace { .. } => "io",
    }
}

/// The function's typed arguments; a value the contract does not accept
/// is an `arguments` rejection.
fn decode<T: DeserializeOwned>(function: Function, args: JsonObject) -> Result<T, Rejection> {
    serde_json::from_value(Value::Object(args)).map_err(|error| {
        Rejection::new(
            function,
            "arguments",
            &format!("{}: {error}", function.name()),
        )
    })
}

/// Run one call whose arguments are already in the function's dialect,
/// resolving relative paths against `cwd`. Blocking: file I/O.
pub(super) fn perform(
    documents: &Documents,
    function: Function,
    cwd: &Path,
    args: JsonObject,
) -> Result<Done, Rejection> {
    match function {
        Function::Read => {
            let args: ReadArgs = decode(function, args)?;
            documents
                .read(cwd, &args.path)
                .map(|view| Done::Read(read_reply(view)))
                .map_err(|error| Rejection::new(function, read_rejection(&error), &error))
        }
        Function::Write => {
            let args: WriteArgs = decode(function, args)?;
            documents
                .write(cwd, &args.path, &args.content)
                .map(|outcome| Done::Write(write_reply(outcome)))
                .map_err(|error| Rejection::new(function, write_rejection(&error), &error))
        }
        Function::Edit => {
            let args: EditArgs = decode(function, args)?;
            documents
                .edit(cwd, &args.input)
                .map(|outcome| Done::Edit(edit_reply(outcome)))
                .map_err(|error| Rejection::new(function, edit_rejection(&error), &error))
        }
        Function::Grep => {
            let args: GrepArgs = decode(function, args)?;
            documents
                .grep(cwd, &args.into_request())
                .map(|output| Done::Grep(grep_reply(output)))
                .map_err(|error| Rejection::new(function, grep_rejection(&error), &error))
        }
        Function::Glob => {
            let args: GlobArgs = decode(function, args)?;
            documents
                .glob(cwd, &args.into_request())
                .map(|output| Done::Glob(glob_reply(output)))
                .map_err(|error| Rejection::new(function, glob_rejection(&error), &error))
        }
    }
}

/// Repair the kernel's arguments by the function's contract, then perform
/// the call.
fn kernel_reply(documents: &Documents, function: Function, cwd: &Path, args: JsonObject) -> Reply {
    let repaired = match function.repair(args) {
        Ok(repaired) => repaired,
        Err(error) => return Reply::Rejected(Rejection::new(function, "arguments", &error)),
    };
    match perform(documents, function, cwd, repaired.arguments) {
        Ok(done) => Reply::Done {
            done: Box::new(done),
            warnings: repaired.repairs.iter().map(ToString::to_string).collect(),
        },
        Err(rejection) => Reply::Rejected(rejection),
    }
}

/// Serve one `fs.*` request on a blocking thread; relative paths resolve
/// against the cwd the kernel sent with it (its `os.getcwd()`).
async fn handle(
    host: Arc<DocumentsHost>,
    function: Function,
    call: HostCall,
) -> anyhow::Result<Value> {
    let request_type = function.request_type();
    let request: KernelCall = serde_json::from_value(call.data.clone())
        .with_context(|| format!("{request_type} request is malformed"))?;
    anyhow::ensure!(
        request.cwd.is_absolute(),
        "{request_type} cwd must be absolute, got {}",
        request.cwd.display()
    );
    let blocking_host = Arc::clone(&host);
    let mut reply = tokio::task::spawn_blocking(move || {
        kernel_reply(
            &blocking_host.documents,
            function,
            &request.cwd,
            request.args,
        )
    })
    .await?;
    if let Reply::Done { done, .. } = &mut reply {
        done.diagnose(&host.lsp, call.conversation_id()).await;
    }
    Ok(serde_json::to_value(reply)?)
}

/// Register the `fs.*` requests over `host`.
pub(super) fn register(registry: &HostRequestRegistry, host: &Arc<DocumentsHost>) {
    for function in [
        Function::Read,
        Function::Write,
        Function::Edit,
        Function::Grep,
        Function::Glob,
    ] {
        let host = Arc::clone(host);
        registry.register(
            function.request_type(),
            Arc::new(move |call: HostCall| handle(Arc::clone(&host), function, call).boxed()),
        );
    }
}

#[cfg(test)]
mod tests;
