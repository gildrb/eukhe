//! The documents functions behind both entry points: [`perform`] runs one
//! decoded call on the session's documents (a `read` of an internal URL
//! through [`super::urls`]), and the `fs.*` kernel host requests
//! (`fs.read`, `fs.write`, `fs.edit`, `fs.grep`, `fs.glob`) repair the
//! kernel's arguments by the function's contract, perform it, and reply
//! `done` with the typed result and the repair warnings, or `rejected` with
//! a reason and the model-facing message. Every reply carries the function
//! revision (`read@1`, `edit@hl.1`).

use std::path::{Path, PathBuf};
use std::sync::Arc;

use anyhow::Context as _;
use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_docs::{
    AccessGate, Documents, EditError, FileChange, GlobError, GlobOutput, GrepError, GrepOutput,
    HashlineOutcome, Notice, ReadContent, ReadError, ReadView, Row, Url, UrlError,
    WriteDisposition, WriteError, WriteOutcome,
};
use eukhe_durable::harness::types::{OmittedAt, OmittedOutput, ToolExecutionApi};
use eukhe_types::pi_ai::{ImageContent, JsonObject};
use futures::FutureExt;
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use tokio::task::JoinError;

use super::contract::{EditArgs, Function, GlobArgs, GrepArgs, ReadArgs, WriteArgs};
use super::{urls, DocumentsHost};
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
    pub(super) fn new(function: Function, reason: &'static str, error: &impl ToString) -> Self {
        Self {
            version: function.version(),
            reason,
            message: error.to_string(),
        }
    }
}

/// A performed call: its typed result and, for a `memory://` message read
/// whole, the message's images (the wire tool shows them; the kernel's
/// reply carries the text only).
pub(super) struct Performed {
    pub(super) done: Done,
    pub(super) images: Vec<ImageContent>,
}

#[derive(Serialize)]
#[serde(tag = "outcome", rename_all = "snake_case")]
enum Reply {
    Done {
        #[serde(flatten)]
        done: Done,
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

    /// Mark seen the rows of a read or grep result that reached the model:
    /// those whose line of [`Done::rendered`] is not in `cut` (the lines an
    /// output bound left out). Only seen lines are edit anchors.
    pub(super) fn mark_seen(&self, documents: &Documents, cut: &Cut) {
        let kept = |rows: &[Row]| -> Vec<u32> {
            rows.iter()
                .filter(|row| cut.keeps(row.at))
                .map(|row| row.line)
                .collect()
        };
        match self {
            Self::Read(reply) => {
                if let (Some(absolute), ReadReplyContent::File { tag: Some(tag), .. }) =
                    (&reply.absolute, &reply.content)
                {
                    documents.mark_seen(absolute, tag, &kept(&reply.rows));
                }
            }
            Self::Grep(reply) => {
                for file in &reply.files {
                    if let Some(tag) = &file.tag {
                        documents.mark_seen(&file.absolute, tag, &kept(&file.rows));
                    }
                }
            }
            Self::Write(_) | Self::Edit(_) | Self::Glob(_) => {}
        }
    }
}

/// The lines of a rendered result that an output bound left out.
pub(super) enum Cut {
    /// The whole result reached the model.
    Whole,
    /// The 0-based lines `first..=last` of the rendered result were cut,
    /// each whole or in part.
    Lines { first: usize, last: usize },
}

impl Cut {
    /// The lines of `rendered` that are not whole in `kept`, which is
    /// `rendered` less `omitted.bytes` contiguous bytes (an output bound
    /// keeps a head and a tail). The bound cuts after line
    /// `omitted.at`; when the bytes do not agree with that, the cut covers
    /// every place it could lie.
    pub(super) fn of(rendered: &str, kept: &str, omitted: &OmittedOutput) -> Self {
        let count = usize::try_from(omitted.bytes).unwrap_or(usize::MAX);
        if count == 0 || kept.len() >= rendered.len() {
            return Self::Whole;
        }
        let (rendered, kept) = (rendered.as_bytes(), kept.as_bytes());
        let line_of = |byte: usize| rendered[..byte].split(|&b| b == b'\n').count() - 1;
        let lines = |start: usize| Self::Lines {
            first: line_of(start),
            last: line_of(start.saturating_add(count).min(rendered.len()) - 1),
        };
        if let OmittedAt::AfterLine(after) = omitted.at {
            let after = usize::try_from(after).unwrap_or(usize::MAX);
            let start = if after == 0 {
                Some(0)
            } else {
                rendered
                    .iter()
                    .enumerate()
                    .filter(|(_, &byte)| byte == b'\n')
                    .nth(after - 1)
                    .map(|(index, _)| index + 1)
            };
            if let Some(start) = start.filter(|&start| {
                start.saturating_add(count) <= rendered.len()
                    && start <= kept.len()
                    && rendered[..start] == kept[..start]
                    && rendered[start + count..] == kept[start..]
            }) {
                return lines(start);
            }
        }
        let prefix = rendered
            .iter()
            .zip(kept)
            .take_while(|(a, b)| a == b)
            .count();
        let suffix = rendered
            .iter()
            .rev()
            .zip(kept.iter().rev())
            .take_while(|(a, b)| a == b)
            .count();
        // The cut starts at some byte in `earliest..=latest`.
        let latest = prefix.min(kept.len());
        let earliest = kept.len().saturating_sub(suffix).min(latest);
        Self::Lines {
            first: line_of(earliest),
            last: line_of(latest.saturating_add(count).min(rendered.len()) - 1),
        }
    }

    fn keeps(&self, at: usize) -> bool {
        match self {
            Self::Whole => true,
            Self::Lines { first, last } => at < *first || at > *last,
        }
    }
}

#[derive(Serialize)]
pub(super) struct ReadReply {
    version: &'static str,
    path: String,
    /// The file read; `None` for an internal URL read as text.
    absolute: Option<PathBuf>,
    rendered: String,
    diags: Vec<String>,
    #[serde(flatten)]
    content: ReadReplyContent,
    /// The shown rows and their lines in `rendered`.
    #[serde(skip)]
    rows: Vec<Row>,
}

impl ReadReply {
    /// An internal URL (`agent://`, `memory://`) read as `text`.
    pub(super) fn text(url: String, text: String) -> Self {
        Self {
            version: Function::Read.version(),
            path: url,
            absolute: None,
            rendered: text.clone(),
            diags: Vec::new(),
            content: ReadReplyContent::Text { text },
            rows: Vec::new(),
        }
    }
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
    /// What the session holds behind an internal URL, as text.
    Text {
        text: String,
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
    rendered: String,
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
    /// Why the file was not written (`change` is `not_written`).
    reason: Option<String>,
    diff: String,
    first_changed_line: Option<u32>,
    warnings: Vec<String>,
    tag: Option<String>,
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
    /// The shown rows and their lines in `rendered`.
    #[serde(skip)]
    rows: Vec<Row>,
}

#[derive(Serialize)]
pub(super) struct GlobReply {
    version: &'static str,
    rendered: String,
    paths: Vec<String>,
    truncated: bool,
    /// Ranked paths skipped before `paths`.
    skip: u64,
    /// The `skip` that returns the next paths, when more follow.
    next_skip: Option<u64>,
}

fn notice_lines(notices: &[Notice]) -> Vec<String> {
    notices.iter().map(ToString::to_string).collect()
}

pub(super) fn read_reply(view: ReadView) -> ReadReply {
    let (content, rows) = match view.content {
        ReadContent::File(file) => (
            ReadReplyContent::File {
                tag: file.tag,
                text: file.text,
                total_lines: file.total_lines,
                shown: file
                    .shown
                    .iter()
                    .map(|span| [span.start_line, span.end_line])
                    .collect(),
            },
            file.rows,
        ),
        ReadContent::Directory(entries) => (
            ReadReplyContent::Directory {
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
            Vec::new(),
        ),
    };
    ReadReply {
        version: Function::Read.version(),
        diags: notice_lines(&view.diags),
        path: view.path,
        absolute: Some(view.absolute),
        rendered: view.rendered,
        content,
        rows,
    }
}

pub(super) fn read_rejection(error: &ReadError) -> &'static str {
    match error {
        ReadError::NotFound(_) => "not_found",
        ReadError::Selector(_) => "selector",
        ReadError::Binary { .. } => "binary",
        ReadError::NotUtf8 { .. } => "encoding",
        ReadError::Io { .. } => "io",
        ReadError::Url(error) => url_rejection(error),
        ReadError::Refused { .. } => "refused",
    }
}

/// The rejection reason of an internal URL no root serves.
pub(super) fn url_rejection(error: &UrlError) -> &'static str {
    match error {
        UrlError::UnknownScheme { .. } => "scheme",
        UrlError::Escapes { .. } | UrlError::Leaves { .. } => "escapes",
        UrlError::Host { .. } => "arguments",
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
        rendered: outcome.rendered,
    }
}

fn write_rejection(error: &WriteError) -> &'static str {
    match error {
        WriteError::IsDirectory { .. } => "is_directory",
        WriteError::Changed { .. } => "changed",
        WriteError::Unseen { .. } => "unseen",
        WriteError::Io { .. } => "io",
        WriteError::Refused { .. } => "refused",
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
                let (change, destination, reason) = match file.change {
                    FileChange::Updated => ("updated", None, None),
                    FileChange::Moved { destination } => ("moved", Some(destination), None),
                    FileChange::Deleted => ("deleted", None, None),
                    FileChange::Unchanged => ("unchanged", None, None),
                    FileChange::NotWritten { reason } => ("not_written", None, Some(reason)),
                };
                EditFileReply {
                    path: file.display,
                    absolute: file.absolute,
                    change,
                    destination,
                    reason,
                    diff: file.diff,
                    first_changed_line: file.first_changed_line,
                    warnings: file.warnings,
                    tag: file.tag,
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
        EditError::Refused(_) => "refused",
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
                rows: file.rows,
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
        GrepError::Refused { .. } => "refused",
    }
}

fn glob_reply(output: GlobOutput) -> GlobReply {
    GlobReply {
        version: Function::Glob.version(),
        rendered: output.render(),
        truncated: output.truncated,
        skip: output.skip,
        next_skip: output.next_skip,
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
        GlobError::Refused { .. } => "refused",
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

/// Run one call on `documents`, resolving relative paths against `cwd`,
/// each path access through `gate`. Blocking: file I/O, and the gate may
/// wait for the user.
fn perform_blocking(
    documents: &Documents,
    function: Function,
    cwd: &Path,
    args: JsonObject,
    gate: &dyn AccessGate,
) -> Result<Done, Rejection> {
    match function {
        Function::Read => {
            let args: ReadArgs = decode(function, args)?;
            documents
                .read(cwd, &args.path, gate)
                .map(|view| Done::Read(read_reply(view)))
                .map_err(|error| Rejection::new(function, read_rejection(&error), &error))
        }
        Function::Write => {
            let args: WriteArgs = decode(function, args)?;
            documents
                .write(cwd, &args.path, &args.content, gate)
                .map(|outcome| Done::Write(write_reply(outcome)))
                .map_err(|error| Rejection::new(function, write_rejection(&error), &error))
        }
        Function::Edit => {
            let args: EditArgs = decode(function, args)?;
            documents
                .edit(cwd, &args.input, gate)
                .map(|outcome| Done::Edit(edit_reply(outcome)))
                .map_err(|error| Rejection::new(function, edit_rejection(&error), &error))
        }
        Function::Grep => {
            let args: GrepArgs = decode(function, args)?;
            documents
                .grep(cwd, &args.into_request(), gate)
                .map(|output| Done::Grep(grep_reply(output)))
                .map_err(|error| Rejection::new(function, grep_rejection(&error), &error))
        }
        Function::Glob => {
            let args: GlobArgs = decode(function, args)?;
            documents
                .glob(cwd, &args.into_request(), gate)
                .map(|output| Done::Glob(glob_reply(output)))
                .map_err(|error| Rejection::new(function, glob_rejection(&error), &error))
        }
    }
}

/// Run one call whose arguments are already in the function's dialect,
/// resolving relative paths against `cwd`: a `read` of an internal URL
/// through [`urls::read`] (`api` is the tool call it runs in), the rest on
/// a blocking thread. Every path access passes the gate of the session's
/// path policy over `workspace` (the call's agent cwd: never a cwd the
/// model can change). The outer error is a failed worker.
#[tracing::instrument(name = "documents.perform", skip_all, fields(function = function.name()))]
pub(super) async fn perform(
    host: &Arc<DocumentsHost>,
    function: Function,
    cwd: PathBuf,
    workspace: &Path,
    args: JsonObject,
    api: Option<Arc<dyn ToolExecutionApi>>,
    cx: &Context,
) -> Result<Result<Performed, Rejection>, JoinError> {
    let gate = host.gate(workspace, api.as_deref());
    let url = match function {
        Function::Read => args
            .get("path")
            .and_then(Value::as_str)
            .and_then(Url::parse),
        Function::Write | Function::Edit | Function::Grep | Function::Glob => None,
    };
    match url {
        Some(Ok(url)) => urls::read(host, api, cwd, url, gate, cx).await,
        Some(Err(error)) => Ok(Err(urls::url_error(&error))),
        None => {
            let host = Arc::clone(host);
            tokio::task::spawn_blocking(move || {
                perform_blocking(&host.documents, function, &cwd, args, &gate).map(|done| {
                    Performed {
                        done,
                        images: Vec::new(),
                    }
                })
            })
            .await
        }
    }
}

/// Serve one `fs.*` request: repair the kernel's arguments by the
/// function's contract, then perform the call; relative paths resolve
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
    let reply = match function.repair(request.args) {
        Err(error) => Reply::Rejected(Rejection::new(function, "arguments", &error)),
        Ok(repaired) => match perform(
            &host,
            function,
            request.cwd,
            &host.workspace,
            repaired.arguments,
            call.call,
            &BACKGROUND_CONTEXT,
        )
        .await?
        {
            Ok(performed) => {
                // The kernel gets the whole result.
                performed.done.mark_seen(&host.documents, &Cut::Whole);
                Reply::Done {
                    done: performed.done,
                    warnings: repaired.repairs.iter().map(ToString::to_string).collect(),
                }
            }
            Err(rejection) => Reply::Rejected(rejection),
        },
    };
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
