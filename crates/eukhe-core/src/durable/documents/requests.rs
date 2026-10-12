//! The `fs.*` kernel host requests: `fs.read`, `fs.write`, `fs.edit`,
//! `fs.grep`, `fs.glob`. Every reply carries the function revision
//! (`read@1`, `edit@hl.1`) and is either `done` with the typed result or
//! `rejected` with a reason and the model-facing message.

use std::num::NonZeroUsize;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use anyhow::Context as _;
use eukhe_docs::{
    EditError, FileChange, GlobError, GlobOutput, GlobRequest, GrepError, GrepOutput, GrepRequest,
    HashlineOutcome, Notice, ReadContent, ReadError, ReadView, WriteDisposition, WriteError,
    WriteOutcome,
};
use futures::FutureExt;
use serde::{Deserialize, Serialize};
use serde_json::Value;

use super::DocumentsHost;
use crate::durable::{HostCall, HostRequestRegistry};

const READ_REV: &str = "read@1";
const WRITE_REV: &str = "write@1";
pub(super) const EDIT_REV: &str = "edit@hl.1";
const GREP_REV: &str = "grep@1";
const GLOB_REV: &str = "glob@1";

/// Every request carries the kernel's working directory: relative paths
/// resolve the way the model's `os.chdir` expects.
#[derive(Deserialize)]
struct ReadRequest {
    cwd: PathBuf,
    path: String,
}

#[derive(Deserialize)]
struct WriteRequest {
    cwd: PathBuf,
    path: String,
    content: String,
}

#[derive(Deserialize)]
struct EditRequest {
    cwd: PathBuf,
    input: String,
}

#[derive(Deserialize)]
struct GrepCall {
    cwd: PathBuf,
    pattern: String,
    path: String,
    glob: Option<String>,
    ignore_case: bool,
    context: u32,
    skip: u64,
    limit: Option<NonZeroUsize>,
}

#[derive(Deserialize)]
struct GlobCall {
    cwd: PathBuf,
    path: String,
    hidden: bool,
    limit: Option<NonZeroUsize>,
}

#[derive(Serialize)]
#[serde(tag = "outcome", rename_all = "snake_case")]
enum Reply<T> {
    Done(T),
    Rejected {
        version: &'static str,
        reason: &'static str,
        message: String,
    },
}

impl<T> Reply<T> {
    fn rejected(version: &'static str, reason: &'static str, error: &impl ToString) -> Self {
        Self::Rejected {
            version,
            reason,
            message: error.to_string(),
        }
    }
}

#[derive(Serialize)]
struct ReadReply {
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
    name: String,
    is_dir: bool,
    size: Option<u64>,
}

#[derive(Serialize)]
struct WriteReply {
    version: &'static str,
    path: String,
    absolute: PathBuf,
    created: bool,
    bytes: usize,
    tag: Option<String>,
    made_executable: bool,
    rendered: String,
}

#[derive(Serialize)]
pub(super) struct EditReply {
    version: &'static str,
    pub(super) rendered: String,
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
}

#[derive(Serialize)]
struct GrepReply {
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
struct GlobReply {
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
                    name: entry.name,
                    is_dir: entry.is_dir,
                    size: entry.size,
                })
                .collect(),
        },
    };
    ReadReply {
        version: READ_REV,
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
        version: WRITE_REV,
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
    }
}

fn write_rejection(error: &WriteError) -> &'static str {
    match error {
        WriteError::IsDirectory { .. } => "is_directory",
        WriteError::Io { .. } => "io",
    }
}

pub(super) fn edit_reply(outcome: HashlineOutcome) -> EditReply {
    EditReply {
        version: EDIT_REV,
        rendered: outcome.text,
        files: outcome
            .files
            .into_iter()
            .map(|file| {
                let (change, destination) = match file.change {
                    FileChange::Updated => ("updated", None),
                    FileChange::Moved { destination } => ("moved", Some(destination)),
                    FileChange::Deleted => ("deleted", None),
                    FileChange::Unchanged => ("unchanged", None),
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
                }
            })
            .collect(),
    }
}

/// The rejection reason of an edit: what the model must fix.
pub(super) fn edit_rejection(error: &EditError) -> &'static str {
    match error {
        EditError::Parse { .. } => "parse",
        EditError::Apply(_) => "apply",
        EditError::Match(_) => "anchor",
        EditError::Io { .. } => "io",
    }
}

fn grep_reply(output: GrepOutput) -> GrepReply {
    GrepReply {
        version: GREP_REV,
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
        GrepError::TimedOut => "timeout",
        GrepError::AllPathsMissing { .. } => "not_found",
        GrepError::Workspace { .. } => "io",
    }
}

fn glob_reply(output: GlobOutput) -> GlobReply {
    GlobReply {
        version: GLOB_REV,
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

fn parse<T: for<'de> Deserialize<'de>>(request_type: &str, call: &HostCall) -> anyhow::Result<T> {
    let request: T = serde_json::from_value(call.data.clone())
        .with_context(|| format!("{request_type} request is malformed"))?;
    Ok(request)
}

/// Check the kernel cwd and remember it as the conversation's: the wire
/// `edit` resolves paths where the model's last read resolved them.
fn kernel_cwd(
    host: &DocumentsHost,
    request_type: &str,
    call: &HostCall,
    cwd: &Path,
) -> anyhow::Result<()> {
    anyhow::ensure!(
        cwd.is_absolute(),
        "{request_type} cwd must be absolute, got {}",
        cwd.display()
    );
    host.remember_cwd(call, cwd.to_path_buf());
    Ok(())
}

async fn blocking<T: Send + 'static>(
    work: impl FnOnce() -> T + Send + 'static,
) -> anyhow::Result<T> {
    Ok(tokio::task::spawn_blocking(work).await?)
}

async fn read(host: Arc<DocumentsHost>, call: HostCall) -> anyhow::Result<Value> {
    let request: ReadRequest = parse("fs.read", &call)?;
    kernel_cwd(&host, "fs.read", &call, &request.cwd)?;
    let reply = match blocking(move || host.documents.read(&request.cwd, &request.path)).await? {
        Ok(view) => Reply::Done(read_reply(view)),
        Err(error) => Reply::rejected(READ_REV, read_rejection(&error), &error),
    };
    Ok(serde_json::to_value(reply)?)
}

async fn write(host: Arc<DocumentsHost>, call: HostCall) -> anyhow::Result<Value> {
    let request: WriteRequest = parse("fs.write", &call)?;
    kernel_cwd(&host, "fs.write", &call, &request.cwd)?;
    let result = blocking(move || {
        host.documents
            .write(&request.cwd, &request.path, &request.content)
    })
    .await?;
    let reply = match result {
        Ok(outcome) => Reply::Done(write_reply(outcome)),
        Err(error) => Reply::rejected(WRITE_REV, write_rejection(&error), &error),
    };
    Ok(serde_json::to_value(reply)?)
}

async fn edit(host: Arc<DocumentsHost>, call: HostCall) -> anyhow::Result<Value> {
    let request: EditRequest = parse("fs.edit", &call)?;
    kernel_cwd(&host, "fs.edit", &call, &request.cwd)?;
    let reply = match blocking(move || host.documents.edit(&request.cwd, &request.input)).await? {
        Ok(outcome) => Reply::Done(edit_reply(outcome)),
        Err(error) => Reply::rejected(EDIT_REV, edit_rejection(&error), &error),
    };
    Ok(serde_json::to_value(reply)?)
}

async fn grep(host: Arc<DocumentsHost>, call: HostCall) -> anyhow::Result<Value> {
    let call_request: GrepCall = parse("fs.grep", &call)?;
    kernel_cwd(&host, "fs.grep", &call, &call_request.cwd)?;
    let request = GrepRequest {
        pattern: call_request.pattern,
        path: call_request.path,
        glob: call_request.glob,
        ignore_case: call_request.ignore_case,
        gitignore: true,
        context_before: call_request.context,
        context_after: call_request.context,
        skip: call_request.skip,
        limit: call_request.limit,
    };
    let cwd = call_request.cwd;
    let reply = match blocking(move || host.documents.grep(&cwd, &request)).await? {
        Ok(output) => Reply::Done(grep_reply(output)),
        Err(error) => Reply::rejected(GREP_REV, grep_rejection(&error), &error),
    };
    Ok(serde_json::to_value(reply)?)
}

async fn glob(host: Arc<DocumentsHost>, call: HostCall) -> anyhow::Result<Value> {
    let call_request: GlobCall = parse("fs.glob", &call)?;
    kernel_cwd(&host, "fs.glob", &call, &call_request.cwd)?;
    let request = GlobRequest {
        path: call_request.path,
        hidden: call_request.hidden,
        gitignore: true,
        limit: call_request.limit,
    };
    let cwd = call_request.cwd;
    let reply = match blocking(move || host.documents.glob(&cwd, &request)).await? {
        Ok(output) => Reply::Done(glob_reply(output)),
        Err(error) => Reply::rejected(GLOB_REV, glob_rejection(&error), &error),
    };
    Ok(serde_json::to_value(reply)?)
}

/// Register the `fs.*` requests over `host`.
pub(super) fn register(registry: &HostRequestRegistry, host: &Arc<DocumentsHost>) {
    macro_rules! handler {
        ($request_type:literal, $function:path) => {{
            let host = Arc::clone(host);
            registry.register(
                $request_type,
                Arc::new(move |call: HostCall| $function(Arc::clone(&host), call).boxed()),
            );
        }};
    }
    handler!("fs.read", read);
    handler!("fs.write", write);
    handler!("fs.edit", edit);
    handler!("fs.grep", grep);
    handler!("fs.glob", glob);
}

#[cfg(test)]
mod tests;
