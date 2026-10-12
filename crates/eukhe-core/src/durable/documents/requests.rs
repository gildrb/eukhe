//! The `fs.read` and `fs.write` kernel host requests. Every reply carries
//! the function revision (`read@1`) and is either `done` with the typed
//! result or `rejected` with a reason and the model-facing message.

use std::path::PathBuf;
use std::sync::Arc;

use anyhow::Context as _;
use eukhe_docs::{
    Documents, Notice, ReadContent, ReadError, ReadView, WriteDisposition, WriteError,
    WriteOutcome,
};
use futures::FutureExt;
use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::durable::{HostCall, HostRequestRegistry};

const READ_REV: &str = "read@1";
const WRITE_REV: &str = "write@1";

/// The kernel's working directory comes with every request: relative paths
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

fn diag_lines(diags: &[Notice]) -> Vec<String> {
    diags.iter().map(ToString::to_string).collect()
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
        diags: diag_lines(&view.diags),
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

fn parse<T: for<'de> Deserialize<'de>>(request_type: &str, call: &HostCall) -> anyhow::Result<T> {
    let request: T = serde_json::from_value(call.data.clone())
        .with_context(|| format!("{request_type} request is malformed"))?;
    Ok(request)
}

fn require_absolute(request_type: &str, cwd: &std::path::Path) -> anyhow::Result<()> {
    anyhow::ensure!(
        cwd.is_absolute(),
        "{request_type} cwd must be absolute, got {}",
        cwd.display()
    );
    Ok(())
}

async fn read(documents: Arc<Documents>, call: HostCall) -> anyhow::Result<Value> {
    let request: ReadRequest = parse("fs.read", &call)?;
    require_absolute("fs.read", &request.cwd)?;
    let result =
        tokio::task::spawn_blocking(move || documents.read(&request.cwd, &request.path)).await?;
    let reply = match result {
        Ok(view) => Reply::Done(read_reply(view)),
        Err(error) => Reply::Rejected {
            version: READ_REV,
            reason: read_rejection(&error),
            message: error.to_string(),
        },
    };
    Ok(serde_json::to_value(reply)?)
}

async fn write(documents: Arc<Documents>, call: HostCall) -> anyhow::Result<Value> {
    let request: WriteRequest = parse("fs.write", &call)?;
    require_absolute("fs.write", &request.cwd)?;
    let result = tokio::task::spawn_blocking(move || {
        documents.write(&request.cwd, &request.path, &request.content)
    })
    .await?;
    let reply = match result {
        Ok(outcome) => Reply::Done(write_reply(outcome)),
        Err(error) => Reply::Rejected {
            version: WRITE_REV,
            reason: write_rejection(&error),
            message: error.to_string(),
        },
    };
    Ok(serde_json::to_value(reply)?)
}

/// Register `fs.read` and `fs.write` over `documents`.
pub(super) fn register(registry: &HostRequestRegistry, documents: &Arc<Documents>) {
    macro_rules! handler {
        ($request_type:literal, $function:path) => {{
            let documents = Arc::clone(documents);
            registry.register(
                $request_type,
                Arc::new(move |call: HostCall| $function(Arc::clone(&documents), call).boxed()),
            );
        }};
    }
    handler!("fs.read", read);
    handler!("fs.write", write);
}

#[cfg(test)]
mod tests;
