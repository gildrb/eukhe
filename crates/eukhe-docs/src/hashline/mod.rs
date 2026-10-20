//! Hashline edits: `[path#TAG]` sections of line-anchored `PUT`/`CUT`/`REM`/`MV`
//! ops, ported from omp (`crates/edit/src/modes/hashline`, `session.rs`).
//!
//! [`apply_hashline`] parses a payload, stages every section in memory
//! (all-or-nothing), writes each file through the host's [`EditWriter`],
//! records the written text as the new snapshot, and renders omp's result
//! text: `[path#NEWTAG]`, a compact preview of the edited lines, and a
//! `Warnings:` block.
//!
//! eukhe has no block resolver (tree-sitter, tool-surface design, Phase 5),
//! so block ops (`N*`) are rejected with omp's no-resolver message.

// Line numbers, line counts, and edit indices are `u32` like omp's; a text
// with more than `u32::MAX` lines cannot be held in memory, so the narrowing
// `usize` casts are bounded.
#![allow(
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss
)]

mod apply;
mod block;
mod clipboard;
mod input;
mod messages;
mod mismatch;
mod parser;
mod patcher;
mod prefixes;
mod recovery;
mod tokenizer;
mod types;

#[cfg(test)]
mod tests;

use std::path::{Path, PathBuf};

use eukhe_types::path_policy::real_path;

use self::{
    input::split_sections,
    messages::write_drift_warning,
    patcher::{stage_patch, StagedFile, StagedOp, Workspace},
};
use crate::{
    diff_string::build_compact_diff_preview,
    error::EditError,
    store::EditStore,
    text::{normalize_to_lf, strip_bom},
};

/// The `edit` tool description: omp's hashline prompt without the block
/// (`N*`) ops, which eukhe rejects for lack of a block resolver.
pub const HASHLINE_DESCRIPTION: &str = include_str!("../../prompts/hashline.md");

/// Separates per-file results in the model-facing text.
const EDIT_RESULT_SEPARATOR: &str = "\n\n";

/// Knobs and context for one [`apply_hashline`] call.
#[derive(Debug, Clone, Copy)]
pub struct HashlineOptions<'a> {
    /// Directory relative section paths resolve against.
    pub cwd: &'a Path,
    /// Directory `~` expands to; `None` keeps `~` literal.
    pub home: Option<&'a Path>,
    /// Reject anchors on lines the tagged read never displayed (omp
    /// `edit.enforceSeenLines`, off by default).
    pub enforce_seen_lines: bool,
}

/// The filesystem change one write performs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WriteOp<'a> {
    /// Create a file that did not exist. Hashline edits existing files only
    /// and never sends this.
    Create {
        /// Bytes to write.
        content: &'a str,
    },
    /// Replace the file's bytes.
    Update {
        /// The bytes read before the edit.
        before_raw: &'a str,
        /// Bytes to write.
        content: &'a str,
    },
    /// Delete the file.
    Delete {
        /// The bytes read before the edit.
        before_raw: &'a str,
    },
    /// Write `content` to `destination` and delete the source.
    Move {
        /// The source bytes read before the edit.
        before_raw: &'a str,
        /// Absolute destination path.
        destination: &'a Path,
        /// Bytes to write at `destination`.
        content: &'a str,
    },
}

/// One write the engine asks the host to perform.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WriteRequest<'a> {
    /// Absolute source path.
    pub absolute: &'a Path,
    /// Path as the model wrote it.
    pub display: &'a str,
    /// The change to perform.
    pub op: WriteOp<'a>,
}

/// What a write persisted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WriteResponse {
    /// The text actually on disk after the write (a host may reformat);
    /// empty for deletes.
    pub written: String,
}

/// The host-owned writer every hashline write goes through.
///
/// The engine never writes to disk. For each staged file, in payload order,
/// it calls [`EditWriter::write`] once. An implementation must perform the
/// requested change atomically, and must refuse it with an error when the
/// file's current bytes differ from `before_raw` (compare-and-swap): the
/// engine applied the edit to those bytes. It returns the text that landed;
/// when that differs from `content`, the engine warns and records the landed
/// text as the new snapshot. An error stops the call: files written before
/// it stay written, and the error is returned verbatim.
pub trait EditWriter {
    /// Perform one write and report the text that landed.
    ///
    /// # Errors
    ///
    /// Returns the model-facing reason the write did not happen.
    fn write(&self, request: &WriteRequest<'_>) -> Result<WriteResponse, EditError>;
}

/// What one file's edit did.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FileChange {
    /// The file was rewritten in place.
    Updated,
    /// The file was rewritten at `destination` and the source removed.
    Moved {
        /// Absolute destination path.
        destination: PathBuf,
    },
    /// The file was deleted (`REM`).
    Deleted,
    /// The edit produced no change; nothing was written.
    Unchanged,
}

/// One file's result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FileOutcome {
    /// Path as the model wrote it (after tag path recovery).
    pub display: String,
    /// Absolute source path.
    pub absolute: PathBuf,
    /// What happened to the file.
    pub change: FileChange,
    /// Numbered diff: `+N|new`, `-N|old`, ` N|context` rows.
    pub diff: String,
    /// First changed line of the new text.
    pub first_changed_line: Option<u32>,
    /// Warnings rendered in this file's `Warnings:` block.
    pub warnings: Vec<String>,
    /// Tag of the file's new content; `None` after a delete.
    pub tag: Option<String>,
    /// This file's model-facing result text.
    pub text: String,
}

/// The result of one [`apply_hashline`] call.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HashlineOutcome {
    /// Model-facing text: the per-file texts joined by a blank line.
    pub text: String,
    /// Per-file results in payload order.
    pub files: Vec<FileOutcome>,
}

/// The file paths a payload's sections name, as authored, in payload order.
///
/// # Errors
///
/// The payload's section headers do not parse.
pub fn section_paths(input: &str) -> Result<Vec<String>, EditError> {
    Ok(split_sections(input, Path::new(""))?
        .into_iter()
        .map(|section| section.path)
        .collect())
}

/// Apply a hashline payload.
///
/// Every section is parsed, resolved, and applied in memory first; any
/// failure there writes nothing. Each changed file is then written through
/// `writer`, and the text that landed is recorded in `store` as the file's
/// new snapshot (its tag heads the file's result text).
///
/// # Errors
///
/// Returns the model-facing parse, anchor, stale-tag, or seen-line error; a
/// no-op repeated `NOOP_HARD_LIMIT` times; or the writer's error.
pub fn apply_hashline(
    input: &str,
    options: &HashlineOptions<'_>,
    store: &EditStore,
    writer: &dyn EditWriter,
) -> Result<HashlineOutcome, EditError> {
    let sections = split_sections(input, options.cwd)?;
    if sections.is_empty() {
        return Err(EditError::apply("No hashline sections found in input."));
    }
    let workspace = Workspace {
        cwd: options.cwd,
        home: options.home,
    };
    let staged = stage_patch(
        &sections,
        input,
        options.enforce_seen_lines,
        &workspace,
        store,
    )?;
    let mut files = Vec::with_capacity(staged.len());
    for file in staged {
        files.push(commit(file, store, writer)?);
    }
    let text = files
        .iter()
        .map(|file| file.text.as_str())
        .filter(|text| !text.is_empty())
        .collect::<Vec<_>>()
        .join(EDIT_RESULT_SEPARATOR);
    Ok(HashlineOutcome { text, files })
}

/// Write one staged file, update the store, and render its result text.
fn commit(
    mut file: StagedFile,
    store: &EditStore,
    writer: &dyn EditWriter,
) -> Result<FileOutcome, EditError> {
    let (change, tag, text) = match &file.op {
        StagedOp::Delete => {
            writer.write(&WriteRequest {
                absolute: &file.absolute,
                display: &file.display,
                op: WriteOp::Delete {
                    before_raw: &file.before_raw,
                },
            })?;
            store.invalidate(&file.canonical);
            (
                FileChange::Deleted,
                None,
                format!("Deleted {}", file.display),
            )
        }
        StagedOp::Noop { diagnostic } => (
            FileChange::Unchanged,
            Some(store.record(&file.canonical, &file.after, None)),
            diagnostic.clone(),
        ),
        StagedOp::Update { persisted } => {
            let op = match &file.move_to {
                Some(destination) => WriteOp::Move {
                    before_raw: &file.before_raw,
                    destination: &destination.absolute,
                    content: persisted,
                },
                None => WriteOp::Update {
                    before_raw: &file.before_raw,
                    content: persisted,
                },
            };
            let response = writer.write(&WriteRequest {
                absolute: &file.absolute,
                display: &file.display,
                op,
            })?;
            // The editable text that landed: `after` when the host wrote
            // exactly what was sent, else the reported bytes normalized.
            let recorded = if response.written == *persisted {
                file.after.clone()
            } else {
                normalize_to_lf(strip_bom(&response.written).1).into_owned()
            };
            let (key, change) = if let Some(destination) = &file.move_to {
                let key = real_path(&destination.absolute);
                store.relocate(&file.canonical, &key);
                let change = FileChange::Moved {
                    destination: destination.absolute.clone(),
                };
                (key, change)
            } else {
                if recorded != file.after {
                    file.warnings.push(write_drift_warning(&file.display));
                }
                (file.canonical.clone(), FileChange::Updated)
            };
            let tag = store.record(&key, &recorded, None);
            store.reset_noop(&file.canonical);
            let text = format_file_text(&file, &tag);
            (change, Some(tag), text)
        }
    };
    store.commit_clipboard(&file.clipboard_after);
    Ok(FileOutcome {
        display: file.display,
        absolute: file.absolute,
        change,
        diff: file.diff,
        first_changed_line: file.first_changed_line,
        warnings: file.warnings,
        tag,
        text,
    })
}

/// Model-facing text for one written file (omp `format_file_text`).
fn format_file_text(file: &StagedFile, tag: &str) -> String {
    let header_path = file
        .move_to
        .as_ref()
        .map_or(file.display.as_str(), |destination| {
            destination.display.as_str()
        });
    let mut lines = vec![format!("[{header_path}#{tag}]")];
    if let Some(destination) = &file.move_to {
        lines.push(format!("Moved to {}", destination.display));
    }
    let preview = build_compact_diff_preview(&file.diff);
    if !preview.is_empty() {
        lines.push(preview);
    }
    let body = lines.join("\n");
    let warnings: Vec<&str> = file
        .warnings
        .iter()
        .map(String::as_str)
        .filter(|warning| !warning.is_empty())
        .collect();
    if warnings.is_empty() {
        body
    } else {
        format!("{body}\n\nWarnings:\n{}", warnings.join("\n"))
    }
}
