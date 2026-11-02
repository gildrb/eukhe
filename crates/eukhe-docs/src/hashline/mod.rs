//! Hashline edits: `[path#TAG]` sections of line-anchored `PUT`/`CUT`/`REM`/`MV`
//! ops, ported from omp (`crates/edit/src/modes/hashline`, `session.rs`).
//!
//! [`apply_hashline`] parses a payload, stages every section in memory
//! (all-or-nothing), gives every write to the host's [`EditWriter`] in one
//! call (checked all before any is written), records the written text as
//! the new snapshot, and renders omp's result
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
mod endings;
mod input;
mod messages;
mod mismatch;
mod parse_error;
mod parser;
mod patcher;
mod prefixes;
mod recovery;
mod seen;
mod tokenizer;
mod types;

#[cfg(test)]
mod tests;

use std::path::{Path, PathBuf};

use eukhe_types::path_policy::real_path;

pub use self::parse_error::HashlineParseError;

use self::{
    input::split_sections,
    messages::write_drift_warning,
    patcher::{stage_patch, StagedFile, StagedOp, Workspace},
};
use crate::{
    diff_string::build_compact_diff_preview, error::EditError, store::EditStore, text::lf_text,
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
    /// Reject anchors on lines no read, grep, or edit showed the model
    /// (omp `edit.enforceSeenLines`); a session's [`crate::Documents`] sets it.
    pub enforce_seen_lines: bool,
}

/// The filesystem change one write performs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WriteOp<'a> {
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
    /// Write `content` to `destination`, which must not exist, and delete
    /// the source.
    Move {
        /// The source bytes read before the edit.
        before_raw: &'a str,
        /// Absolute destination path.
        destination: &'a Path,
        /// Destination path as the model wrote it.
        destination_display: &'a str,
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

/// What the host did with one write of a call.
#[derive(Debug)]
pub enum Published {
    /// The change is on disk.
    Landed {
        /// The text actually on disk after the write (a host may
        /// reformat); empty for deletes.
        written: String,
        /// What `written` was made from.
        basis: Basis,
        /// What a step after the change landed met (a failed directory
        /// sync, a moved file's source not removed, the rebase of the
        /// change onto bytes another program wrote).
        warnings: Vec<String>,
    },
    /// The change is not on disk.
    Failed(EditError),
}

/// What the text that landed was made from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Basis {
    /// The bytes the edit was staged on.
    Staged,
    /// Bytes another program wrote while the edit was being written: the
    /// change was rebased onto them.
    Rebased,
}

/// The host-owned writer every hashline write goes through.
///
/// The engine never writes to disk. It calls [`EditWriter::write_all`] once
/// per call with every changed file, in payload order. An implementation
/// first checks every request: it refuses the whole call with an error,
/// writing nothing, when a file's current bytes differ from `before_raw`
/// (the engine applied the edit to those bytes) or a move destination
/// exists. Then it performs each change atomically, in order, and stops
/// after the first change that fails. It returns one [`Published`] per
/// request it tried: fewer than the requests when a failure stopped it.
/// When the text that landed differs from `content`, the engine warns and
/// records the landed text as the new snapshot. A change the host rebased
/// onto bytes another program wrote after the check lands as
/// [`Basis::Rebased`]: the lines that program wrote are not seen.
pub trait EditWriter {
    /// Check every request, then perform them in order.
    ///
    /// # Errors
    ///
    /// The model-facing reason the call wrote nothing: a file changed, a
    /// move destination exists, or a lock or a read failed.
    fn write_all(&self, requests: &[WriteRequest<'_>]) -> Result<Vec<Published>, EditError>;
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
    /// The edit of this file did not land: its write failed, or an earlier
    /// write of the call failed first. The file is as it was.
    NotWritten {
        /// Why, model-facing.
        reason: String,
    },
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
    /// Model-facing text: when a file did not land, a line that names the
    /// files applied and not applied; then the per-file texts joined by a
    /// blank line.
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
/// failure there writes nothing. The changed files then go to `writer` in
/// one call, which checks them all before it writes any (a conflict writes
/// nothing) and then writes them in order. The text that landed is recorded
/// in `store` as each file's new snapshot (its tag heads the file's result
/// text). When a write fails after earlier files landed, the outcome
/// reports, per file, what landed and what did not.
///
/// # Errors
///
/// Returns the model-facing parse, anchor, stale-tag, or seen-line error; a
/// no-op repeated `NOOP_HARD_LIMIT` times; or the writer's error when no
/// file landed.
#[allow(
    clippy::too_many_lines,
    reason = "one edit in order: split, stage, write, the core's reply, commit, render"
)]
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
    let requests: Vec<WriteRequest<'_>> = staged.iter().filter_map(write_request).collect();
    let mut published = if requests.is_empty() {
        Vec::new()
    } else {
        writer.write_all(&requests)?
    }
    .into_iter();
    drop(requests);
    // What became of each staged file; the reply is the core's choice
    // (`answer` of bend/doc_commit.bend). The engine knows only whether a
    // write landed: the warning's kind does not enter the reply.
    let mut by_file: Vec<Option<Published>> = Vec::with_capacity(staged.len());
    let fates: Vec<crate::commit::Fate> = staged
        .iter()
        .map(|file| match file.op {
            StagedOp::Noop { .. } => {
                by_file.push(None);
                crate::commit::Fate::Noop
            }
            StagedOp::Update { .. } | StagedOp::Delete => {
                let Some(write) = published.next() else {
                    by_file.push(None);
                    return crate::commit::Fate::Untried;
                };
                let outcome = match &write {
                    Published::Landed { .. } => {
                        crate::commit::Outcome::Lands(crate::commit::Warn::None)
                    }
                    Published::Failed(_) => crate::commit::Outcome::Fails,
                };
                by_file.push(Some(write));
                crate::commit::Fate::Wrote(outcome)
            }
        })
        .collect();
    let (notes, partial) = match crate::commit::answer(&fates) {
        crate::commit::Verdict::Failure => {
            let first = by_file.into_iter().flatten().find_map(|write| match write {
                Published::Failed(error) => Some(error),
                Published::Landed { .. } => None,
            });
            return Err(first.unwrap_or_else(|| crate::commit::inconsistent("a failed write")));
        }
        crate::commit::Verdict::Summary { notes, partial } => (notes, partial),
    };
    let displays: Vec<String> = staged.iter().map(|file| file.display.clone()).collect();
    let mut files = Vec::with_capacity(staged.len());
    for ((file, write), note) in staged.into_iter().zip(by_file).zip(notes) {
        let write = match (note, write) {
            (crate::commit::Note::Untouched, _) => Write::Unneeded,
            (
                crate::commit::Note::Written,
                Some(Published::Landed {
                    written,
                    basis,
                    warnings,
                }),
            ) => Write::Landed {
                written,
                basis,
                warnings,
            },
            (crate::commit::Note::Unwritten, Some(Published::Failed(error))) => {
                Write::NotWritten(error.to_string())
            }
            (crate::commit::Note::Skipped(at), None) => Write::NotWritten(format!(
                "not tried: the write of {} failed first",
                displays[at]
            )),
            (
                crate::commit::Note::Written
                | crate::commit::Note::Unwritten
                | crate::commit::Note::Skipped(_),
                _,
            ) => crate::commit::inconsistent("a note the write allows"),
        };
        files.push(commit(file, write, store));
    }
    let landed: Vec<&str> = files
        .iter()
        .filter(|file| match file.change {
            FileChange::Updated | FileChange::Moved { .. } | FileChange::Deleted => true,
            FileChange::Unchanged | FileChange::NotWritten { .. } => false,
        })
        .map(|file| file.display.as_str())
        .collect();
    let not_written: Vec<&str> = files
        .iter()
        .filter(|file| matches!(file.change, FileChange::NotWritten { .. }))
        .map(|file| file.display.as_str())
        .collect();
    let mut texts: Vec<String> = Vec::with_capacity(files.len() + 1);
    if partial {
        texts.push(format!(
            "Applied to {}; NOT applied to {}. The applied files have the new tags below; \
             re-read the others before you edit them again.",
            landed.join(", "),
            not_written.join(", ")
        ));
    }
    texts.extend(
        files
            .iter()
            .map(|file| file.text.clone())
            .filter(|text| !text.is_empty()),
    );
    let text = texts.join(EDIT_RESULT_SEPARATOR);
    Ok(HashlineOutcome { text, files })
}

/// The write a staged file needs; `None` for a no-op.
fn write_request(file: &StagedFile) -> Option<WriteRequest<'_>> {
    let op = match &file.op {
        StagedOp::Noop { .. } => return None,
        StagedOp::Delete => WriteOp::Delete {
            before_raw: &file.before_raw,
        },
        StagedOp::Update { persisted } => match &file.move_to {
            Some(destination) => WriteOp::Move {
                before_raw: &file.before_raw,
                destination: &destination.absolute,
                destination_display: &destination.display,
                content: persisted,
            },
            None => WriteOp::Update {
                before_raw: &file.before_raw,
                content: persisted,
            },
        },
    };
    Some(WriteRequest {
        absolute: &file.absolute,
        display: &file.display,
        op,
    })
}

/// What the writer did with one staged file.
enum Write {
    /// A no-op: nothing to write.
    Unneeded,
    /// The change is on disk.
    Landed {
        written: String,
        basis: Basis,
        warnings: Vec<String>,
    },
    /// The change is not on disk, for this reason.
    NotWritten(String),
}

/// Update the store with what landed of one staged file and render its
/// result text.
fn commit(mut file: StagedFile, write: Write, store: &EditStore) -> FileOutcome {
    let (written, basis, warnings) = match write {
        Write::Unneeded => (String::new(), Basis::Staged, Vec::new()),
        Write::Landed {
            written,
            basis,
            warnings,
        } => (written, basis, warnings),
        Write::NotWritten(reason) => {
            let text = format!("NOT applied to {}: {reason}", file.display);
            return FileOutcome {
                display: file.display,
                absolute: file.absolute,
                change: FileChange::NotWritten { reason },
                diff: file.diff,
                first_changed_line: file.first_changed_line,
                warnings: file.warnings,
                tag: None,
                text,
            };
        }
    };
    file.warnings.extend(warnings);
    let (change, tag, text) = match &file.op {
        StagedOp::Delete => {
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
            // The editable text that landed: `after` when the host wrote
            // exactly what was sent, else the reported bytes normalized.
            let recorded = if written == *persisted {
                file.after.clone()
            } else {
                lf_text(&written)
            };
            // The lines of the new text the model saw: the lines of the
            // base it saw that the edit kept, and every line the edit
            // wrote, less every line another program wrote meanwhile (a
            // rebased edit); `None` when the session holds no seen lines of
            // the base.
            let before = lf_text(&file.before_raw);
            let seen = store
                .by_content(&file.canonical, &before)
                .and_then(|snapshot| snapshot.seen_lines)
                .map(|seen| match basis {
                    Basis::Staged => {
                        carry_seen(&before, &recorded, |line| seen.contains(&line), Added::Seen)
                    }
                    Basis::Rebased => {
                        let edited = carry_seen(
                            &before,
                            &file.after,
                            |line| seen.contains(&line),
                            Added::Seen,
                        );
                        carry_seen(
                            &file.after,
                            &recorded,
                            |line| edited.binary_search(&line).is_ok(),
                            Added::Unseen,
                        )
                    }
                });
            let (key, change) = if let Some(destination) = &file.move_to {
                let key = real_path(&destination.absolute);
                store.relocate(&file.canonical, &key);
                let change = FileChange::Moved {
                    destination: destination.absolute.clone(),
                };
                (key, change)
            } else {
                if basis == Basis::Staged && recorded != file.after {
                    file.warnings.push(write_drift_warning(&file.display));
                }
                (file.canonical.clone(), FileChange::Updated)
            };
            match basis {
                // The write tool may replace exactly these bytes.
                Basis::Staged => store.saw_bytes(&key, written.as_bytes()),
                // Another program's lines are in them: the model has not
                // seen these bytes.
                Basis::Rebased => {}
            }
            let tag = store.record(&key, &recorded, seen.as_deref());
            store.reset_noop(&file.canonical);
            let text = format_file_text(&file, &tag);
            (change, Some(tag), text)
        }
    };
    store.commit_clipboard(&file.clipboard_after);
    FileOutcome {
        display: file.display,
        absolute: file.absolute,
        change,
        diff: file.diff,
        first_changed_line: file.first_changed_line,
        warnings: file.warnings,
        tag,
        text,
    }
}

/// Who wrote the lines a change added.
#[derive(Clone, Copy)]
pub(crate) enum Added {
    /// The edit: the model saw them.
    Seen,
    /// Another program: the model has not seen them.
    Unseen,
}

/// The seen lines of `new` (ascending), changed from `old` whose seen
/// lines `seen` answers: a kept line keeps its state; an added line is
/// seen only when the edit wrote it.
pub(crate) fn carry_seen(
    old: &str,
    new: &str,
    seen: impl Fn(u32) -> bool,
    added: Added,
) -> Vec<u32> {
    let (mut at_old, mut at_new) = (1_u32, 1_u32);
    let mut carried = Vec::new();
    for run in crate::diff::line_runs(old, new) {
        match (run.added, run.removed) {
            (true, false | true) => {
                match added {
                    Added::Seen => carried.extend(at_new..at_new + run.count),
                    Added::Unseen => {}
                }
                at_new += run.count;
            }
            (false, true) => at_old += run.count,
            (false, false) => {
                carried.extend(
                    (0..run.count)
                        .filter(|offset| seen(at_old + offset))
                        .map(|offset| at_new + offset),
                );
                at_old += run.count;
                at_new += run.count;
            }
        }
    }
    carried
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
