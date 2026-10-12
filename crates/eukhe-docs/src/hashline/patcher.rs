//! Staging hashline sections: resolve, read, apply in memory, diff (omp
//! `modes/hashline/patcher.rs`). Nothing here writes; staging is
//! all-or-nothing, so any failure stages no file.

use std::{
    collections::HashMap,
    path::{Path, PathBuf},
};

use super::{
    apply::apply_edits,
    block::{has_block_edit, resolve_block_edits},
    clipboard::validate_clipboard_sequence,
    input::PatchSection,
    messages::{
        missing_snapshot_tag_message, path_recovered_from_tag_message, unseen_lines_message,
        RevealedLine, UnseenLinesReveal, HEADTAIL_DRIFT_WARNING,
    },
    mismatch::{mismatch_error, MismatchDetails},
    recovery::try_recover,
    types::{ApplyResult, Cursor, Edit, FileOp, PasteTarget},
};
use crate::{
    diff_string::generate_diff_string,
    error::EditError,
    path::{canonical_key, lexical_normalize},
    store::{file_hash, payload_hash, Clipboard, EditStore},
    text::{detect_line_ending, normalize_to_lf, restore_line_endings, strip_bom, LineEnding},
};

const SEEN_LINE_REVEAL_CAP: usize = 40;
const SEEN_LINE_REVEAL_MAX_COLUMNS: usize = 512;

/// Where authored paths resolve.
pub(crate) struct Workspace<'a> {
    pub(crate) cwd: &'a Path,
    pub(crate) home: Option<&'a Path>,
}

/// An edit target: the absolute path and the display path the model
/// authored (after tag path recovery).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Resolved {
    pub(crate) absolute: PathBuf,
    pub(crate) display: String,
}

impl Workspace<'_> {
    /// Resolve an authored path; a strict `[path]` / `[path#TAG]` wrapper
    /// is unwrapped first.
    fn resolve(&self, authored: &str) -> Resolved {
        let display = unwrap_hashline_header_path(authored).to_owned();
        let absolute = lexical_normalize(&crate::path::resolve(self.cwd, self.home, &display));
        Resolved { absolute, display }
    }
}

/// Strip a strict `[path]` / `[path#XXXX]` hashline header wrapper.
fn unwrap_hashline_header_path(target: &str) -> &str {
    let trimmed = target.trim_end();
    let Some(inner) = trimmed.strip_prefix('[').and_then(|s| s.strip_suffix(']')) else {
        return target;
    };
    let path = match inner.rsplit_once('#') {
        Some((path, tag)) if tag.len() == 4 && tag.bytes().all(|b| b.is_ascii_hexdigit()) => path,
        Some(_) => return target,
        None => inner,
    };
    if path.is_empty() || path.contains('#') {
        target
    } else {
        path
    }
}

/// One target file as read from disk plus its editable form.
struct FileRead {
    /// Snapshot-store key.
    canonical: PathBuf,
    /// Text as read: BOM and line endings intact.
    raw: String,
    bom: &'static str,
    ending: LineEnding,
    /// LF-normalized, BOM-stripped editable text.
    text: String,
}

impl FileRead {
    /// Read `absolute`; `None` when it does not exist.
    fn load(absolute: &Path) -> Result<Option<Self>, EditError> {
        let raw = match std::fs::read_to_string(absolute) {
            Ok(raw) => raw,
            Err(source) if source.kind() == std::io::ErrorKind::NotFound => return Ok(None),
            Err(source) => {
                return Err(EditError::Io {
                    path: absolute.to_path_buf(),
                    source,
                })
            }
        };
        let (bom, body) = strip_bom(&raw);
        let ending = detect_line_ending(body);
        let text = normalize_to_lf(body).into_owned();
        Ok(Some(Self {
            canonical: canonical_key(absolute),
            raw,
            bom,
            ending,
            text,
        }))
    }

    /// Encode LF post-edit text back to the bytes this file persists with:
    /// BOM and line endings restored.
    fn persist(&self, after_lf: &str) -> String {
        format!(
            "{}{}",
            self.bom,
            restore_line_endings(after_lf, self.ending)
        )
    }
}

/// What staging decided for one file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum StagedOp {
    /// Write `persisted` (to `move_to` when set).
    Update { persisted: String },
    /// `REM`: delete the file.
    Delete,
    /// The edit changed nothing; nothing is written and `diagnostic` is the
    /// whole result text.
    Noop { diagnostic: String },
}

/// One file's computed post-edit state, ready to be written.
#[derive(Debug, Clone)]
pub(crate) struct StagedFile {
    pub(crate) display: String,
    pub(crate) absolute: PathBuf,
    /// Snapshot-store key of `absolute`.
    pub(crate) canonical: PathBuf,
    pub(crate) op: StagedOp,
    /// Destination of `MV`.
    pub(crate) move_to: Option<Resolved>,
    /// Text as read, for the writer's compare-and-swap.
    pub(crate) before_raw: String,
    /// LF-normalized post-edit text.
    pub(crate) after: String,
    /// Numbered diff (`+N|`, `-N|`, ` N|` rows).
    pub(crate) diff: String,
    pub(crate) first_changed_line: Option<u32>,
    pub(crate) warnings: Vec<String>,
    /// Clipboard to publish once this file's write lands.
    pub(crate) clipboard_after: Clipboard,
}

/// Diagnostic for a clean, byte-identical hashline apply.
fn no_change_diagnostic(path: &str) -> String {
    format!(
        "Edits to {path} parsed and applied cleanly, but produced no change: your body row(s) are \
         byte-identical to the file at the targeted lines. The bug is somewhere else — re-read the \
         file before issuing another edit. Do NOT widen the payload or add lines; verify the anchor \
         first."
    )
}

/// Escalated diagnostic for a repeated identical no-op payload.
fn no_change_loop_diagnostic(path: &str, count: u32) -> String {
    format!(
        "STOP. Edits to {path} have been a byte-identical no-op {count} times in a row — the patch \
         body matches the file at the targeted lines and the soft hint did not break the cycle. \
         Cease re-issuing this payload. Either the intended change is already on disk (move on), or \
         your anchor is wrong (re-read the file with `read` to observe the current line numbers and \
         tag, then author a different edit). This exact payload will keep being rejected until it \
         changes."
    )
}

fn has_anchor_scoped_edit(edits: &[Edit]) -> bool {
    edits.iter().any(|edit| match edit {
        Edit::Delete { .. }
        | Edit::Block { .. }
        | Edit::Cut { .. }
        | Edit::Paste {
            at: PasteTarget::Span { .. },
            ..
        } => true,
        Edit::Paste {
            at: PasteTarget::Gap { cursor },
            ..
        }
        | Edit::Insert { cursor, .. } => {
            matches!(cursor, Cursor::BeforeAnchor(_) | Cursor::AfterAnchor(_))
        }
    })
}

/// Concrete anchor lines in ascending order without duplicates.
fn collect_anchor_lines(edits: &[Edit]) -> Vec<u32> {
    let mut lines = Vec::new();
    for edit in edits {
        match edit {
            Edit::Delete { anchor, .. } | Edit::Block { anchor, .. } => lines.push(anchor.line),
            Edit::Cut { range, .. }
            | Edit::Paste {
                at: PasteTarget::Span { range },
                ..
            } => {
                lines.extend(range.start.line..=range.end.line);
            }
            Edit::Paste {
                at: PasteTarget::Gap { cursor },
                ..
            }
            | Edit::Insert { cursor, .. } => match cursor {
                Cursor::BeforeAnchor(anchor) | Cursor::AfterAnchor(anchor) => {
                    lines.push(anchor.line);
                }
                Cursor::Bof | Cursor::Eof => {}
            },
        }
    }
    lines.sort_unstable();
    lines.dedup();
    lines
}

/// Reject a section whose tag does not name the live text. Records the
/// live text so a later tag from it is recognized.
fn mismatch(
    display: &str,
    anchor_lines: Vec<u32>,
    canonical: &Path,
    normalized: &str,
    expected: &str,
    store: &EditStore,
) -> EditError {
    let actual = store.record(canonical, normalized, None);
    mismatch_error(&MismatchDetails {
        path: display.to_owned(),
        expected_file_hash: expected.to_owned(),
        actual_file_hash: actual,
        file_lines: normalized.split('\n').map(str::to_owned).collect(),
        anchor_lines,
        hash_recognized: store.by_hash(canonical, expected).is_some(),
    })
}

/// Reject anchors on lines the tagged read never displayed, revealing their
/// content so a straight retry can succeed.
fn assert_seen_lines(
    display: &str,
    anchor_lines: &[u32],
    expected: &str,
    canonical: &Path,
    store: &EditStore,
    text: &str,
) -> Result<(), EditError> {
    let Some(snapshot) = store.by_content(canonical, text) else {
        return Ok(());
    };
    let Some(seen) = snapshot.seen_lines else {
        return Ok(());
    };
    if seen.is_empty() {
        return Ok(());
    }
    let unseen = anchor_lines
        .iter()
        .copied()
        .filter(|line| !seen.contains(line))
        .collect::<Vec<_>>();
    if unseen.is_empty() {
        return Ok(());
    }
    let source = snapshot.text.split('\n').collect::<Vec<_>>();
    let mut revealed = Vec::new();
    let mut column_truncated = false;
    for &line in unseen.iter().take(SEEN_LINE_REVEAL_CAP) {
        let Some(value) = usize::try_from(line)
            .ok()
            .and_then(|n| n.checked_sub(1))
            .and_then(|n| source.get(n))
        else {
            continue;
        };
        let chars = value.chars().collect::<Vec<_>>();
        if chars.len() > SEEN_LINE_REVEAL_MAX_COLUMNS {
            revealed.push(RevealedLine {
                line,
                text: chars[..SEEN_LINE_REVEAL_MAX_COLUMNS]
                    .iter()
                    .collect::<String>()
                    + "…",
            });
            column_truncated = true;
        } else {
            revealed.push(RevealedLine {
                line,
                text: (*value).to_owned(),
            });
        }
    }
    let truncated = unseen.len() > revealed.len() || column_truncated;
    if !truncated {
        store.record_seen_lines(
            canonical,
            expected,
            &revealed.iter().map(|item| item.line).collect::<Vec<_>>(),
        );
    }
    Err(EditError::matched(unseen_lines_message(
        display,
        &unseen,
        expected,
        &UnseenLinesReveal {
            lines: revealed,
            truncated,
        },
    )))
}

/// Apply a section whose tag names an older snapshot onto the live text,
/// or `None` to reject it as stale.
///
/// Runs omp's anchor remap ([`try_recover`]) on a clipboard fork, so a
/// failed attempt leaves `clipboard` untouched. Hook: the byte-level 3-way
/// rebase fallback (port of omp envd `docserver/rebase.rs`) goes after the
/// remap, with the snapshot `store.by_hash(canonical, tag)` as base, the
/// section applied to it as ours, and `live` as theirs.
fn recover_stale(
    store: &EditStore,
    canonical: &Path,
    live: &str,
    tag: &str,
    edits: &[Edit],
    clipboard: &mut Clipboard,
) -> Option<ApplyResult> {
    let mut fork = clipboard.fork();
    let recovered = try_recover(store, canonical, live, tag, edits, &mut fork)?;
    *clipboard = fork;
    Some(recovered)
}

/// Apply one section's edits to the live text `normalized`.
///
/// The live text matches the section when it hashes to the section tag and,
/// because the 16-bit tag can collide, the store holds no snapshot under
/// that tag or holds the live text itself. A matching section applies
/// directly; a stale one with only head/tail inserts applies with a warning;
/// any other stale section goes through [`recover_stale`] or is rejected.
#[allow(
    clippy::too_many_arguments,
    reason = "omp's apply_with_recovery contract: section identity, live text, edits, batch clipboard, store, policy"
)]
fn apply_with_recovery(
    display: &str,
    tag: &str,
    canonical: &Path,
    normalized: &str,
    edits: &[Edit],
    clipboard: &mut Clipboard,
    store: &EditStore,
    enforce_seen_lines: bool,
) -> Result<ApplyResult, EditError> {
    let anchor_lines = collect_anchor_lines(edits);
    let stored = store.by_hash(canonical, tag);
    let live_matches = file_hash(normalized).eq_ignore_ascii_case(tag)
        && (stored.is_none() || store.by_content(canonical, normalized).is_some());
    let mut warnings = Vec::new();
    let resolved = if has_block_edit(edits) {
        let base = if live_matches {
            normalized
        } else if let Some(snapshot) = &stored {
            &snapshot.text
        } else {
            return Err(mismatch(
                display,
                anchor_lines,
                canonical,
                normalized,
                tag,
                store,
            ));
        };
        resolve_block_edits(edits, base, &mut |warning| warnings.push(warning))?
    } else {
        edits.to_vec()
    };
    validate_clipboard_sequence(&resolved, clipboard)?;
    if live_matches {
        if enforce_seen_lines {
            assert_seen_lines(display, &anchor_lines, tag, canonical, store, normalized)?;
        }
        let mut result = apply_edits(normalized, &resolved, clipboard)?;
        warnings.append(&mut result.warnings);
        result.warnings = warnings;
        return Ok(result);
    }
    if !has_anchor_scoped_edit(&resolved) {
        let mut result = apply_edits(normalized, &resolved, clipboard)?;
        warnings.push(HEADTAIL_DRIFT_WARNING.to_owned());
        warnings.append(&mut result.warnings);
        result.warnings = warnings;
        return Ok(result);
    }
    if let Some(mut recovered) =
        recover_stale(store, canonical, normalized, tag, &resolved, clipboard)
    {
        warnings.append(&mut recovered.warnings);
        recovered.warnings = warnings;
        return Ok(recovered);
    }
    Err(mismatch(
        display,
        anchor_lines,
        canonical,
        normalized,
        tag,
        store,
    ))
}

/// Rebind a section whose path does not exist to the one retained snapshot
/// with the same file name and tag, when it lies under the workspace.
fn recover_target(
    section: &PatchSection,
    initial: Resolved,
    workspace: &Workspace<'_>,
    store: &EditStore,
) -> (PatchSection, Resolved) {
    let Some(tag) = section.file_hash.as_deref() else {
        return (section.clone(), initial);
    };
    if initial.absolute.exists() {
        return (section.clone(), initial);
    }
    let authored_name = initial.absolute.file_name();
    let mut candidates = store
        .find_by_hash(tag)
        .into_iter()
        .filter(|snapshot| {
            snapshot.path.file_name() == authored_name && snapshot.path != initial.absolute
        })
        .map(|snapshot| snapshot.path)
        .collect::<Vec<_>>();
    candidates.sort();
    candidates.dedup();
    let cwd = lexical_normalize(workspace.cwd);
    if candidates.len() != 1 || !lexical_normalize(&candidates[0]).starts_with(&cwd) {
        return (section.clone(), initial);
    }
    let path = candidates.remove(0);
    let display = path.to_string_lossy().into_owned();
    (
        section.with_path(&display),
        Resolved {
            absolute: path,
            display,
        },
    )
}

/// Stage every section atomically, in payload order.
#[allow(
    clippy::too_many_lines,
    reason = "omp's per-section staging sequence, ported as one function"
)]
pub(crate) fn stage_patch(
    sections: &[PatchSection],
    raw_input: &str,
    enforce_seen_lines: bool,
    workspace: &Workspace<'_>,
    store: &EditStore,
) -> Result<Vec<StagedFile>, EditError> {
    let mut clipboard = store.start_clipboard_batch();
    let mut staged = Vec::with_capacity(sections.len());
    let mut canonical_paths = HashMap::<PathBuf, String>::new();
    for original in sections {
        let parsed = original.parse()?;
        let Some(tag) = original.file_hash.as_deref() else {
            return Err(EditError::apply(missing_snapshot_tag_message(
                &original.path,
            )));
        };
        let initial = workspace.resolve(&original.path);
        let (section, resolved) = recover_target(original, initial, workspace, store);
        let read = FileRead::load(&resolved.absolute)?.ok_or_else(|| {
            EditError::apply(format!(
                "File not found: {}. Use the write tool to create new files.",
                section.path
            ))
        })?;
        if let Some(previous) =
            canonical_paths.insert(read.canonical.clone(), original.path.clone())
        {
            return Err(EditError::apply(format!(
                "Multiple hashline sections resolve to the same file ({previous} and {}). Merge their \
                 ops under one header before applying.",
                original.path
            )));
        }
        let move_to = match &parsed.file_op {
            Some(FileOp::Move { dest }) => {
                let destination = workspace.resolve(dest);
                if canonical_key(&destination.absolute) == read.canonical {
                    return Err(EditError::apply(format!(
                        "MV destination is the same as {}.",
                        section.path
                    )));
                }
                Some(destination)
            }
            Some(FileOp::Rem) | None => None,
        };
        let edits = match parsed.file_op {
            Some(FileOp::Rem) => &[][..],
            Some(FileOp::Move { .. }) | None => parsed.edits.as_slice(),
        };
        let apply = apply_with_recovery(
            &section.path,
            tag,
            &read.canonical,
            &read.text,
            edits,
            &mut clipboard,
            store,
            enforce_seen_lines,
        )?;
        let mut warnings = parsed.warnings;
        if section.path != original.path {
            warnings.push(path_recovered_from_tag_message(
                &original.path,
                &section.path,
                tag,
            ));
        }
        warnings.extend(apply.warnings);
        let diff = generate_diff_string(&read.text, &apply.text);
        let op = match parsed.file_op {
            Some(FileOp::Rem) => StagedOp::Delete,
            None if apply.text == read.text => StagedOp::Noop {
                diagnostic: no_change_diagnostic(&original.path),
            },
            Some(FileOp::Move { .. }) | None => StagedOp::Update {
                persisted: read.persist(&apply.text),
            },
        };
        if matches!(op, StagedOp::Noop { .. }) && sections.len() == 1 {
            let (count, escalate) = store.record_noop(&read.canonical, payload_hash(raw_input));
            if escalate {
                return Err(EditError::apply(no_change_loop_diagnostic(
                    &original.path,
                    count,
                )));
            }
        }
        staged.push(StagedFile {
            display: section.path.clone(),
            absolute: resolved.absolute,
            canonical: read.canonical,
            op,
            move_to,
            before_raw: read.raw,
            after: apply.text,
            diff: diff.diff,
            first_changed_line: apply.first_changed_line.or(diff.first_changed_line),
            warnings,
            clipboard_after: clipboard.fork(),
        });
    }
    if staged.len() > 1 {
        if let Some(item) = staged
            .iter()
            .find(|item| matches!(item.op, StagedOp::Noop { .. }))
        {
            let (count, escalate) = store.record_noop(&item.canonical, payload_hash(raw_input));
            return Err(EditError::apply(if escalate {
                no_change_loop_diagnostic(&item.display, count)
            } else {
                no_change_diagnostic(&item.display)
            }));
        }
    }
    Ok(staged)
}
