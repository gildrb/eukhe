//! Staging hashline sections: resolve, read, apply in memory, diff (omp
//! `modes/hashline/patcher.rs`). Nothing here writes; staging is
//! all-or-nothing, so any failure stages no file.

use std::{
    collections::HashMap,
    path::{Path, PathBuf},
};

use super::{
    apply::{apply_edits, diff_origins},
    block::reject_block_edits,
    clipboard::validate_clipboard_sequence,
    input::PatchSection,
    messages::{
        already_landed_message, anchored_context_lines, missing_snapshot_tag_message,
        path_recovered_from_tag_message, unseen_lines_message, RevealedLine, UnseenLinesReveal,
        HEADTAIL_DRIFT_WARNING, RECOVERY_REBASE_WARNING,
    },
    mismatch::{mismatch_error, MismatchDetails},
    recovery::try_recover,
    types::{ApplyResult, Cursor, Edit, FileOp, Landing, PasteTarget},
};
use crate::{
    diff_string::generate_diff_string,
    error::EditError,
    path::lexical_normalize,
    rebase::rebase_content,
    store::{file_hash, payload_hash, Clipboard, EditStore},
    text::{encoding_name, line_endings, normalize_to_lf, strip_bom, LineEnding},
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
pub(crate) struct FileRead {
    /// Snapshot-store key.
    pub(crate) canonical: PathBuf,
    /// Text as read: BOM and line endings intact.
    pub(crate) raw: String,
    bom: &'static str,
    /// The ending of each line that has one: one item for each `\n` of `text`.
    endings: Vec<LineEnding>,
    /// BOM-stripped editable text with each CRLF made LF.
    pub(crate) text: String,
}

impl FileRead {
    /// Read `absolute`; `None` when it does not exist. `display` names the
    /// file in errors.
    pub(crate) fn load(absolute: &Path, display: &str) -> Result<Option<Self>, EditError> {
        let bytes = match std::fs::read(absolute) {
            Ok(bytes) => bytes,
            Err(source) if source.kind() == std::io::ErrorKind::NotFound => return Ok(None),
            Err(source) => {
                return Err(EditError::Io {
                    display: display.to_owned(),
                    path: absolute.to_path_buf(),
                    source,
                })
            }
        };
        let raw = String::from_utf8(bytes).map_err(|error| {
            EditError::apply(format!(
                "{display} is {}; `edit` changes UTF-8 text only. To see it, `read` it with \
                 `:raw`. To change it, `write` the whole file (it is then saved as UTF-8).",
                encoding_name(error.as_bytes())
            ))
        })?;
        let (bom, body) = strip_bom(&raw);
        let endings = line_endings(body);
        let text = normalize_to_lf(body).into_owned();
        Ok(Some(Self {
            canonical: eukhe_types::path_policy::real_path(absolute),
            bom,
            endings,
            text,
            raw,
        }))
    }

    /// Encode post-edit text back to the bytes this file persists with: the
    /// BOM, then each line with its ending. `origins[j]` is the index of
    /// the original line that line `j` of `after` came from. A line from
    /// the file keeps its own ending; a new line takes the ending written
    /// before it (at the start: the file's first ending, else LF).
    pub(crate) fn persist(&self, after: &str, origins: &[Option<usize>]) -> String {
        let mut out = String::with_capacity(after.len() + self.bom.len() + origins.len());
        out.push_str(self.bom);
        let mut carry = self.endings.first().copied().unwrap_or(LineEnding::Lf);
        let mut pieces = after.split('\n').enumerate().peekable();
        while let Some((index, piece)) = pieces.next() {
            out.push_str(piece);
            if pieces.peek().is_none() {
                break;
            }
            if let Some(&ending) = origins
                .get(index)
                .copied()
                .flatten()
                .and_then(|origin| self.endings.get(origin))
            {
                carry = ending;
            }
            out.push_str(match carry {
                LineEnding::Lf => "\n",
                LineEnding::CrLf => "\r\n",
            });
        }
        out
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
    /// [`Landing::Already`] when the section was found on disk already.
    pub(crate) landing: Landing,
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
/// live text so a later tag from it is recognized; the lines the error
/// prints are recorded as seen.
fn mismatch(
    display: &str,
    anchor_lines: Vec<u32>,
    canonical: &Path,
    normalized: &str,
    expected: &str,
    store: &EditStore,
) -> EditError {
    let file_lines = normalized
        .split('\n')
        .map(str::to_owned)
        .collect::<Vec<_>>();
    let shown = anchored_context_lines(&anchor_lines, file_lines.len())
        .into_iter()
        .collect::<Vec<_>>();
    let hash_recognized = store.by_hash(canonical, expected).is_some();
    let actual = store.record(canonical, normalized, Some(&shown));
    mismatch_error(&MismatchDetails {
        path: display.to_owned(),
        expected_file_hash: expected.to_owned(),
        actual_file_hash: actual,
        file_lines,
        anchor_lines,
        hash_recognized,
    })
}

/// Reject anchors on lines the tagged read never displayed, revealing their
/// content so a straight retry can succeed. With no snapshot of `text`, or
/// one with no seen lines, no line counts as seen.
fn assert_seen_lines(
    display: &str,
    anchor_lines: &[u32],
    expected: &str,
    canonical: &Path,
    store: &EditStore,
    text: &str,
) -> Result<(), EditError> {
    let snapshot = store.by_content(canonical, text);
    let held = snapshot.is_some();
    let seen = snapshot
        .and_then(|snapshot| snapshot.seen_lines)
        .unwrap_or_default();
    let unseen = anchor_lines
        .iter()
        .copied()
        .filter(|line| !seen.contains(line))
        .collect::<Vec<_>>();
    if unseen.is_empty() {
        return Ok(());
    }
    let source = text.split('\n').collect::<Vec<_>>();
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
        let lines = revealed.iter().map(|item| item.line).collect::<Vec<_>>();
        if held {
            store.record_seen_lines(canonical, expected, &lines);
        } else {
            store.record(canonical, text, Some(&lines));
        }
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

/// What the seen-line guard needs to check anchors against a snapshot.
#[derive(Clone, Copy)]
struct SeenGuard<'a> {
    display: &'a str,
    anchor_lines: &'a [u32],
}

/// Apply a section whose tag names an older snapshot onto the live text,
/// or `Ok(None)` to reject it as stale.
///
/// Tries omp's anchor remap ([`try_recover`]), then the byte-level
/// three-way rebase ([`rebase_stale`]), each on a clipboard fork, so a
/// failed attempt leaves `clipboard` untouched.
fn recover_stale(
    store: &EditStore,
    canonical: &Path,
    live: &str,
    tag: &str,
    edits: &[Edit],
    clipboard: &mut Clipboard,
    seen_guard: Option<SeenGuard<'_>>,
) -> Result<Option<ApplyResult>, EditError> {
    let mut fork = clipboard.fork();
    if let Some(recovered) = try_recover(store, canonical, live, tag, edits, &mut fork) {
        *clipboard = fork;
        return Ok(Some(recovered));
    }
    let mut fork = clipboard.fork();
    let Some(rebased) = rebase_stale(store, canonical, live, tag, edits, &mut fork, seen_guard)?
    else {
        return Ok(None);
    };
    *clipboard = fork;
    Ok(Some(rebased))
}

/// The byte-level three-way rebase (omp envd `docserver/rebase.rs`): apply
/// the section to the snapshot it was written against, then carry that
/// change onto the live text through regions both sides left unchanged.
/// `Ok(None)` when there is no snapshot, the section does not apply to it,
/// or the change overlaps what moved on disk.
///
/// Like omp's document server, anchors are checked against the snapshot's
/// seen lines before rebasing when `seen_guard` is set.
fn rebase_stale(
    store: &EditStore,
    canonical: &Path,
    live: &str,
    tag: &str,
    edits: &[Edit],
    clipboard: &mut Clipboard,
    seen_guard: Option<SeenGuard<'_>>,
) -> Result<Option<ApplyResult>, EditError> {
    let Some(base) = store.by_hash(canonical, tag) else {
        return Ok(None);
    };
    if let Some(guard) = seen_guard {
        assert_seen_lines(
            guard.display,
            guard.anchor_lines,
            tag,
            canonical,
            store,
            &base.text,
        )?;
    }
    let Ok(ours) = apply_edits(&base.text, edits, clipboard) else {
        return Ok(None);
    };
    let Some(Ok(rebased)) =
        rebase_content(base.text.as_bytes(), live.as_bytes(), ours.text.as_bytes()).ok()
    else {
        return Ok(None);
    };
    let Ok(text) = String::from_utf8(rebased.into_parts().0) else {
        return Ok(None);
    };
    let first_changed_line = live
        .split('\n')
        .zip(text.split('\n'))
        .position(|(before, after)| before != after)
        .or_else(|| (live != text).then(|| live.split('\n').count().min(text.split('\n').count())))
        .map(|index| u32::try_from(index + 1).unwrap_or(u32::MAX));
    let mut warnings = vec![RECOVERY_REBASE_WARNING.to_owned()];
    warnings.extend(ours.warnings);
    Ok(Some(ApplyResult {
        origins: diff_origins(live, &text),
        text,
        first_changed_line,
        warnings,
        landing: Landing::Fresh,
    }))
}

/// Apply one section's edits to the live text `normalized`.
///
/// The live text matches the section when it hashes to the section tag and,
/// because the 16-bit tag can collide, the store holds no snapshot under
/// that tag or holds the live text itself. A matching section applies
/// directly; a stale one with only head/tail inserts applies with a warning;
/// any other stale section goes through [`recover_stale`] or is rejected.
/// Block locators (`N*`) are rejected up front: there is no block resolver.
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
    reject_block_edits(edits)?;
    let anchor_lines = collect_anchor_lines(edits);
    let stored = store.by_hash(canonical, tag);
    let live_matches = file_hash(normalized).eq_ignore_ascii_case(tag)
        && (stored.is_none() || store.by_content(canonical, normalized).is_some());
    validate_clipboard_sequence(edits, clipboard)?;
    if live_matches {
        if enforce_seen_lines {
            assert_seen_lines(display, &anchor_lines, tag, canonical, store, normalized)?;
        }
        return apply_edits(normalized, edits, clipboard);
    }
    if !has_anchor_scoped_edit(edits) {
        // A retry of a head/tail insert that already landed: the edits
        // applied to the tagged snapshot give the live text.
        if let Some(base) = store.by_hash(canonical, tag) {
            let landed = apply_edits(&base.text, edits, &mut clipboard.fork())
                .is_ok_and(|ours| ours.text == normalized && ours.text != *base.text);
            if landed {
                return Ok(ApplyResult {
                    text: normalized.to_owned(),
                    origins: (0..normalized.split('\n').count()).map(Some).collect(),
                    landing: Landing::Already,
                    ..ApplyResult::default()
                });
            }
        }
        let mut result = apply_edits(normalized, edits, clipboard)?;
        let mut warnings = vec![HEADTAIL_DRIFT_WARNING.to_owned()];
        warnings.append(&mut result.warnings);
        result.warnings = warnings;
        return Ok(result);
    }
    let seen_guard = enforce_seen_lines.then_some(SeenGuard {
        display,
        anchor_lines: &anchor_lines,
    });
    if let Some(recovered) = recover_stale(
        store, canonical, normalized, tag, edits, clipboard, seen_guard,
    )? {
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
            let size = std::fs::metadata(workspace.resolve(&original.path).absolute)
                .ok()
                .map(|metadata| metadata.len());
            return Err(EditError::apply(missing_snapshot_tag_message(
                &original.path,
                size,
            )));
        };
        let initial = workspace.resolve(&original.path);
        let (section, resolved) = recover_target(original, initial, workspace, store);
        let read = FileRead::load(&resolved.absolute, &section.path)?.ok_or_else(|| {
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
                if eukhe_types::path_policy::real_path(&destination.absolute) == read.canonical {
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
        let op = match (parsed.file_op, apply.landing) {
            (Some(FileOp::Rem), Landing::Fresh | Landing::Already) => StagedOp::Delete,
            (None, Landing::Already) => StagedOp::Noop {
                diagnostic: already_landed_message(&original.path),
            },
            (None, Landing::Fresh) if apply.text == read.text => StagedOp::Noop {
                diagnostic: no_change_diagnostic(&original.path),
            },
            (Some(FileOp::Move { .. }), Landing::Fresh | Landing::Already)
            | (None, Landing::Fresh) => StagedOp::Update {
                persisted: read.persist(&apply.text, &apply.origins),
            },
        };
        let repeated_noop = matches!(op, StagedOp::Noop { .. }) && apply.landing == Landing::Fresh;
        if repeated_noop && sections.len() == 1 {
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
            landing: apply.landing,
            warnings,
            clipboard_after: clipboard.fork(),
        });
    }
    if staged.len() > 1 {
        if let Some(item) = staged
            .iter()
            .find(|item| matches!(item.op, StagedOp::Noop { .. }) && item.landing == Landing::Fresh)
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
