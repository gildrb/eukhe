//! Line-level three-way rebase of a stale edit: the plumbing around the
//! compiled core's decision (`eukhe_bend::rules::rebase`, `bend/rebase.bend`).
//!
//! The session wrote `proposed` from `base` (the snapshot its tag names);
//! the file is now `head`. This module interns every line (jsdiff line
//! tokens: a line keeps its `\n`) to one id, describes the session's change
//! as line edits against the base (the runs of the jsdiff line diff, the
//! same diff the hashline engine shows), asks the core where those edits
//! land in the head, and splices the session's lines there. Where an edit
//! lands, or why the rebase is refused, is the core's alone.

use std::collections::HashMap;

use eukhe_bend::rules::rebase::{self, LineEdit, Outcome, Refusal};

use crate::diff::{line_runs, line_tokens};

/// Why a stale edit could not be carried onto the current file; nothing
/// was applied.
#[derive(Clone, Copy, Debug, Eq, PartialEq, thiserror::Error)]
#[error("text proposal conflicts with the current file: {refusal:?}")]
pub(crate) struct RebaseConflict {
    refusal: Refusal,
}

/// A run of the session's lines replacing base lines: the edit sent to the
/// core and where its lines sit in `proposed`.
struct Hunk {
    edit: LineEdit,
    proposed: std::ops::Range<usize>,
}

/// `head` with the session's change from `base` to `proposed` carried onto
/// it.
///
/// # Errors
/// [`RebaseConflict`] with the core's refusal: the edits are not apart, the
/// head changed what an edit touches, an edit's place is ambiguous, two
/// edits cross in the head, or the input passes the core's work bound.
pub(crate) fn rebase_content(
    base: &str,
    head: &str,
    proposed: &str,
) -> Result<String, RebaseConflict> {
    let base_lines = line_tokens(base);
    let head_lines = line_tokens(head);
    let proposed_lines = line_tokens(proposed);
    let mut ids: HashMap<&str, u64> = HashMap::with_capacity(base_lines.len() + head_lines.len());
    let base_ids = intern(&mut ids, &base_lines);
    let head_ids = intern(&mut ids, &head_lines);
    let proposed_ids = intern(&mut ids, &proposed_lines);
    let hunks = hunks(base, proposed, &proposed_ids);
    let edits: Vec<LineEdit> = hunks.iter().map(|hunk| hunk.edit.clone()).collect();
    let landed = match rebase::rebase(&base_ids, &head_ids, &edits) {
        Outcome::Rebased(landed) => landed,
        Outcome::Conflict(refusal) => return Err(RebaseConflict { refusal }),
    };
    // The core answers one edit per hunk, sorted and within the head
    // (checked when its reply is read), so every range below is in bounds.
    let mut out = String::with_capacity(head.len() + proposed.len());
    let mut cursor = 0;
    for (hunk, edit) in hunks.iter().zip(&landed) {
        out.extend(head_lines[cursor..edit.start].iter().copied());
        out.extend(proposed_lines[hunk.proposed.clone()].iter().copied());
        cursor = edit.end;
    }
    out.extend(head_lines[cursor..].iter().copied());
    Ok(out)
}

/// The id of each line: equal lines, equal ids.
fn intern<'a>(ids: &mut HashMap<&'a str, u64>, lines: &[&'a str]) -> Vec<u64> {
    lines
        .iter()
        .map(|&line| {
            let next = ids.len() as u64;
            *ids.entry(line).or_insert(next)
        })
        .collect()
}

/// The session's change as line edits against the base: each maximal run
/// of removed and added lines of the line diff is one edit.
fn hunks(base: &str, proposed: &str, proposed_ids: &[u64]) -> Vec<Hunk> {
    let mut hunks = Vec::new();
    let (mut base_at, mut proposed_at) = (0_usize, 0_usize);
    let mut open: Option<(usize, usize)> = None;
    let mut close = |open: &mut Option<(usize, usize)>, base_at: usize, proposed_at: usize| {
        if let Some((base_start, proposed_start)) = open.take() {
            hunks.push(Hunk {
                edit: LineEdit {
                    start: base_start,
                    end: base_at,
                    lines: proposed_ids[proposed_start..proposed_at].to_vec(),
                },
                proposed: proposed_start..proposed_at,
            });
        }
    };
    for run in line_runs(base, proposed) {
        let count = run.count as usize;
        match (run.added, run.removed) {
            (false, false) => {
                close(&mut open, base_at, proposed_at);
                base_at += count;
                proposed_at += count;
            }
            (true, _) => {
                open.get_or_insert((base_at, proposed_at));
                proposed_at += count;
            }
            (false, true) => {
                open.get_or_insert((base_at, proposed_at));
                base_at += count;
            }
        }
    }
    close(&mut open, base_at, proposed_at);
    hunks
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Examples from the byte rebase's tests, one word per line (the rule
    /// now works on lines; `laws/rebase.bend` `rebase_example` holds them
    /// as ids).
    #[test]
    fn stale_edits_land_or_are_refused_whole() {
        assert_eq!(
            [
                rebase_content(
                    "alpha\nbeta\ngamma\n",
                    "ALPHA\nbeta\ngamma\n",
                    "alpha\nbeta\nGAMMA\n"
                ),
                rebase_content(
                    "alpha\nbeta\ngamma\n",
                    "alpha\nBETA\ngamma\n",
                    "alpha\nxx\ngamma\n"
                ),
                rebase_content("left\nright\n", "left\nA\nright\n", "left\nB\nright\n"),
                rebase_content(
                    "remove\nkeep\ntarget\n",
                    "keep\ntarget\n",
                    "remove\nkeep\nTARGET\n"
                ),
                rebase_content("a\na\na\na\n", "a\na\na\na\na\n", "a\nZ\na\na\n"),
                rebase_content(
                    "fn a() {}\nfn b() {}\nfn c() {}\n",
                    "fn a() { 1 }\nfn b() {}\nfn c() {}\n",
                    "fn a() {}\nfn b() {}\nfn c() { 3 }\n",
                ),
            ],
            [
                Ok("ALPHA\nbeta\nGAMMA\n".to_owned()),
                Err(RebaseConflict {
                    refusal: Refusal::Moved { edit: 0 }
                }),
                Err(RebaseConflict {
                    refusal: Refusal::Moved { edit: 0 }
                }),
                Ok("keep\nTARGET\n".to_owned()),
                Err(RebaseConflict {
                    refusal: Refusal::Ambiguous { edit: 0 }
                }),
                Ok("fn a() { 1 }\nfn b() {}\nfn c() { 3 }\n".to_owned()),
            ]
        );
    }

    /// A line without its final `\n` is another line than the one with it.
    #[test]
    fn a_missing_final_newline_is_its_own_line() {
        assert_eq!(
            rebase_content("a\nb", "a\nb\nc\n", "A\nb"),
            Ok("A\nb\nc\n".to_owned())
        );
    }
}
