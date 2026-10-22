//! The seen-line guard (model `bend/doc_seen.bend`, laws in `LAWS.bend`
//! section `documents`, F11): an edit's anchors against the lines a tagged
//! read displayed. [`check`] is the whole decision, plain data in and out;
//! the store lookups, the line widths it reads and the message it renders
//! stay in [`super::patcher`].

use std::collections::BTreeSet;

/// The most unseen anchors that one rejection shows (model `cap`).
pub(crate) const SEEN_LINE_REVEAL_CAP: usize = 40;
/// The most characters of a line that a rejection shows whole (model
/// `cols`).
pub(crate) const SEEN_LINE_REVEAL_MAX_COLUMNS: usize = 512;

/// A run of seen lines, `lo` to `hi` included (model `Iv`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Run {
    pub(crate) lo: u32,
    pub(crate) hi: u32,
}

/// An anchor and what the snapshot holds there: the width of its line in
/// characters, or `None` when the snapshot has no such line (model `At`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Anchor {
    pub(crate) line: u32,
    pub(crate) width: Option<usize>,
}

/// A line a rejection shows: whole (`cut: None`) or only its first `k`
/// characters (`cut: Some(k)`), then `…` (model `Show`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Shown {
    pub(crate) line: u32,
    pub(crate) cut: Option<usize>,
}

/// The guard's verdict (model `Check`): the unseen anchors in order (none:
/// the edit applies), the lines the rejection shows, and whether it showed
/// every unseen anchor whole (then they become seen).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Verdict {
    pub(crate) unseen: Vec<u32>,
    pub(crate) shown: Vec<Shown>,
    pub(crate) whole: bool,
}

/// The guard: an edit with these anchors on a snapshot with these seen
/// runs (model `check`).
pub(crate) fn check(seen: &[Run], anchors: &[Anchor]) -> Verdict {
    let unseen = anchors
        .iter()
        .filter(|anchor| {
            !seen
                .iter()
                .any(|run| run.lo <= anchor.line && anchor.line <= run.hi)
        })
        .collect::<Vec<_>>();
    let shown = unseen
        .iter()
        .take(SEEN_LINE_REVEAL_CAP)
        .filter_map(|anchor| {
            anchor.width.map(|width| Shown {
                line: anchor.line,
                cut: (width > SEEN_LINE_REVEAL_MAX_COLUMNS).then_some(SEEN_LINE_REVEAL_MAX_COLUMNS),
            })
        })
        .collect();
    let whole = unseen.len() <= SEEN_LINE_REVEAL_CAP
        && unseen.iter().all(|anchor| {
            anchor
                .width
                .is_some_and(|width| width <= SEEN_LINE_REVEAL_MAX_COLUMNS)
        });
    Verdict {
        unseen: unseen.iter().map(|anchor| anchor.line).collect(),
        shown,
        whole,
    }
}

/// The seen lines as maximal runs of consecutive lines.
pub(crate) fn runs(lines: &BTreeSet<u32>) -> Vec<Run> {
    let mut runs = Vec::<Run>::new();
    for &line in lines {
        match runs.last_mut() {
            Some(run) if run.hi.checked_add(1) == Some(line) => run.hi = line,
            Some(_) | None => runs.push(Run { lo: line, hi: line }),
        }
    }
    runs
}

/// Each anchor line with the width of that line of `text` (1-based; line
/// 0 and lines past the end have none). Reads `text` only up to the last
/// anchor.
pub(crate) fn anchors(text: &str, lines: &[u32]) -> Vec<Anchor> {
    let last = lines.iter().copied().max().unwrap_or(0);
    let rows = text
        .split('\n')
        .take(usize::try_from(last).unwrap_or(usize::MAX))
        .collect::<Vec<_>>();
    lines
        .iter()
        .map(|&line| Anchor {
            line,
            width: usize::try_from(line)
                .ok()
                .and_then(|n| n.checked_sub(1))
                .and_then(|n| rows.get(n))
                .map(|row| row.chars().count()),
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn runs_merge_consecutive_lines() {
        let lines = BTreeSet::from([1, 2, 3, 7, 9, 10, u32::MAX]);
        assert_eq!(
            runs(&lines),
            [
                Run { lo: 1, hi: 3 },
                Run { lo: 7, hi: 7 },
                Run { lo: 9, hi: 10 },
                Run {
                    lo: u32::MAX,
                    hi: u32::MAX
                },
            ]
        );
    }

    #[test]
    fn anchors_read_the_width_of_their_line() {
        let text = format!("a\n{}\nééé\n", "x".repeat(600));
        assert_eq!(
            anchors(&text, &[0, 1, 2, 3, 4, 5]),
            [
                Anchor {
                    line: 0,
                    width: None
                },
                Anchor {
                    line: 1,
                    width: Some(1)
                },
                Anchor {
                    line: 2,
                    width: Some(600)
                },
                Anchor {
                    line: 3,
                    width: Some(3)
                },
                Anchor {
                    line: 4,
                    width: Some(0)
                },
                Anchor {
                    line: 5,
                    width: None
                },
            ]
        );
    }
}
