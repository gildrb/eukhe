//! The three-way rebase of a stale edit (`bend/rebase.bend`, entry
//! `bend/ffi_rebase.bend`; `laws/rebase.bend`, spec
//! `spec/harness/rebase.bend`). Rust sends the base's and the head's lines
//! as ids (equal ids: equal lines) and the session's edits against the
//! base; the core answers the edits against the head, or the refusal with
//! its exact reason. The decision is the core's; this module only spells
//! the request and reads the reply.

use crate::wire::{Reader, WireError, Writer};
use crate::{call, expect_core, Entry, Error};

/// An edit: the lines `[start, end)` (0-based) become `lines`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LineEdit {
    /// The first replaced line.
    pub start: usize,
    /// One past the last replaced line.
    pub end: usize,
    /// The ids of the lines put there.
    pub lines: Vec<u64>,
}

/// Why the core refused a rebase (`edit`: the index of the edit, from 0).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Refusal {
    /// The edits are not sorted and apart within the base.
    Invalid { edit: usize },
    /// The head no longer holds the edit's lines with the context they
    /// were found by: the head changed what the edit touches.
    Moved { edit: usize },
    /// The edit's lines match more than once in the base or the head with
    /// every context up to the bound: refused, never guessed.
    Ambiguous { edit: usize },
    /// The edit lands before or over the one before it in the head.
    Crossed { edit: usize },
    /// The edits times the lines pass the core's work bound.
    TooLarge,
}

/// The core's answer to a rebase.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Outcome {
    /// The edits against the head, in order: each keeps its lines, sorted
    /// and apart within the head.
    Rebased(Vec<LineEdit>),
    /// The rebase is refused whole: no edit lands.
    Conflict(Refusal),
}

/// The edits `edits` against `base`, carried onto `head` by the compiled
/// core.
#[must_use]
pub fn rebase(base: &[u64], head: &[u64], edits: &[LineEdit]) -> Outcome {
    expect_core(Entry::Rebase, rebase_call(base, head, edits))
}

fn rebase_call(base: &[u64], head: &[u64], edits: &[LineEdit]) -> Result<Outcome, Error> {
    let mut writer = Writer::new();
    put_ids(&mut writer, base);
    put_ids(&mut writer, head);
    let flat: usize = edits.iter().map(|edit| 3 + edit.lines.len()).sum();
    writer.count(flat);
    for edit in edits {
        writer
            .count(edit.start)
            .count(edit.end)
            .count(edit.lines.len());
        for &line in &edit.lines {
            writer.nat(line);
        }
    }
    let reply = call(Entry::Rebase, &writer.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let outcome = if reader.tag_of(2, "a rebase outcome")? == 0 {
        Outcome::Rebased(landed(&mut reader, head.len(), edits.len())?)
    } else {
        Outcome::Conflict(refusal(&mut reader)?)
    };
    reader.end()?;
    Ok(outcome)
}

fn put_ids(writer: &mut Writer, ids: &[u64]) {
    writer.count(ids.len());
    for &id in ids {
        writer.nat(id);
    }
}

/// The flat edits of a `Rebased` reply. Checked to be one per edit sent,
/// sorted and within the head: the caller splices with them.
fn landed(reader: &mut Reader<'_>, head: usize, edits: usize) -> Result<Vec<LineEdit>, WireError> {
    let malformed = WireError::Malformed {
        at: 0,
        expected: "one edit per edit sent, sorted and within the head",
    };
    let mut left = reader.count()?;
    let mut out = Vec::with_capacity(edits);
    let mut floor = 0;
    while left > 0 {
        let start = reader.count()?;
        let end = reader.count()?;
        let count = reader.count()?;
        let lines = (0..count)
            .map(|_| reader.nat())
            .collect::<Result<Vec<_>, _>>()?;
        left = left
            .checked_sub(3 + count)
            .ok_or_else(|| malformed.clone())?;
        if start < floor || end < start || end > head {
            return Err(malformed);
        }
        floor = end;
        out.push(LineEdit { start, end, lines });
    }
    if out.len() == edits {
        Ok(out)
    } else {
        Err(malformed)
    }
}

fn refusal(reader: &mut Reader<'_>) -> Result<Refusal, WireError> {
    Ok(match reader.tag_of(5, "a rebase refusal")? {
        0 => Refusal::Invalid {
            edit: reader.count()?,
        },
        1 => Refusal::Moved {
            edit: reader.count()?,
        },
        2 => Refusal::Ambiguous {
            edit: reader.count()?,
        },
        3 => Refusal::Crossed {
            edit: reader.count()?,
        },
        // `tag_of` answers a tag below 5: this is 4.
        _ => Refusal::TooLarge,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn edit(start: usize, end: usize, lines: &[u64]) -> LineEdit {
        LineEdit {
            start,
            end,
            lines: lines.to_vec(),
        }
    }

    /// The core carries a stale edit past a head change, refuses an edit
    /// whose lines the head changed, and refuses a repeated alignment.
    #[test]
    fn the_core_rebases_line_edits() {
        assert_eq!(
            [
                rebase(
                    &[1, 2, 3, 4, 5, 6],
                    &[1, 2, 3, 4, 7, 5, 6],
                    &[edit(1, 2, &[8]), edit(5, 6, &[9])]
                ),
                rebase(&[1, 2, 3], &[1, 6, 3], &[edit(1, 2, &[7])]),
                rebase(&[1, 1, 1, 1], &[1, 1, 1, 1, 1], &[edit(1, 2, &[9])]),
            ],
            [
                Outcome::Rebased(vec![edit(1, 2, &[8]), edit(6, 7, &[9])]),
                Outcome::Conflict(Refusal::Moved { edit: 0 }),
                Outcome::Conflict(Refusal::Ambiguous { edit: 0 }),
            ]
        );
    }
}
