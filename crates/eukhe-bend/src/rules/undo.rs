//! The per-prompt workspace snapshots of a top-level session
//! (`bend/undo.bend`, entry `bend/ffi_undo.bend`; `laws/undo.bend`):
//! [`step`] answers what a turn start, `/undo` or `/diff` does with the
//! snapshots; [`fixes`] what `/undo` does to each changed path, [`seens`]
//! what `/diff` says of it.

use eukhe_types::undo::DiffScope;

use crate::wire::{Reader, WireError, Writer};
use crate::{call, Entry, Error};

/// What happens to the snapshots (`U.Ev`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Event {
    /// A turn starts: its snapshot, numbered `turn`, is taken.
    TurnStart { turn: u64 },
    /// `/undo`.
    Undo,
    /// `/diff`.
    Diff(DiffScope),
}

/// The snapshots (`U.St`): the turns not undone, newest first, and the
/// session's first turn.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Snapshots {
    pub live: Vec<u64>,
    pub base: Option<u64>,
}

/// The answer to an [`Event`] (`U.Act`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Act {
    /// The turn's snapshot is kept.
    Took,
    /// Restore the snapshot of `turn`.
    Restore { turn: u64 },
    /// Nothing to undo: nothing changes.
    Refused,
    /// Compare the workspace with the snapshot of `turn`.
    Compare { turn: u64 },
    /// No snapshot to compare with.
    NoSnapshot,
}

/// Whether `/undo` may touch a path.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Reach {
    /// In the snapshot's scope.
    Open,
    /// Ignored, over the size cap, or a nested repository: never touched.
    Held,
}

/// One path (`U.Row`): its content in the snapshot and in the workspace (a
/// blob number of the caller's, `None` when absent).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Row {
    pub before: Option<u64>,
    pub now: Option<u64>,
    pub reach: Reach,
}

/// What `/undo` does to a row's path (`U.Fix`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fix {
    Keep,
    /// Delete it: added since the snapshot.
    Remove,
    /// Write the snapshot's content back.
    Write,
}

/// What `/diff` says of a row's path (`U.Seen`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Seen {
    Same,
    Differs,
    /// Held: not compared.
    Skipped,
}

fn maybe_code(m: Option<u64>) -> u64 {
    m.map_or(0, |t| t.saturating_add(1))
}

fn event_code(event: Event) -> u64 {
    match event {
        Event::Undo => 0,
        Event::Diff(DiffScope::Turn) => 1,
        Event::Diff(DiffScope::All) => 2,
        Event::TurnStart { turn } => turn.saturating_add(3),
    }
}

/// The snapshots after `event`, and its answer.
///
/// # Errors
///
/// [`Error::Wire`] when a turn number is past [`crate::wire::NAT_MAX`];
/// else only from an inconsistent build.
pub fn step(state: &Snapshots, event: Event) -> Result<(Snapshots, Act), Error> {
    let mut request = Writer::new();
    request.tag(0).count(state.live.len());
    for turn in &state.live {
        request.nat(*turn);
    }
    request.nat(maybe_code(state.base)).nat(event_code(event));
    let reply = call(Entry::Undo, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let act = match reader.tag_of(5, "an undo answer")? {
        0 => Act::Took,
        1 => Act::Restore {
            turn: reader.nat()?,
        },
        2 => Act::Refused,
        3 => Act::Compare {
            turn: reader.nat()?,
        },
        _ => Act::NoSnapshot,
    };
    let count = reader.count()?;
    let live = (0..count)
        .map(|_| reader.nat())
        .collect::<Result<Vec<u64>, WireError>>()?;
    let base = match reader.nat()? {
        0 => None,
        code => Some(code - 1),
    };
    reader.end()?;
    Ok((Snapshots { live, base }, act))
}

fn row_request(tag: u32, rows: &[Row]) -> Result<String, WireError> {
    let mut request = Writer::new();
    request.tag(tag).count(rows.len().saturating_mul(3));
    for row in rows {
        request
            .nat(maybe_code(row.before))
            .nat(maybe_code(row.now))
            .nat(match row.reach {
                Reach::Open => 0,
                Reach::Held => 1,
            });
    }
    request.finish()
}

fn row_codes(tag: u32, rows: &[Row]) -> Result<Vec<u64>, Error> {
    let reply = call(Entry::Undo, &row_request(tag, rows)?)?;
    let mut reader = Reader::reply(&reply)?;
    let count = reader.count()?;
    if count != rows.len() {
        return Err(WireError::Malformed {
            at: 0,
            expected: "one answer per row",
        }
        .into());
    }
    let codes = (0..count)
        .map(|_| reader.nat())
        .collect::<Result<Vec<u64>, WireError>>()?;
    reader.end()?;
    Ok(codes)
}

/// What `/undo` does to each row, in order.
///
/// # Errors
///
/// [`Error::Wire`] when a blob number is past [`crate::wire::NAT_MAX`];
/// else only from an inconsistent build.
pub fn fixes(rows: &[Row]) -> Result<Vec<Fix>, Error> {
    Ok(row_codes(1, rows)?
        .into_iter()
        .map(|code| match code {
            0 => Fix::Keep,
            1 => Fix::Remove,
            _ => Fix::Write,
        })
        .collect())
}

/// What `/diff` says of each row, in order.
///
/// # Errors
///
/// [`Error::Wire`] when a blob number is past [`crate::wire::NAT_MAX`];
/// else only from an inconsistent build.
pub fn seens(rows: &[Row]) -> Result<Vec<Seen>, Error> {
    Ok(row_codes(2, rows)?
        .into_iter()
        .map(|code| match code {
            0 => Seen::Same,
            1 => Seen::Differs,
            _ => Seen::Skipped,
        })
        .collect())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Turns 1 and 2, `/undo` (2 restored), turn 3: two more `/undo`
    /// restore 3 then 1, a third is refused; `/diff all` compares with 1.
    #[test]
    fn the_core_keeps_the_snapshot_stack() {
        let events = [
            Event::TurnStart { turn: 1 },
            Event::TurnStart { turn: 2 },
            Event::Undo,
            Event::TurnStart { turn: 3 },
            Event::Undo,
            Event::Diff(DiffScope::All),
            Event::Undo,
            Event::Undo,
        ];
        let (_, acts) = events.iter().fold(
            (Snapshots::default(), Vec::new()),
            |(state, mut acts), event| {
                let (next, act) = step(&state, *event).unwrap();
                acts.push(act);
                (next, acts)
            },
        );
        assert_eq!(
            acts,
            vec![
                Act::Took,
                Act::Took,
                Act::Restore { turn: 2 },
                Act::Took,
                Act::Restore { turn: 3 },
                Act::Compare { turn: 1 },
                Act::Restore { turn: 1 },
                Act::Refused,
            ]
        );
    }

    /// Added, removed, changed, unchanged and held paths.
    #[test]
    fn the_core_decides_each_path() {
        let row = |before, now, reach| Row { before, now, reach };
        let rows = [
            row(None, Some(1), Reach::Open),
            row(Some(2), None, Reach::Open),
            row(Some(3), Some(4), Reach::Open),
            row(Some(5), Some(5), Reach::Open),
            row(Some(6), None, Reach::Held),
        ];
        assert_eq!(
            (fixes(&rows).unwrap(), seens(&rows).unwrap()),
            (
                vec![Fix::Remove, Fix::Write, Fix::Write, Fix::Keep, Fix::Keep],
                vec![
                    Seen::Differs,
                    Seen::Differs,
                    Seen::Differs,
                    Seen::Same,
                    Seen::Skipped
                ]
            )
        );
    }
}
