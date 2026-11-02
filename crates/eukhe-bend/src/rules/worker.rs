//! The two pure decisions of the "main + worker" session shape: the model
//! `bend/worker.bend`, entry `bend/ffi_worker.bend`, laws
//! `laws/worker.bend`.
//!
//! The pause of the worker tree: the caller keeps the [`PauseState`] (in a
//! durable doc) and sends it with each [`PauseEvent`]; the core answers the
//! next state and the [`PauseVerdict`]. A pause cancels nothing: a tool
//! call that started runs to its end; every boundary of a paused tree holds
//! until a resume or a waking message.
//!
//! The forward pick: main hands its user's messages past a cursor to the
//! worker, verbatim, with main's note.

use crate::wire::{Reader, WireError, Writer};
use crate::{call, Entry, Error};

/// Whether the worker tree runs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PauseMode {
    Run,
    Paused,
}

/// The pause state of a worker tree.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PauseState {
    pub mode: PauseMode,
    /// The boundary held while paused (the id its gate named).
    pub parked: Option<u64>,
    /// The messages kept while paused, in arrival order.
    pub kept: Vec<u64>,
    /// The tool calls that started and did not end.
    pub inflight: u64,
}

impl Default for PauseState {
    /// A new tree: running, nothing parked, kept or in flight.
    fn default() -> Self {
        Self {
            mode: PauseMode::Run,
            parked: None,
            kept: Vec::new(),
            inflight: 0,
        }
    }
}

/// What a run is about to start.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GateKind {
    Request,
    Tool,
    Spawn,
}

/// What happened to the worker tree.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PauseEvent {
    Pause,
    Resume,
    /// The run is about to start a boundary; `id` names it.
    Gate {
        kind: GateKind,
        id: u64,
    },
    /// A tool call that started ended.
    Done,
    /// A message reached the session; `wakes`: a user message or a forward
    /// from main (it wakes a paused tree), else a report or a note.
    Msg {
        id: u64,
        wakes: bool,
    },
    /// The run ended.
    End,
}

/// The answer to an event.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PauseVerdict {
    /// Start the boundary.
    Go,
    /// Wait at the boundary.
    Hold,
    /// These kept messages go to the run now, in order.
    Release(Vec<u64>),
    /// The message waits.
    Kept,
    /// The message goes as it would without the pause.
    Pass,
    /// Noted.
    Ack,
}

/// What main hands on: the new cursor, the seqs handed on, and the text.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ForwardPick {
    pub cursor: u64,
    pub picked: Vec<u64>,
    pub body: String,
}

/// The request tags of the entry.
const STEP: u32 = 0;
const FORWARD: u32 = 1;

/// The state after `event`, and the answer to it.
///
/// # Errors
///
/// A number past the wire's bound (99 999 999 999 999), or a failed call to
/// the compiled core.
pub fn pause_step(
    state: &PauseState,
    event: PauseEvent,
) -> Result<(PauseState, PauseVerdict), Error> {
    let mut w = Writer::new();
    w.tag(STEP);
    put_state(&mut w, state);
    match event {
        PauseEvent::Pause => w.tag(0),
        PauseEvent::Resume => w.tag(1),
        PauseEvent::Gate { kind, id } => w.tag(2).nat(kind_code(kind)).nat(id),
        PauseEvent::Done => w.tag(3),
        PauseEvent::Msg { id, wakes } => w.tag(4).nat(id).bool(wakes),
        PauseEvent::End => w.tag(5),
    };
    let reply = call(Entry::Worker, &w.finish()?)?;
    let mut r = Reader::reply(&reply)?;
    let next = read_state(&mut r)?;
    let verdict = match r.tag_of(6, "a pause verdict")? {
        0 => PauseVerdict::Go,
        1 => PauseVerdict::Hold,
        2 => PauseVerdict::Release(read_nats(&mut r)?),
        3 => PauseVerdict::Kept,
        4 => PauseVerdict::Pass,
        // `tag_of` answers a tag below 6: this is 5.
        _ => PauseVerdict::Ack,
    };
    r.end()?;
    Ok((next, verdict))
}

/// Main's user `messages` (seq, text, in transcript order) past `cursor`,
/// handed on with main's `note`.
///
/// # Errors
///
/// A number or text past the wire's bounds, or a failed call to the
/// compiled core.
pub fn forward_pick(
    cursor: u64,
    messages: &[(u64, &str)],
    note: Option<&str>,
) -> Result<ForwardPick, Error> {
    let mut w = Writer::new();
    w.tag(FORWARD).nat(cursor).count(messages.len());
    for (seq, text) in messages {
        w.nat(*seq).str(text);
    }
    match note {
        Some(note) => w.some().str(note),
        None => w.none(),
    };
    let reply = call(Entry::Worker, &w.finish()?)?;
    let mut r = Reader::reply(&reply)?;
    let pick = ForwardPick {
        cursor: r.nat()?,
        picked: read_nats(&mut r)?,
        body: r.str()?.to_string(),
    };
    r.end()?;
    Ok(pick)
}

fn kind_code(kind: GateKind) -> u64 {
    match kind {
        GateKind::Request => 0,
        GateKind::Tool => 1,
        GateKind::Spawn => 2,
    }
}

fn put_state(w: &mut Writer, state: &PauseState) {
    w.tag(match state.mode {
        PauseMode::Run => 0,
        PauseMode::Paused => 1,
    });
    match state.parked {
        Some(id) => w.some().nat(id),
        None => w.none(),
    };
    w.count(state.kept.len());
    for id in &state.kept {
        w.nat(*id);
    }
    w.nat(state.inflight);
}

fn read_state(r: &mut Reader<'_>) -> Result<PauseState, WireError> {
    let mode = if r.tag_of(2, "a pause mode")? == 0 {
        PauseMode::Run
    } else {
        PauseMode::Paused
    };
    let parked = if r.maybe()? { Some(r.nat()?) } else { None };
    let kept = read_nats(r)?;
    let inflight = r.nat()?;
    Ok(PauseState {
        mode,
        parked,
        kept,
        inflight,
    })
}

fn read_nats(r: &mut Reader<'_>) -> Result<Vec<u64>, WireError> {
    let count = r.count()?;
    let mut xs = Vec::with_capacity(count);
    for _ in 0..count {
        xs.push(r.nat()?);
    }
    Ok(xs)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn paused(parked: Option<u64>, kept: &[u64], inflight: u64) -> PauseState {
        PauseState {
            mode: PauseMode::Paused,
            parked,
            kept: kept.to_vec(),
            inflight,
        }
    }

    fn running(parked: Option<u64>, kept: &[u64], inflight: u64) -> PauseState {
        PauseState {
            mode: PauseMode::Run,
            parked,
            kept: kept.to_vec(),
            inflight,
        }
    }

    /// One call per event against the whole answer of the compiled core
    /// (the rule itself is pinned by `laws/worker.bend`).
    #[test]
    fn each_event_steps_in_the_core() {
        let steps = [
            pause_step(&PauseState::default(), PauseEvent::Pause),
            pause_step(&paused(Some(5), &[7], 1), PauseEvent::Resume),
            pause_step(
                &running(Some(5), &[], 1),
                PauseEvent::Gate {
                    kind: GateKind::Tool,
                    id: 6,
                },
            ),
            pause_step(
                &paused(None, &[], 1),
                PauseEvent::Gate {
                    kind: GateKind::Spawn,
                    id: 6,
                },
            ),
            pause_step(&paused(Some(6), &[], 1), PauseEvent::Done),
            pause_step(
                &paused(Some(6), &[7], 0),
                PauseEvent::Msg {
                    id: 9,
                    wakes: false,
                },
            ),
            pause_step(
                &paused(Some(6), &[7, 9], 0),
                PauseEvent::Msg {
                    id: 10,
                    wakes: true,
                },
            ),
            pause_step(
                &running(None, &[], 0),
                PauseEvent::Msg {
                    id: 11,
                    wakes: true,
                },
            ),
            pause_step(&paused(Some(6), &[7], 2), PauseEvent::End),
        ]
        .map(|step| step.expect("the core answers"));
        assert_eq!(
            steps,
            [
                (paused(None, &[], 0), PauseVerdict::Ack),
                (running(Some(5), &[], 1), PauseVerdict::Release(vec![7])),
                (running(None, &[], 2), PauseVerdict::Go),
                (paused(Some(6), &[], 1), PauseVerdict::Hold),
                (paused(Some(6), &[], 0), PauseVerdict::Ack),
                (paused(Some(6), &[7, 9], 0), PauseVerdict::Kept),
                (
                    running(Some(6), &[], 0),
                    PauseVerdict::Release(vec![7, 9, 10])
                ),
                (running(None, &[], 0), PauseVerdict::Pass),
                (paused(None, &[7], 0), PauseVerdict::Ack),
            ]
        );
    }

    /// Main hands on the messages past its cursor, verbatim, then its note.
    #[test]
    fn the_core_picks_what_to_forward() {
        assert_eq!(
            forward_pick(1, &[(1, "a"), (5, " b "), (3, "c\n")], Some("n"))
                .expect("the core answers"),
            ForwardPick {
                cursor: 5,
                picked: vec![5, 3],
                body: " b \n\nc\n\n\n[note from main] n".to_string(),
            }
        );
    }
}
