//! One staged change of a submission's lifecycle (`bend/submission.bend`,
//! entry `bend/ffi_submission.bend`; `laws/submission.bend`): whether a
//! submission stays, moves to its next lifecycle, or refuses the change.
//! [`step`] encodes the submission and the change, calls
//! [`Entry::Submission`] and decodes the outcome.

use crate::wire::{Reader, Writer};
use crate::{call, Entry, Error};

/// A submission's lifecycle: its type, its status and its entry ids (`Sb.Sub`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Sub {
    /// An input admitted but not in the transcript yet.
    InputQueued,
    /// An input placed at its user entry.
    InputPlaced { entry: u64 },
    /// An input answered by the `answer` entry.
    InputAnswered { entry: u64, answer: u64 },
    /// An input settled without an answer, at its user entry when it was
    /// placed.
    InputUnanswered { entry: Option<u64> },
    /// A passive write admitted but not appended yet.
    WriteQueued,
    /// A passive write appended at `entry`.
    WriteDone { entry: u64 },
    /// A passive write settled without being placed.
    WriteUnanswered,
}

/// A staged change (`Sb.Change`); an unanswered settlement's reason and
/// detail stay with the caller.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Change {
    /// Place a queued submission at `entry`.
    Place { entry: u64 },
    /// Answer a placed input with the `answer` entry.
    Answer { answer: u64 },
    /// Settle the submission unanswered.
    Unanswered,
}

/// Why a change is refused (`Sb.Why`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Why {
    /// The submission is not queued.
    NotQueued,
    /// The submission is not a placed input.
    NotPlacedInput,
}

/// The outcome of a change (`Sb.Out`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Out {
    /// The submission stays as it is.
    Stays,
    /// The submission moves to this lifecycle.
    Moves(Sub),
    /// The change does not apply.
    Refused(Why),
}

fn put_sub(request: &mut Writer, sub: Sub) {
    match sub {
        Sub::InputQueued => request.tag(0),
        Sub::InputPlaced { entry } => request.tag(1).nat(entry),
        Sub::InputAnswered { entry, answer } => request.tag(2).nat(entry).nat(answer),
        Sub::InputUnanswered { entry: None } => request.tag(3),
        Sub::InputUnanswered { entry: Some(entry) } => request.tag(4).nat(entry),
        Sub::WriteQueued => request.tag(5),
        Sub::WriteDone { entry } => request.tag(6).nat(entry),
        Sub::WriteUnanswered => request.tag(7),
    };
}

fn get_sub(reply: &mut Reader<'_>) -> Result<Sub, Error> {
    Ok(match reply.tag_of(8, "a submission")? {
        0 => Sub::InputQueued,
        1 => Sub::InputPlaced {
            entry: reply.nat()?,
        },
        2 => Sub::InputAnswered {
            entry: reply.nat()?,
            answer: reply.nat()?,
        },
        3 => Sub::InputUnanswered { entry: None },
        4 => Sub::InputUnanswered {
            entry: Some(reply.nat()?),
        },
        5 => Sub::WriteQueued,
        6 => Sub::WriteDone {
            entry: reply.nat()?,
        },
        _ => Sub::WriteUnanswered,
    })
}

/// The outcome of `change` on `sub` (`Sb.step`): a settled submission
/// stays; placing moves a queued input to placed and a queued write to
/// done; an answer moves a placed input to answered; settling unanswered
/// moves any unsettled input or write to unanswered, an input keeping its
/// user entry; anything else is refused.
///
/// # Errors
///
/// [`Error::Wire`] when an entry id is past [`crate::wire::NAT_MAX`]; else
/// only from an inconsistent build (see [`crate::expect_core`]).
pub fn step(sub: Sub, change: Change) -> Result<Out, Error> {
    let mut request = Writer::new();
    put_sub(&mut request, sub);
    match change {
        Change::Place { entry } => request.tag(0).nat(entry),
        Change::Answer { answer } => request.tag(1).nat(answer),
        Change::Unanswered => request.tag(2),
    };
    let reply = call(Entry::Submission, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let out = match reply.tag_of(3, "an outcome")? {
        0 => Out::Stays,
        1 => Out::Moves(get_sub(&mut reply)?),
        _ => Out::Refused(match reply.tag_of(2, "a refusal")? {
            0 => Why::NotQueued,
            _ => Why::NotPlacedInput,
        }),
    };
    reply.end()?;
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::{step, Change, Out, Sub, Why};

    #[test]
    fn the_codec_carries_each_outcome_through_the_core() {
        assert_eq!(
            step(Sub::InputPlaced { entry: 7 }, Change::Answer { answer: 9 }).unwrap(),
            Out::Moves(Sub::InputAnswered {
                entry: 7,
                answer: 9
            })
        );
        assert_eq!(
            step(Sub::InputQueued, Change::Answer { answer: 9 }).unwrap(),
            Out::Refused(Why::NotPlacedInput)
        );
        assert_eq!(
            step(Sub::WriteUnanswered, Change::Unanswered).unwrap(),
            Out::Stays
        );
    }
}
