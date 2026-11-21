//! What follows a run the supervisor ended (`bend/restart_turn.bend`,
//! entry `bend/ffi_restart_turn.bend`; `laws/restart_turn.bend`): the
//! worker that reopens the session continues the interrupted turn by
//! itself, at most three times a turn, then ends the run with its report;
//! the supervisor relaunches a worker its restart budget gave up unless
//! the session's last relaunch never opened it or ended its turn.

use crate::wire::{Reader, WireError, Writer};
use crate::{call, expect_core, Entry, Error};

/// What the supervisor knows of a session's last relaunch.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Prior {
    /// No relaunch of it is unsettled, and none ended its turn at the cap.
    Clear,
    /// Its last relaunch never opened the session.
    Unsettled,
    /// Its last reopen ended the turn at the cap.
    Ended,
}

/// What follows a reopen of a session whose run the supervisor ended.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Reopened {
    /// Submit the continuation: the `n`-th automatic continue of the turn.
    Continue { n: u64 },
    /// End the run with its report: `n` automatic continues were made.
    End { n: u64 },
}

/// What follows a give-up of a crash-looping worker.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GaveUp {
    /// Relaunch the worker: its reopen decides the turn.
    Relaunch,
    /// Give the worker up.
    Retire,
}

/// The reopen of a session with `made` automatic continues made this turn.
#[must_use]
pub fn reopened(made: u64) -> Reopened {
    expect_core(Entry::RestartTurn, reopened_call(made))
}

/// The give-up of a session's worker after a `prior` last relaunch.
#[must_use]
pub fn gave_up(prior: Prior) -> GaveUp {
    expect_core(Entry::RestartTurn, gave_up_call(prior))
}

fn reopened_call(made: u64) -> Result<Reopened, Error> {
    let mut request = Writer::new();
    request.nat(0).nat(made);
    let reply = call(Entry::RestartTurn, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    // A reopen answers Continue (0) or End (1).
    let next = if reader.tag_of(2, "what follows a reopen")? == 0 {
        Reopened::Continue { n: reader.nat()? }
    } else {
        Reopened::End { n: reader.nat()? }
    };
    reader.end()?;
    Ok(next)
}

fn gave_up_call(prior: Prior) -> Result<GaveUp, Error> {
    let tag = match prior {
        Prior::Clear => 1,
        Prior::Unsettled => 2,
        Prior::Ended => 3,
    };
    let mut request = Writer::new();
    request.nat(tag);
    let reply = call(Entry::RestartTurn, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    // A give-up answers Relaunch (2) or Retire (3).
    let next = match reader.tag_of(4, "what follows a give-up")? {
        2 => GaveUp::Relaunch,
        3 => GaveUp::Retire,
        _continue_or_end => {
            return Err(WireError::Malformed {
                at: 0,
                expected: "a give-up answer",
            }
            .into())
        }
    };
    reader.end()?;
    Ok(next)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The table comes from the compiled core: three continues a turn,
    /// then the end; a give-up relaunches only after a clear relaunch.
    #[test]
    fn the_core_continues_three_times_then_ends() {
        assert_eq!(
            (0..5).map(reopened).collect::<Vec<_>>(),
            [
                Reopened::Continue { n: 1 },
                Reopened::Continue { n: 2 },
                Reopened::Continue { n: 3 },
                Reopened::End { n: 3 },
                Reopened::End { n: 4 },
            ]
        );
        assert_eq!(
            [Prior::Clear, Prior::Unsettled, Prior::Ended].map(gave_up),
            [GaveUp::Relaunch, GaveUp::Retire, GaveUp::Retire]
        );
    }
}
