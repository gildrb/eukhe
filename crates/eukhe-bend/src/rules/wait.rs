//! A wait with every exit (docs/harness.md H6): the model
//! `bend/wait.bend`, stepper entry `bend/ffi_wait_race.bend`.
//!
//! The wait lives in the compiled core. Its race opens it with its
//! deadline, sends what it finds ready at each poll, and ends on the end
//! the stepper answers: the event, then the cancel, then the deadline
//! (`wait_poll_refines` in `laws/wait.bend`), never a second one
//! (`wait_entry_once`), whatever order the polls come in
//! (`wait_step_is_model`).

use crate::wire::{Reader, WireError, Writer};
use crate::{expect_core, Entry, Stepper};

/// What a race found ready at one poll.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Ready {
    /// The awaited event is done.
    pub work: bool,
    /// The cancel signal fired.
    pub cancel: bool,
    /// The deadline passed.
    pub deadline: bool,
}

/// What ends a race.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum End {
    /// The awaited event.
    Work,
    /// The cancel signal.
    Cancel,
    /// The deadline.
    Deadline,
}

/// The deadline a wait opens with.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Deadline {
    /// The wait has none.
    Never,
    /// One instant: the wait's one tick is its timer firing.
    Set,
}

/// One wait, kept in the compiled core.
#[derive(Debug)]
pub struct Wait {
    stepper: Stepper,
}

impl Wait {
    /// A wait with `deadline`, and the end its open answers.
    #[must_use]
    pub fn open(deadline: Deadline) -> (Self, Option<End>) {
        let mut request = Writer::new();
        match deadline {
            Deadline::Never => request.none(),
            Deadline::Set => request.some().nat(1),
        };
        let request = expect_core(Entry::WaitRace, request.finish());
        let (stepper, reply) =
            expect_core(Entry::WaitRace, Stepper::open(Entry::WaitRace, &request));
        (
            Wait { stepper },
            expect_core(Entry::WaitRace, read_end(&reply)),
        )
    }

    /// The end the poll that found `ready` brings; `None`: none yet.
    pub fn poll(&mut self, ready: Ready) -> Option<End> {
        let request = expect_core(
            Entry::WaitRace,
            Writer::new()
                .bool(ready.work)
                .bool(ready.cancel)
                .bool(ready.deadline)
                .finish(),
        );
        let reply = expect_core(Entry::WaitRace, self.stepper.step(&request));
        expect_core(Entry::WaitRace, read_end(&reply))
    }
}

/// The ends of a reply: none, or one.
fn read_end(reply: &str) -> Result<Option<End>, WireError> {
    let mut r = Reader::reply(reply)?;
    let end = if r.maybe()? {
        Some(match r.tag_of(3, "a race's end")? {
            0 => End::Work,
            1 => End::Deadline,
            // `tag_of` answers a tag below 3: this is 2.
            _ => End::Cancel,
        })
    } else {
        None
    };
    r.end()?;
    Ok(end)
}

#[cfg(test)]
mod tests {
    use super::{Deadline, End, Ready, Wait};

    /// The compiled core is reached: the open, an empty poll, then the
    /// event and the cancel ready at once (the rule itself is pinned by
    /// `laws/wait.bend`).
    #[test]
    fn the_wait_runs_in_the_core() {
        let (mut wait, opened) = Wait::open(Deadline::Set);
        let polls = [
            wait.poll(Ready::default()),
            wait.poll(Ready {
                work: true,
                cancel: true,
                deadline: false,
            }),
            wait.poll(Ready {
                deadline: true,
                ..Ready::default()
            }),
        ];
        assert_eq!((opened, polls), (None, [None, Some(End::Work), None]));
    }
}
