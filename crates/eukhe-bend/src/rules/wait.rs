//! The end of a race at one poll (docs/harness.md H6): the model
//! `bend/wait.bend` `poll`, entry `bend/ffi_wait.bend`.
//!
//! A race polls its event, its cancel and its deadline together; more
//! than one can be ready at a poll. The core decides which ends the race:
//! the event, then the cancel, then the deadline (`wait_poll_refines` in
//! `laws/wait.bend`).

use crate::wire::{Reader, WireError, Writer};
use crate::{call, expect_core, Entry};

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

/// What ends the race that found `ready` at a poll; `None`: nothing yet.
#[must_use]
pub fn end(ready: Ready) -> Option<End> {
    let request = expect_core(
        Entry::Wait,
        Writer::new()
            .bool(ready.work)
            .bool(ready.cancel)
            .bool(ready.deadline)
            .finish(),
    );
    let reply = expect_core(Entry::Wait, call(Entry::Wait, &request));
    expect_core(Entry::Wait, read_end(&reply))
}

fn read_end(reply: &str) -> Result<Option<End>, WireError> {
    let mut r = Reader::reply(reply)?;
    let end = match r.tag_of(4, "a race's end")? {
        0 => None,
        1 => Some(End::Work),
        2 => Some(End::Cancel),
        // `tag_of` answers a tag below 4: this is 3.
        _ => Some(End::Deadline),
    };
    r.end()?;
    Ok(end)
}

#[cfg(test)]
mod tests {
    use super::{end, End, Ready};

    /// The compiled core is reached (the order is pinned by
    /// `laws/wait.bend`).
    #[test]
    fn the_race_end_runs_in_the_core() {
        let all = Ready {
            work: true,
            cancel: true,
            deadline: true,
        };
        assert_eq!(
            [
                end(all),
                end(Ready { work: false, ..all }),
                end(Ready {
                    deadline: true,
                    ..Ready::default()
                }),
                end(Ready::default()),
            ],
            [
                Some(End::Work),
                Some(End::Cancel),
                Some(End::Deadline),
                None
            ]
        );
    }
}
