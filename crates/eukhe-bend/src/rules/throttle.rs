//! The throttle of one streamed request's partials (`bend/throttle.bend`,
//! stepper `bend/ffi_throttle.bend`; `laws/throttle.bend`): its flags (a
//! partial pending, the timer running, a commit in flight, the request
//! stopped) stay in the Bend heap. The caller steps each event, does the
//! actions the core answers in order, and keeps the timer and the commit;
//! the [`Gate`] keeps the pending partial's value, which the core only
//! knows is there.

use std::array;
use std::iter::Flatten;

use crate::wire::{Reader, WireError, Writer};
use crate::{expect_core, Entry, Error, Stepper};

/// Whether a streamed partial shows anything.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Content {
    /// It has content.
    Shown,
    /// It has none (such as the stream's opening event).
    Empty,
}

/// What the caller does.
#[derive(Debug, PartialEq, Eq)]
pub enum Act<T> {
    /// Start the timer; when it fires, [`Gate::fired`].
    Arm,
    /// Start a commit of this partial; when it settles, [`Gate::settled`].
    Commit(T),
    /// Abort the running timer.
    Abort,
    /// Await the commit in flight.
    Await,
}

/// The actions of one event, in order (at most two).
#[derive(Debug, PartialEq, Eq)]
pub struct Acts<T>([Option<Act<T>>; 2]);

impl<T> IntoIterator for Acts<T> {
    type Item = Act<T>;
    type IntoIter = Flatten<array::IntoIter<Option<Act<T>>, 2>>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter().flatten()
    }
}

/// The throttle of one request: open it, then step each event.
#[derive(Debug)]
pub struct Gate<T> {
    core: Stepper,
    /// The partial the core holds pending.
    pending: Option<T>,
}

impl<T> Gate<T> {
    /// A throttle that saw nothing.
    #[must_use]
    pub fn open() -> Gate<T> {
        let opened = (|| -> Result<Gate<T>, Error> {
            let (core, reply) = Stepper::open(Entry::Throttle, "")?;
            Reader::reply(&reply)?.end()?;
            Ok(Gate {
                core,
                pending: None,
            })
        })();
        expect_core(Entry::Throttle, opened)
    }

    /// A partial arrived.
    pub fn partial(&mut self, partial: T, content: Content) -> Acts<T> {
        let mut event = Writer::new();
        event.tag(0).bool(match content {
            Content::Shown => true,
            Content::Empty => false,
        });
        let acts = self.step(&mut event, Some(partial));
        expect_core(Entry::Throttle, acts)
    }

    /// The timer fired.
    pub fn fired(&mut self) -> Acts<T> {
        self.event(1)
    }

    /// The commit in flight settled.
    pub fn settled(&mut self) -> Acts<T> {
        self.event(2)
    }

    /// The request ended: stop.
    pub fn stop(&mut self) -> Acts<T> {
        self.event(3)
    }

    /// The request was dropped early: stop.
    pub fn dropped(&mut self) -> Acts<T> {
        self.event(4)
    }

    fn event(&mut self, tag: u32) -> Acts<T> {
        let mut event = Writer::new();
        event.tag(tag);
        let acts = self.step(&mut event, None);
        expect_core(Entry::Throttle, acts)
    }

    fn step(&mut self, event: &mut Writer, mut partial: Option<T>) -> Result<Acts<T>, Error> {
        let reply = self.core.step(&event.finish()?)?;
        let mut reader = Reader::reply(&reply)?;
        let mut acts = [None, None];
        let mut taken = 0;
        for _ in 0..reader.count()? {
            let act = match reader.tag_of(5, "an action")? {
                0 => {
                    self.pending = Some(partial.take().ok_or(WireError::Malformed {
                        at: 0,
                        expected: "a partial to keep",
                    })?);
                    continue;
                }
                1 => Act::Arm,
                2 => Act::Commit(self.pending.take().ok_or(WireError::Malformed {
                    at: 0,
                    expected: "a pending partial to commit",
                })?),
                3 => Act::Abort,
                4.. => Act::Await,
            };
            let slot = acts.get_mut(taken).ok_or(WireError::Malformed {
                at: 0,
                expected: "at most two actions",
            })?;
            *slot = Some(act);
            taken += 1;
        }
        reader.end()?;
        Ok(Acts(acts))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Each event goes to the compiled core: a partial arms the timer, an
    /// empty one changes nothing, the timer commits the partial, a partial
    /// during the commit waits for it, the commit settling re-arms the
    /// timer, the stop awaits the commit in flight and nothing starts after.
    #[test]
    fn the_throttle_runs_in_the_compiled_core() {
        let mut gate = Gate::open();
        let steps = [
            gate.partial(1, Content::Shown),
            gate.partial(2, Content::Empty),
            gate.fired(),
            gate.partial(3, Content::Shown),
            gate.settled(),
            gate.fired(),
            gate.stop(),
            gate.settled(),
            gate.partial(4, Content::Shown),
            gate.dropped(),
        ];
        let acts: Vec<Vec<Act<u32>>> = steps.into_iter().map(|a| a.into_iter().collect()).collect();
        assert_eq!(
            acts,
            [
                vec![Act::Arm],
                vec![],
                vec![Act::Commit(1)],
                vec![],
                vec![Act::Arm],
                vec![Act::Commit(3)],
                vec![Act::Await],
                vec![],
                vec![],
                vec![],
            ]
        );
    }
}
