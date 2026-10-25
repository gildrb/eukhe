//! The chat's root-turn lease (docs/harness.md H6.2): the model
//! `bend/lease.bend`, stepper entry `bend/ffi_lease.bend`.
//!
//! The lease lives in the compiled core: the holder, then the waiters in
//! the order they asked, each named by the key its ask got. The caller
//! sends each event and acts on the [`Answer`]: it grants the lease to the
//! key the answer grants and forgets the keys it ended. It sends no stop:
//! a grant that cannot be delivered (the waiter stopped waiting) is
//! released at once (`lease_undelivered_is_stopped` in `laws/lease.bend`).

use crate::wire::{Reader, WireError, Writer};
use crate::{expect_core, Entry, Stepper};

/// What the owner of the lease does after an event.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Answer {
    /// The key the lease goes to now, if the event handed it on.
    pub grant: Option<u64>,
    /// The keys the event ended, held or still waited for.
    pub ended: Vec<u64>,
}

/// One lease, kept in the compiled core.
#[derive(Debug)]
pub struct Lease {
    stepper: Stepper,
}

impl Default for Lease {
    fn default() -> Self {
        Self::new()
    }
}

impl Lease {
    /// A free lease with no waiter.
    #[must_use]
    pub fn new() -> Self {
        let (stepper, reply) = expect_core(Entry::Lease, Stepper::open(Entry::Lease, ""));
        expect_core(Entry::Lease, Reader::reply(&reply).and_then(Reader::end));
        Lease { stepper }
    }

    /// `origin` asks for the lease: the key its ask got, and the answer.
    /// An origin is a number the caller gives each asker that can crash,
    /// within the wire's bound (99 999 999 999 999).
    pub fn ask(&mut self, origin: u64) -> (u64, Answer) {
        let reply = self.step(0, origin);
        expect_core(Entry::Lease, read_ask(&reply))
    }

    /// The lease `key` ends, held or still waited for.
    pub fn release(&mut self, key: u64) -> Answer {
        let reply = self.step(1, key);
        expect_core(Entry::Lease, read_answer(&reply))
    }

    /// Every lease of `origin` ends, held or still waited for.
    pub fn crash(&mut self, origin: u64) -> Answer {
        let reply = self.step(2, origin);
        expect_core(Entry::Lease, read_answer(&reply))
    }

    fn step(&mut self, tag: u32, n: u64) -> String {
        let event = expect_core(Entry::Lease, Writer::new().tag(tag).nat(n).finish());
        expect_core(Entry::Lease, self.stepper.step(&event))
    }
}

fn answer(r: &mut Reader<'_>) -> Result<Answer, WireError> {
    let grant = if r.maybe()? { Some(r.nat()?) } else { None };
    let count = r.count()?;
    let mut ended = Vec::with_capacity(count);
    for _ in 0..count {
        ended.push(r.nat()?);
    }
    Ok(Answer { grant, ended })
}

fn read_ask(reply: &str) -> Result<(u64, Answer), WireError> {
    let mut r = Reader::reply(reply)?;
    let key = r.nat()?;
    let answer = answer(&mut r)?;
    r.end()?;
    Ok((key, answer))
}

fn read_answer(reply: &str) -> Result<Answer, WireError> {
    let mut r = Reader::reply(reply)?;
    let answer = answer(&mut r)?;
    r.end()?;
    Ok(answer)
}

#[cfg(test)]
mod tests {
    use super::{Answer, Lease};

    fn answer(grant: Option<u64>, ended: &[u64]) -> Answer {
        Answer {
            grant,
            ended: ended.to_vec(),
        }
    }

    /// The compiled core is reached: asks queue in order, a release hands
    /// the lease on, a crash ends every lease of its origin (the rule
    /// itself is pinned by `laws/lease.bend`).
    #[test]
    fn the_lease_runs_in_the_core() {
        let mut lease = Lease::new();
        let asks = [lease.ask(0), lease.ask(2), lease.ask(2)];
        let ends = [lease.release(0), lease.crash(2)];
        assert_eq!(
            (asks, ends),
            (
                [
                    (0, answer(Some(0), &[])),
                    (1, answer(None, &[])),
                    (2, answer(None, &[])),
                ],
                [answer(Some(1), &[0]), answer(None, &[1, 2])],
            )
        );
    }
}
